theory Parser_Impl_Macros
  imports Parser_Impl_Matching
begin

section\<open> Legacy macro lowering \<close>

ML\<open>
signature URUST_MACROS =
sig
  val lower_macro:
    (URust_Resolution.environment -> URust_AST.ur_expr -> term) ->
      Proof.context ->
      URust_Resolution.environment ->
      string * Position.T * Position.T * URust_AST.macro_payload * Position.T ->
      term
end
\<close>

text\<open>
The macro layer owns invocation-span policy, registered-name precedence, builtin dispatch, retained
arguments, and raw message conversion. Fixed primitive term construction remains in
\<open>URust_Shallow_Terms\<close>, while \<open>matches!\<close> delegates case lowering to
\<open>URust_Matching\<close>.
\<close>

ML\<open>
(*
  URust_Macros is the complete legacy bang-macro policy boundary. It owns adjacency and full-name span
  handling, registered-function precedence, builtin markup, arity checks, retained-argument policy,
  raw-message conversion, macro-specific pattern rejection, and `matches!` delegation. Primitive
  unchecked term construction remains in URust_Shallow_Terms, identifier mechanics remain in
  URust_Resolution, boolean case orchestration remains in URust_Matching, and recursive traversal and
  final type checking remain outside this structure.

  lower_macro is the sole public operation. Its lowering callback must lower one URust_AST.ur_expr in
  the supplied abstract environment and return an unchecked shallow HOL term; callers must close that
  callback over the same Proof.context passed to lower_macro. The payload tuple is the source macro
  name, separate name and bang positions, parsed payload, and complete invocation position. The result
  may contain dummy types and must reach the command layer's single Syntax.check_term through
  URust_Translate.mk_closed.

  For MP_Arguments, an exact registered NFunction name including `!` is considered only when the name
  and bang positions are adjacent. A registered name wins over every builtin and lowers every argument
  in source order through the callback. Otherwise builtin markup is reported at the name before
  dispatch and arity validation. Assertion and debug-assert families lower only their first one or two
  operands; discarded arguments are never resolved, lowered, checked, or evaluated. vec! lowers every
  element through the shared array builder. addr_of! and addr_of_mut! require exactly one argument and
  share the legacy address term. Unknown names and arity failures preserve their existing text and
  invocation/name spans.

  Message macros retain only the first argument. No argument produces the empty String.implode value;
  an identifier uses the resolution layer's unlifted lexical-before-NLiteral lookup, a quoted string
  uses the shared string decoder, and a value antiquotation is parsed in the current lexical
  environment before String.implode. Every other retained message form raises the existing positioned
  raw-message diagnostic. panic! and unreachable! share Panic, fatal! retains Fatal, and
  unimplemented! and todo! share Unimplemented.

  MP_Matches reports builtin markup first, rejects legacy range patterns recursively before lowering
  the scrutinee, then delegates to URust_Matching.lower_boolean_match. That preserves one scrutinee
  evaluation, the requested-pattern true branch, and explicit false fallback while leaving ordinary
  matching policy independent of the legacy macro restriction.

  Adjacency tests, span construction, arity helpers, raw-message inspection, range traversal, builtin
  tables expressed by dispatch clauses, module aliases, and retained-list selection are private
  implementation details. URUST_MACROS exposes no macro registry, helper representation, or secondary
  lowering entry point.
*)
structure URust_Macros :> URUST_MACROS =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure R = URust_Resolution
  structure M = URust_Matching

  fun positions_are_adjacent left right =
    (case (Position.end_offset_of left, Position.offset_of right) of
       (SOME left_end, SOME right_start) => left_end = right_start
     | _ => false)

  fun macro_name_position name_pos bang_pos =
    Position.range_position
      (name_pos, Position.symbol_explode "!" bang_pos)

  fun require_macro_arity name expected actual pos =
    if expected = actual then ()
    else
      error
        ("urust_expr: macro " ^ quote (name ^ "!") ^ " expects exactly " ^
          string_of_int expected ^ " argument(s), but got " ^
          string_of_int actual ^ Position.here pos)

  fun require_macro_minimum_arity name expected actual pos =
    if expected <= actual then ()
    else
      error
        ("urust_expr: macro " ^ quote (name ^ "!") ^ " expects at least " ^
          string_of_int expected ^ " argument(s), but got " ^
          string_of_int actual ^ Position.here pos)

  fun reject_legacy_matches_ranges pattern =
    let
      fun reject source_pattern =
        (case source_pattern of
           P_Range (_, _, _, pos) =>
             error
               ("urust_expr: range patterns are not supported by legacy matches!" ^
                 Position.here pos)
         | P_Constr (_, _, arguments) => List.app reject arguments
         | P_Tuple (arguments, _) => List.app reject arguments
         | P_Group inner => reject inner
         | P_Borrow (_, inner, _) => reject inner
         | P_Alias (_, _, inner, _) => reject inner
         | P_Slice (items, _) =>
             List.app
               (fn SI_Pat inner => reject inner
                 | SI_Rest _ => ())
               items
         | P_Struct (_, _, fields) =>
             List.app
               (fn SF_Field (_, _, inner) => reject inner
                 | SF_Shorthand _ => ()
                 | SF_Rest _ => ())
               fields
         | P_Or (alternatives, _) => List.app reject alternatives
         | _ => ())
    in reject pattern end

  fun raw_message ctxt environment expression =
    (case expression of
       UE_Ident identifier =>
         R.literal_identifier_value ctxt environment identifier
     | UE_Literal (LP_String (raw, pos)) =>
         T.string_value raw pos
     | UE_Literal (LP_ValAntiq source) =>
         T.string_from_characters
           (R.parse_antiquotation ctxt environment source)
     | _ =>
         error
           ("urust_expr: macro message must be an identifier, quoted string, or value antiquotation" ^
             Position.here (expression_position expression)))

  fun report_builtin ctxt pos =
    Context_Position.report ctxt pos Markup.keyword1

  fun lower_macro lower ctxt environment
      (name, name_pos, bang_pos, payload, position) =
    let
      val complete_name = name ^ "!"
      val complete_name_pos = macro_name_position name_pos bang_pos

      fun lower_argument expression = lower environment expression

      fun lower_message target arguments =
        let
          val message =
            (case arguments of
               [] => T.string_from_characters T.list_nil
             | first :: _ => raw_message ctxt environment first)
        in target message end

      fun lower_builtin arguments =
        let
          val actual = length arguments
          val _ = report_builtin ctxt name_pos
        in
          (case name of
             "assert" =>
               (require_macro_minimum_arity name 1 actual position;
                T.assertion (lower_argument (hd arguments)))
           | "debug_assert" =>
               (require_macro_minimum_arity name 1 actual position;
                T.assertion (lower_argument (hd arguments)))
           | "assert_eq" =>
               (require_macro_minimum_arity name 2 actual position;
                T.assertion_equal
                  (lower_argument (hd arguments))
                  (lower_argument (nth arguments 1)))
           | "debug_assert_eq" =>
               (require_macro_minimum_arity name 2 actual position;
                T.assertion_equal
                  (lower_argument (hd arguments))
                  (lower_argument (nth arguments 1)))
           | "assert_ne" =>
               (require_macro_minimum_arity name 2 actual position;
                T.assertion_not_equal
                  (lower_argument (hd arguments))
                  (lower_argument (nth arguments 1)))
           | "debug_assert_ne" =>
               (require_macro_minimum_arity name 2 actual position;
                T.assertion_not_equal
                  (lower_argument (hd arguments))
                  (lower_argument (nth arguments 1)))
           | "panic" => lower_message T.panic_message arguments
           | "unreachable" => lower_message T.panic_message arguments
           | "fatal" => lower_message T.fatal_message arguments
           | "unimplemented" =>
               lower_message T.unimplemented_message arguments
           | "todo" =>
               lower_message T.unimplemented_message arguments
           | "vec" =>
               T.array_literal (map lower_argument arguments)
           | "addr_of" =>
               (require_macro_arity name 1 actual position;
                T.address_of (lower_argument (hd arguments)))
           | "addr_of_mut" =>
               (require_macro_arity name 1 actual position;
                T.address_of (lower_argument (hd arguments)))
           | _ =>
               error
                 ("urust_expr: unknown macro " ^ quote complete_name ^
                   Position.here complete_name_pos))
        end
    in
      (case payload of
         MP_Matches (scrutinee, pattern) =>
           (report_builtin ctxt name_pos;
            reject_legacy_matches_ranges pattern;
            M.lower_boolean_match lower ctxt environment
              (scrutinee, pattern, position))
       | MP_Arguments arguments =>
           (case
               if positions_are_adjacent name_pos bang_pos
               then R.registered_function ctxt (complete_name, complete_name_pos)
               else NONE
            of
              SOME function =>
                T.function_call position function
                  (map lower_argument arguments)
            | NONE => lower_builtin arguments))
    end
end
\<close>

end
