theory Parser_Impl_Command
  imports
    Parser_Impl_Diagnostics
    Parser_Impl_Translate
  keywords
    "urust_expr" :: thy_decl
    and "urust_fun" :: thy_decl
    and "urust_notation" :: thy_decl
    and "against"
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr [OPTIONS] NAME src\<close> parses, elaborates, checks once, and defines \<open>NAME\<close>.
The optional comma-separated inline options override the corresponding scoped configurations.
\<open>urust_conformance_check\<close> defaults to false. When enabled, the command also checks the generated
definition against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend by definition unfolding and
\<open>refl\<close>, and records \<open>NAME_conformance\<close>.

An optional trailing \<open>against old_term\<close> supplies a distinct existing-frontend term and implies
conformance checking even when the configuration is false. Combining it with an explicit
\<open>[urust_conformance_check = false]\<close> is rejected.

The standard Isabelle definition mechanism supplies one default code equation, but the command adds
no custom attributes and keeps generated definitions out of the global simp set. Successful
interactive commands print the generated \<open>NAME_def\<close> definition and, when checking is enabled,
the \<open>NAME_conformance\<close> theorem through Isabelle's standard result display. The scoped
\<open>urust_verbose\<close> configuration defaults to false: compact output contains only the result names,
while true also prints the complete definition and theorem statements. Compact output is always
shown for interactive commands; \<open>show_results\<close> additionally enables it during noninteractive
processing.

\<open>urust_fun [OPTIONS] NAME :: TYPE (parameters) src\<close> uses Isabelle's type
syntax for a curried function signature ending in \<open>function_body\<close>. It elaborates the body with
typed lexical parameters, wraps it once in \<open>FunctionBody\<close>, checks the complete constrained
function term, and defines it through the same standard mechanism. Its configuration and trailing
\<open>against old_term\<close> forms select the corresponding same-source or explicit-term
complete-function conformance checks under temporary typed parameter fixes.

Both commands accept the same extensible boolean-option list. Current options are
\<open>urust_conformance_check\<close> and \<open>urust_verbose\<close>; either may appear alone or together in
either order.
\<close>
ML\<open>
signature URUST_COMMAND =
sig
  val elab_urust: local_theory -> Input.source -> term
  val elab_urust_fun:
    local_theory ->
      {raw_type: string * Position.T,
       parameters: (string * Position.T) list,
       parameters_pos: Position.T,
       body: Input.source} ->
      term
end

(* THE expression pipeline, exported: every expression definition command runs source through
   elab_urust, so `urust_expr` and the negative harness can never drift on what they exercise.
   elab_urust_fun is the corresponding shared typed-function pipeline for `urust_fun` and focused
   rejection tests. Both raise (positioned) on lexer, yacc, elaboration, or final term-check failures.
   URust_Diagnostics.parse_source owns serialization of the generated runtime; elaboration and
   check_term remain outside that lock.

   URUST_COMMAND exposes expression and focused function elaboration for test harnesses and
   programmatic clients.
   Definition helpers, conformance-proof assembly, outer-command parsers, and command
   registration are private implementation details. *)
structure URust_Command :> URUST_COMMAND =
struct
val urust_conformance_check =
  Attrib.setup_config_bool \<^binding>\<open>urust_conformance_check\<close> (K false)

val urust_verbose =
  Attrib.setup_config_bool \<^binding>\<open>urust_verbose\<close> (K false)

val conformance_flag = "urust_conformance_check"
val verbose_flag = "urust_verbose"

val flag_configs =
  Symtab.make
    [(conformance_flag, urust_conformance_check),
     (verbose_flag, urust_verbose)]

type command_options = (bool * Position.T) Symtab.table

fun add_inline_flag ((name, pos), enabled) options =
  (case Symtab.lookup flag_configs name of
     NONE =>
       error
         ("unknown uRust command option " ^ quote name ^
           Position.here pos)
   | SOME _ =>
       if Symtab.defined options name
       then
         error
           ("duplicate uRust command option " ^ quote name ^
             Position.here pos)
       else Symtab.update (name, (enabled, pos)) options)

fun configured_flag lthy options name =
  (case Symtab.lookup options name of
     SOME (enabled, _) => enabled
   | NONE =>
       (case Symtab.lookup flag_configs name of
          SOME config => Config.get lthy config
        | NONE => error ("internal unknown uRust command option " ^ quote name)))

fun elab_urust lthy source : term =
  (case
      URust_Diagnostics.parse_source lthy source of
     SOME ast => Syntax.check_term lthy (URust_Translate.mk_closed lthy ast)
   | NONE => error ("urust_expr: empty expression" ^ Position.here (Input.pos_of source)))

fun elab_urust_fun lthy
    {raw_type = (raw_type, type_pos), parameters, parameters_pos, body} : term =
  let
    val declared_type = Syntax.read_typ lthy raw_type
    val (parameter_types, result_type) = Term.strip_type declared_type
    val _ =
      (case result_type of
         Type (name, _) =>
           if name = \<^type_name>\<open>function_body\<close> then ()
           else
             error
               ("urust_fun: declared result type must be function_body" ^
                 Position.here type_pos)
       | _ =>
           error
             ("urust_fun: declared result type must be function_body" ^
               Position.here type_pos))
    val expected = length parameter_types
    val actual = length parameters
    val count_pos =
      if actual > expected
      then #2 (nth parameters expected)
      else parameters_pos
    val _ =
      if expected = actual then ()
      else
        error
          ("urust_fun: declared type expects " ^ string_of_int expected ^
            " parameter" ^ (if expected = 1 then "" else "s") ^
            ", but " ^ string_of_int actual ^
            (if actual = 1 then " name was" else " names were") ^
            " supplied" ^ Position.here count_pos)
    val parameters_with_types =
      map2 (fn parameter => fn T => (parameter, T))
        parameters parameter_types
    val ast =
      (case URust_Diagnostics.parse_source lthy body of
         SOME expression => expression
       | NONE =>
           error
             ("urust_fun: empty function body" ^
               Position.here (Input.pos_of body)))
    val unchecked =
      URust_Translate.mk_function lthy parameters_with_types ast
    val checked =
      Syntax.check_term lthy (Type.constraint declared_type unchecked)
    val unresolved =
      Term.add_frees checked []
      |> filter_out (Variable.is_fixed lthy o #1)
      |> sort_by #1
    val _ =
      (case unresolved of
         (name, _) :: _ =>
           error
             ("urust_fun: unresolved body name " ^ quote name ^
               Position.here (Input.pos_of body))
       | [] => ())
  in
    checked
  end

fun define_urust_result (binding, source) lthy =
  let
    val term = elab_urust lthy source
    val name = Binding.name_of binding
  in
    Specification.definition
      (SOME (binding, NONE, NoSyn)) [] []
      ((Thm.def_binding binding, []),
        Logic.mk_equals
          (Free (name, fastype_of term), term)) lthy
  end

fun define_urust_fun_result
    (binding, raw_type, parameters_pos, parameters, body) lthy =
  let
    val term =
      elab_urust_fun lthy
        {raw_type = raw_type,
         parameters = parameters,
         parameters_pos = parameters_pos,
         body = body}
    val name = Binding.name_of binding
  in
    Specification.definition
      (SOME (binding, NONE, NoSyn)) [] []
      ((Thm.def_binding binding, []),
        Logic.mk_equals
          (Free (name, fastype_of term), term)) lthy
  end

fun old_frontend_source source = "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"

fun print_compact_result interactive kind lthy name =
  if interactive orelse Config.get lthy Proof_Display.show_results
  then
    Pretty.writeln_urgent
      (Pretty.chunks
        [Pretty.block
           [Pretty.mark_position (Position.thread_data ()) (Pretty.keyword1 kind),
            Pretty.brk 1,
            Pretty.str (Long_Name.base_name name),
            Pretty.str ":"],
         Pretty.str "  ..."])
  else ()

fun print_generated_result interactive verbose kind lthy (name, thms) =
  if verbose
  then
    Proof_Display.print_results
      {interactive = interactive, pos = Position.thread_data ()}
      lthy ((kind, name), [("", thms)])
  else print_compact_result interactive kind lthy name

fun print_definition interactive verbose lthy (_, (name, thm)) =
  print_generated_result interactive verbose "definition" lthy (name, [thm])

fun note_conformance binding lhs def_thm old_frontend lthy =
  let
    val equality =
      Syntax.check_term lthy
        (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ old_frontend)
    val conformance =
      Goal.prove lthy [] [] (HOLogic.mk_Trueprop equality)
        (fn {context = ctxt, ...} =>
          Local_Defs.unfold_tac ctxt [def_thm] THEN
          resolve_tac ctxt [@{thm refl}] 1)
    val (result, lthy') =
      Local_Theory.note
        ((Binding.suffix_name "_conformance" binding, []), [conformance]) lthy
  in (result, lthy') end

fun define_urust_with_frontend_check
    (binding, new_source, old_frontend_source) interactive verbose lthy =
  let
    val (definition as (lhs, (_, def_thm)), lthy') =
      define_urust_result (binding, new_source) lthy
    val old_frontend =
      Syntax.parse_term lthy' old_frontend_source
    val (conformance, lthy'') =
      note_conformance binding lhs def_thm old_frontend lthy'
    val _ = print_definition interactive verbose lthy'' definition
    val _ =
      print_generated_result interactive verbose Thm.theoremK lthy''
        conformance
  in
    lthy''
  end

fun old_frontend_function lthy declared_type parameters old_body_source =
  let
    val (parameter_types, result_type) = Term.strip_type declared_type
    val body_type =
      (case result_type of
         Type (_, [stateT, returnT, abortT, inputT, outputT]) =>
           Type
             (\<^type_name>\<open>expression\<close>,
               [stateT, returnT, returnT, abortT, inputT, outputT])
       | _ =>
           error
             "urust_fun: internal malformed function_body result type")
    val fixes =
      map2
        (fn (name, _) => fn T => (Binding.name name, SOME T, NoSyn))
        parameters parameter_types
    val (internal_names, body_ctxt) =
      Proof_Context.add_fixes fixes (Variable.set_body true lthy)
    val formals =
      map2 (fn name => fn T => Free (name, T))
        internal_names parameter_types
    val old_body =
      Syntax.parse_term body_ctxt old_body_source
      |> Type.constraint body_type
      |> Syntax.check_term body_ctxt
    val unchecked =
      fold_rev Term.lambda formals
        (URust_Shallow_Terms.function_body old_body)
    val checked =
      Syntax.check_term body_ctxt
        (Type.constraint declared_type unchecked)
  in
    singleton (Variable.export_terms body_ctxt lthy) checked
  end

fun define_urust_fun_with_frontend_check
    (args as (binding, _, _, parameters, _), old_body_source) interactive verbose lthy =
  let
    val (definition as (lhs, (_, def_thm)), lthy') =
      define_urust_fun_result args lthy
    val old_frontend =
      old_frontend_function lthy' (fastype_of lhs) parameters old_body_source
    val (conformance, lthy'') =
      note_conformance binding lhs def_thm old_frontend lthy'
    val _ = print_definition interactive verbose lthy'' definition
    val _ =
      print_generated_result interactive verbose Thm.theoremK lthy''
        conformance
  in
    lthy''
  end

fun define_and_print define args interactive verbose lthy =
  let
    val (definition, lthy') = define args lthy
    val _ = print_definition interactive verbose lthy' definition
  in lthy' end

fun reject_contradictory_against command options against =
  (case (Symtab.lookup options conformance_flag, against) of
     (SOME (false, pos), SOME _) =>
       error
         (command ^ ": [urust_conformance_check = false] cannot be combined with `against`" ^
           Position.here pos)
   | _ => ())

fun define_urust
    (options, args as (binding, source), against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_expr" options against
    val verbose = configured_flag lthy options verbose_flag
  in
    (case against of
       SOME (old_frontend, _) =>
         define_urust_with_frontend_check
           (binding, source, old_frontend) interactive verbose lthy
     | NONE =>
         if configured_flag lthy options conformance_flag
         then
           define_urust_with_frontend_check
             (binding, source, old_frontend_source source) interactive verbose lthy
         else define_and_print define_urust_result args interactive verbose lthy)
  end

fun define_urust_fun
    (options, args as (_, _, _, _, body), against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_fun" options against
    val verbose = configured_flag lthy options verbose_flag
  in
    (case against of
       SOME (old_frontend, _) =>
         define_urust_fun_with_frontend_check
           (args, old_frontend) interactive verbose lthy
     | NONE =>
         if configured_flag lthy options conformance_flag
         then
           define_urust_fun_with_frontend_check
             (args, old_frontend_source body) interactive verbose lthy
         else define_and_print define_urust_fun_result args interactive verbose lthy)
  end

val parse_boolean =
  Parse.reserved "true" >> K true ||
  Parse.reserved "false" >> K false

val parse_inline_flag =
  (Parse.name_position --| Parse.$$$ "=") -- parse_boolean

val parse_command_options =
  Scan.optional
    (Parse.$$$ "[" |--
      Parse.!!! (Parse.enum1 "," parse_inline_flag --| Parse.$$$ "]") >>
      (fn flags => fold add_inline_flag flags Symtab.empty))
    Symtab.empty

val parse_against =
  Scan.option
    (Parse.position (Parse.$$$ "against") -- Parse.term >>
      (fn ((_, pos), term) => (term, pos)))

val parse_urust_expr =
  parse_command_options --
    (Parse.binding --
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source)) --
    parse_against >>
  (fn ((options, args), against) => (options, args, against))

val _ = Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_expr\<close>
          "Define a uRust expression, optionally checking existing-frontend conformance by refl"
          (parse_urust_expr >> define_urust)

val parse_parameter =
  Parse.position Parse.liberal_name || Parse.position Parse.underscore

val parse_parameters =
  (Parse.position (Parse.$$$ "(") >> #2) --
    Scan.optional
      (parse_parameter --
        Scan.repeat (Parse.$$$ "," |-- parse_parameter) --
        Scan.optional (Parse.$$$ "," >> K ()) () >>
        (fn ((first, rest), ()) => first :: rest))
      [] --|
    Parse.$$$ ")"

val parse_urust_fun =
  parse_command_options --
    (Parse.binding --| Parse.$$$ "::" --
      Parse.position Parse.typ --
      parse_parameters --
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source) >>
      (fn (((binding, raw_type), (parameters_pos, parameters)), body) =>
        (binding, raw_type, parameters_pos, parameters, body))) --
    parse_against >>
  (fn ((options, args), against) => (options, args, against))

val _ = Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_fun\<close>
          "Define a typed uRust function body, optionally checking existing-frontend conformance by refl"
          (parse_urust_fun >> define_urust_fun)
end
\<close>

section\<open> Canonical notation declarations \<close>

text\<open>
\<open>urust_notation\<close> is a parser-aware declaration wrapper. It validates and
canonicalizes Rust names with the same parser and path renderer used by lookup,
then delegates all registration and configuration behavior to
\<open>Micro_Rust_Notation_Cmd\<close>.
\<close>
ML\<open>
local
  fun split_bang name =
    if String.isSuffix "!" name
    then (String.substring (name, 0, size name - 1), "!")
    else (name, "")

  fun canonical_name ctxt (name, pos) =
    let
      val (path_text, bang) = split_bang name
      val source =
        Parser_Lex_Util.positioned_content_source path_text pos
      val path =
        (case URust_Diagnostics.parse_source ctxt source of
           SOME (URust_AST.UE_Path path) => path
         | SOME _ =>
             error
               ("urust_notation: expected a complete uRust path" ^
                 Position.here pos)
         | NONE =>
             error
               ("urust_notation: empty uRust name" ^
                 Position.here pos))
    in URust_AST.render_path path ^ bang end

  fun register kind_opt (hol_src, rust_name) lthy =
    Micro_Rust_Notation_Cmd.do_register kind_opt
      (hol_src, (canonical_name lthy rust_name, #2 rust_name)) lthy

  fun configure (bit, names) lthy =
    Micro_Rust_Notation_Cmd.do_config
      (bit, map (canonical_name lthy) names) lthy

  val parse_name = Parse.position Parse.string
  val parse_names = Scan.repeat parse_name
  val parse_payload =
    Parse.term --
      (Parse.$$$ "(" |-- parse_name --| Parse.$$$ ")")

  val parse_register_with_kind =
    parse_payload >> (fn payload => fn kind => register (SOME kind) payload)

  val parse_command : (local_theory -> local_theory) parser =
       (Parse.$$$ "(" |-- Args.$$$ "literal" --| Parse.$$$ ")"
          |-- parse_register_with_kind
          >> (fn f => f Micro_Rust_Names.NLiteral))
    || (Parse.$$$ "(" |-- Args.$$$ "call" --| Parse.$$$ ")"
          |-- parse_register_with_kind
          >> (fn f => f Micro_Rust_Names.NFunction))
    || (Parse.$$$ "(" |-- Args.$$$ "field" --| Parse.$$$ ")"
          |-- parse_register_with_kind
          >> (fn f => f Micro_Rust_Names.NField))
    || (Parse.$$$ "(" |-- Args.$$$ "config" --| Parse.$$$ ")"
          |-- Micro_Rust_Notation_Cmd.parse_shadow_mode -- parse_names
          >> configure)
    || (parse_payload >> register NONE)
in
  val _ =
    Outer_Syntax.local_theory \<^command_keyword>\<open>urust_notation\<close>
      "register a parser-canonical uRust notation or configure shadow checks"
      parse_command
end
\<close>

end
