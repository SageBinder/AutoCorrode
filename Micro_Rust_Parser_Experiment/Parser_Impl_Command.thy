theory Parser_Impl_Command
  imports
    Parser_Impl_Diagnostics
    Parser_Impl_Translate
  keywords
    "urust_expr" :: thy_decl
    and "urust_fun" :: thy_decl
    and "urust_fun_with_check" :: thy_decl
    and "urust_expr_with_check" :: thy_decl
    and "urust_expr_with_check'" :: thy_decl
    and "urust_notation" :: thy_decl
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr NAME src\<close> parses, elaborates, checks once, and defines \<open>NAME\<close>.
The standard Isabelle definition mechanism supplies one default code equation, but the command
adds no custom attributes and keeps generated definitions out of the global simp set.

\<open>urust_fun NAME :: TYPE (parameters) src\<close> uses Isabelle's type syntax for a curried
function signature ending in \<open>function_body\<close>. It elaborates the body with typed lexical
parameters, wraps it once in \<open>FunctionBody\<close>, checks the complete constrained function term,
and defines it through the same standard mechanism.

\<open>urust_fun_with_check NAME :: TYPE (parameters) src\<close> additionally elaborates
\<open>FunctionBody \<lbrakk>src\<rbrakk>\<close> through the existing frontend under temporary typed fixes,
abstracts those fixes in source order, and records \<open>NAME_conformance\<close> by unfolding only
\<open>NAME_def\<close> and applying \<open>refl\<close>.

\<open>urust_expr_with_check NAME src\<close> additionally checks the resulting definition
against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend by definition unfolding and
\<open>refl\<close>, and records the theorem as \<open>NAME_conformance\<close>.

\<open>urust_expr_with_check' NAME new_src old_term\<close> performs the same check with
\<open>new_src\<close> sent to the new parser and the explicit
\<open>\<lbrakk>old_src\<rbrakk>\<close> in \<open>old_term\<close> sent to the existing frontend.
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
   elab_urust, so `urust_expr`, both expression conformance commands, and the negative harness can
   never drift on what they exercise. elab_urust_fun is the corresponding shared typed-function
   pipeline for `urust_fun`, `urust_fun_with_check`, and focused rejection tests. Both raise
   (positioned) on lexer, yacc, elaboration, or final term-check failures.
   URust_Diagnostics.parse_source owns serialization of the generated runtime; elaboration and
   check_term remain outside that lock.

   URUST_COMMAND exposes expression and focused function elaboration for test harnesses and
   programmatic clients.
   Definition helpers, conformance-proof assembly, outer-command parsers, and command
   registration are private implementation details. *)
structure URust_Command :> URUST_COMMAND =
struct
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

fun define_urust args lthy = snd (define_urust_result args lthy)

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

fun define_urust_fun args lthy = snd (define_urust_fun_result args lthy)

fun old_frontend_source source = "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"

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
    val (_, lthy') =
      Local_Theory.note
        ((Binding.suffix_name "_conformance" binding, []), [conformance]) lthy
  in lthy' end

fun define_urust_with_frontend_check (binding, new_source, old_frontend_source) lthy =
  let
    val ((lhs, (_, def_thm)), lthy') =
      define_urust_result (binding, new_source) lthy
    val old_frontend =
      Syntax.parse_term lthy' old_frontend_source
  in
    note_conformance binding lhs def_thm old_frontend lthy'
  end

fun define_urust_with_check (binding, source) =
  define_urust_with_frontend_check (binding, source, old_frontend_source source)

fun old_frontend_function lthy declared_type parameters body =
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
             "urust_fun_with_check: internal malformed function_body result type")
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
      Syntax.parse_term body_ctxt (old_frontend_source body)
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

fun define_urust_fun_with_check
    (args as (binding, _, _, parameters, body)) lthy =
  let
    val ((lhs, (_, def_thm)), lthy') =
      define_urust_fun_result args lthy
    val old_frontend =
      old_frontend_function lthy' (fastype_of lhs) parameters body
  in
    note_conformance binding lhs def_thm old_frontend lthy'
  end

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr\<close>
          "Parse a uRust expression and define it as a HOL constant"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust)

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
  Parse.binding --| Parse.$$$ "::" --
  Parse.position Parse.typ --
  parse_parameters --
  (Parse.token Parse.cartouche >>
    Parser_Lex_Util.cartouche_source) >>
  (fn (((binding, raw_type), (parameters_pos, parameters)), body) =>
    (binding, raw_type, parameters_pos, parameters, body))

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_fun\<close>
          "Define a typed uRust function body"
          (parse_urust_fun >> define_urust_fun)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_fun_with_check\<close>
          "Define a typed uRust function body and check it against the existing frontend by refl"
          (parse_urust_fun >> define_urust_fun_with_check)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check\<close>
          "Define a uRust expression and check it against the existing frontend by refl"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust_with_check)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check'\<close>
          "Define a uRust expression and check it against an explicit existing-frontend term by refl"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) --
            Parse.term >>
            (fn ((binding, new_source), old_frontend_source) =>
              define_urust_with_frontend_check (binding, new_source, old_frontend_source)))
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
