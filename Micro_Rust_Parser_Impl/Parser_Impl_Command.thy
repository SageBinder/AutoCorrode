theory Parser_Impl_Command
  imports
    Parser_Impl_Diagnostics
    Parser_Impl_Translate
    Micro_Rust_Parsing_Legacy_Frontend.Micro_Rust_Parsing_Legacy_Frontend
  keywords
    "urust_expr" :: thy_decl
    and "urust_fun" :: thy_decl
    and "urust_notation" :: thy_decl
    and "with_args"
    and "against"
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr [OPTIONS] NAME src [with_args ARG...] [against TERM]\<close> parses, elaborates, and
checks once. A nonempty \<open>with_args\<close> suffix introduces dummy-typed lexical arguments in source
order and produces \<open>\<lambda>ARG.... src\<close>; it must precede \<open>against\<close>. The optional
comma-separated inline options override the corresponding scoped configurations.
\<open>urust_conformance_check\<close> defaults to false. When enabled, the command also checks the generated
declaration against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend and records
\<open>NAME_conformance\<close>. Contextual legacy bodies are parsed under temporary fixes carrying the
new declaration's inferred argument types, then abstracted in the same order.

An optional trailing \<open>against old_term\<close> supplies a distinct existing-frontend term and implies
conformance checking even when the configuration is false. Combining it with an explicit
\<open>[urust_conformance_check = false]\<close> is rejected.

The scoped \<open>urust_abbrev\<close> configuration defaults to false. False uses Isabelle's standard
definition mechanism, supplying \<open>NAME_def\<close> and one default code equation without adding the
definition to the global simp set. True uses \<open>Local_Theory.abbrev\<close>, supplying neither artifact;
checked client terms contain the expanded right-hand side. Definition conformance unfolds only
\<open>NAME_def\<close> before \<open>refl\<close>; abbreviation conformance closes directly by \<open>refl\<close>.

Successful interactive commands print either the generated definition or abbreviation and, when
checking is enabled, the \<open>NAME_conformance\<close> theorem. The scoped \<open>urust_verbose\<close> configuration
defaults to false: compact output contains only the result names, while true also prints complete
definition/theorem statements or the abbreviation's inferred equation. Compact output is always shown
for interactive commands; \<open>show_results\<close> additionally enables it during noninteractive processing.

\<open>urust_fun [OPTIONS] NAME :: TYPE (parameters) src\<close> uses Isabelle's type
syntax for a curried function signature ending in \<open>function_body\<close>. It elaborates the body with
typed lexical parameters, wraps it once in \<open>FunctionBody\<close>, checks the complete constrained
function term, and installs it through the same selected declaration mode. Its configuration and
trailing \<open>against old_term\<close> forms select the corresponding same-source or explicit-term
complete-function conformance checks under temporary typed parameter fixes.

Both commands accept the same extensible boolean-option list. Current options are
\<open>urust_conformance_check\<close>, \<open>urust_verbose\<close>, and \<open>urust_abbrev\<close>; they may appear in
any order.
\<close>
ML\<open>
signature URUST_COMMAND =
sig
  val elab_urust: local_theory -> Input.source -> term
  val elab_urust_with_args:
    local_theory ->
      (string * Position.T) list ->
      Input.source ->
      term
  val elab_urust_fun:
    local_theory ->
      {raw_type: string * Position.T,
       parameters: (string * Position.T) list,
       parameters_pos: Position.T,
       body: Input.source} ->
      term
end

(* THE expression pipeline, exported: every expression declaration command runs source through
   elab_urust_with_args; elab_urust is its closed-expression wrapper, so command and negative harness
   behavior cannot drift. elab_urust_fun is the corresponding shared typed-function pipeline for
   `urust_fun` and focused rejection tests. All raise (positioned) on lexer, yacc, elaboration, or
   final term-check failures.
   URust_Diagnostics.parse_source owns serialization of the generated runtime; elaboration and
   check_term remain outside that lock.

   URUST_COMMAND exposes closed/contextual expression and focused function elaboration for test
   harnesses and programmatic clients. Declaration installation, conformance-proof assembly,
   outer-command parsers, and command registration are private implementation details. *)
structure URust_Command :> URUST_COMMAND =
struct
val urust_conformance_check =
  Attrib.setup_config_bool \<^binding>\<open>urust_conformance_check\<close> (K false)

val urust_verbose =
  Attrib.setup_config_bool \<^binding>\<open>urust_verbose\<close> (K false)

val urust_abbrev =
  Attrib.setup_config_bool \<^binding>\<open>urust_abbrev\<close> (K false)

val conformance_flag = "urust_conformance_check"
val verbose_flag = "urust_verbose"
val abbrev_flag = "urust_abbrev"

val flag_configs =
  Symtab.make
    [(conformance_flag, urust_conformance_check),
     (verbose_flag, urust_verbose),
     (abbrev_flag, urust_abbrev)]

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

fun elab_urust_with_args lthy arguments source : term =
  (case
      URust_Diagnostics.parse_source lthy source of
     SOME ast =>
       Syntax.check_term lthy
         (URust_Translate.mk_contextual lthy arguments ast)
   | NONE => error ("urust_expr: empty expression" ^ Position.here (Input.pos_of source)))

fun elab_urust lthy source =
  elab_urust_with_args lthy [] source

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

datatype declaration_result =
    Definition_Result of
      {lhs: term, fact_name: string, theorem: thm}
  | Abbreviation_Result of
      {lhs: term, rhs: term, name: string}

fun declaration_conformance_term
      (Definition_Result {lhs, ...}) = lhs
  | declaration_conformance_term
      (Abbreviation_Result {rhs, ...}) = rhs

fun declaration_name fallback lhs =
  (case Term.head_of lhs of
     Const (name, _) => name
   | Free (name, _) => name
   | _ => fallback)

fun install_urust_result abbreviation binding term lthy =
  let
    val name = Binding.name_of binding
  in
    if abbreviation then
      let
        val ((lhs, rhs), lthy') =
          Local_Theory.abbrev Syntax.mode_default
            ((binding, NoSyn), term) lthy
        val full_name =
          declaration_name (Local_Theory.full_name lthy binding) lhs
      in
        (Abbreviation_Result
          {lhs = lhs, rhs = rhs, name = full_name}, lthy')
      end
    else
      let
        val ((lhs, (fact_name, theorem)), lthy') =
          Specification.definition
            (SOME (binding, NONE, NoSyn)) [] []
            ((Thm.def_binding binding, []),
              Logic.mk_equals
                (Free (name, fastype_of term), term)) lthy
      in
        (Definition_Result
          {lhs = lhs, fact_name = fact_name, theorem = theorem}, lthy')
      end
  end

fun declare_urust_result abbreviation
    (binding, source, arguments) lthy =
  let
    val term = elab_urust_with_args lthy arguments source
  in
    install_urust_result abbreviation binding term lthy
  end

fun declare_urust_fun_result abbreviation
    (binding, raw_type, parameters_pos, parameters, body) lthy =
  let
    val term =
      elab_urust_fun lthy
        {raw_type = raw_type,
         parameters = parameters,
         parameters_pos = parameters_pos,
         body = body}
  in
    install_urust_result abbreviation binding term lthy
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

fun print_abbreviation interactive verbose lthy name lhs rhs =
  if verbose andalso
     (interactive orelse Config.get lthy Proof_Display.show_results)
  then
    Pretty.writeln_urgent
      (Pretty.block1
        [Pretty.block
           [Pretty.mark_position (Position.thread_data ())
              (Pretty.keyword1 "abbreviation"),
            Pretty.brk 1,
            Pretty.str (Long_Name.base_name name),
            Pretty.str ":"],
         Pretty.fbrk,
         Syntax.pretty_term
           (Config.put Proof_Context.show_abbrevs false lthy)
           (Logic.mk_equals (lhs, rhs))])
  else print_compact_result interactive "abbreviation" lthy name

fun print_declaration interactive verbose lthy declaration =
  (case declaration of
     Definition_Result {fact_name, theorem, ...} =>
       print_generated_result interactive verbose "definition" lthy
         (fact_name, [theorem])
   | Abbreviation_Result {lhs, rhs, name} =>
       print_abbreviation interactive verbose lthy name lhs rhs)

fun note_conformance binding declaration old_frontend lthy =
  let
    val lhs = declaration_conformance_term declaration
    val equality =
      Syntax.check_term lthy
        (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ old_frontend)
    val conformance =
      Goal.prove lthy [] [] (HOLogic.mk_Trueprop equality)
        (fn {context = ctxt, ...} =>
          (case declaration of
             Definition_Result {theorem, ...} =>
               Local_Defs.unfold_tac ctxt [theorem] THEN
               resolve_tac ctxt [@{thm refl}] 1
           | Abbreviation_Result _ =>
               resolve_tac ctxt [@{thm refl}] 1))
    val (result, lthy') =
      Local_Theory.note
        ((Binding.suffix_name "_conformance" binding, []), [conformance]) lthy
  in (result, lthy') end

fun with_typed_fixes lthy command complete_type parameters
    body_type wrap_body old_body_source =
  let
    val (parameter_types, _) = Term.strip_type complete_type
    val _ =
      if length parameter_types = length parameters then ()
      else
        error
          (command ^ ": internal legacy parameter/type count mismatch")
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
        (wrap_body old_body)
    val checked =
      Syntax.check_term body_ctxt
        (Type.constraint complete_type unchecked)
  in
    singleton (Variable.export_terms body_ctxt lthy) checked
  end

fun old_frontend_expression lthy complete_type arguments old_body_source =
  let
    val (_, result_type) = Term.strip_type complete_type
  in
    with_typed_fixes lthy "urust_expr" complete_type arguments
      result_type I old_body_source
  end

fun old_frontend_function lthy declared_type parameters old_body_source =
  let
    val (_, result_type) = Term.strip_type declared_type
    val body_type =
      (case result_type of
         Type (_, [stateT, returnT, abortT, inputT, outputT]) =>
           Type
             (\<^type_name>\<open>expression\<close>,
               [stateT, returnT, returnT, abortT, inputT, outputT])
       | _ =>
           error
             "urust_fun: internal malformed function_body result type")
  in
    with_typed_fixes lthy "urust_fun" declared_type parameters
      body_type URust_Shallow_Terms.function_body old_body_source
  end

fun declare_with_frontend_check
    declaration binding make_old interactive verbose lthy =
  let
    val (result, lthy') = declaration lthy
    val old_frontend =
      make_old lthy' (fastype_of (declaration_conformance_term result))
    val (conformance, lthy'') =
      note_conformance binding result old_frontend lthy'
    val _ = print_declaration interactive verbose lthy'' result
    val _ =
      print_generated_result interactive verbose Thm.theoremK lthy''
        conformance
  in
    lthy''
  end

fun declare_and_print declaration interactive verbose lthy =
  let
    val (result, lthy') = declaration lthy
    val _ = print_declaration interactive verbose lthy' result
  in lthy' end

fun reject_contradictory_against command options against =
  (case (Symtab.lookup options conformance_flag, against) of
     (SOME (false, pos), SOME _) =>
       error
         (command ^ ": [urust_conformance_check = false] cannot be combined with `against`" ^
           Position.here pos)
   | _ => ())

fun define_urust
    (options, args as (binding, source, arguments), against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_expr" options against
    val verbose = configured_flag lthy options verbose_flag
    val abbreviation = configured_flag lthy options abbrev_flag
    fun declaration lthy' =
      declare_urust_result abbreviation args lthy'
    fun checked old_body =
      declare_with_frontend_check declaration binding
        (fn ctxt => fn complete_type =>
          old_frontend_expression ctxt complete_type arguments old_body)
        interactive verbose lthy
  in
    (case against of
       SOME (old_frontend, _) =>
         checked old_frontend
     | NONE =>
         if configured_flag lthy options conformance_flag
         then checked (old_frontend_source source)
         else declare_and_print declaration interactive verbose lthy)
  end

fun define_urust_fun
    (options, args as (_, _, _, _, body), against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_fun" options against
    val verbose = configured_flag lthy options verbose_flag
    val abbreviation = configured_flag lthy options abbrev_flag
    val (binding, _, _, parameters, _) = args
    fun declaration lthy' =
      declare_urust_fun_result abbreviation args lthy'
    fun checked old_body =
      declare_with_frontend_check declaration binding
        (fn ctxt => fn complete_type =>
          old_frontend_function ctxt complete_type parameters old_body)
        interactive verbose lthy
  in
    (case against of
       SOME (old_frontend, _) =>
         checked old_frontend
     | NONE =>
         if configured_flag lthy options conformance_flag
         then checked (old_frontend_source body)
         else declare_and_print declaration interactive verbose lthy)
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

val parse_argument =
  Scan.unless (Parse.$$$ "against")
    (Parse.position Parse.liberal_name || Parse.position Parse.underscore)

val parse_with_args =
  Scan.option
    ((Parse.position (Parse.$$$ "with_args") >> #2) --
      Scan.repeat parse_argument >>
      (fn (pos, arguments) =>
        if null arguments then
          error
            ("urust_expr: `with_args` requires at least one argument" ^
              Position.here pos)
        else arguments))

val parse_urust_expr =
  parse_command_options --
    (Parse.binding --
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source)) --
    parse_with_args --
    parse_against >>
  (fn (((options, (binding, source)), arguments), against) =>
    (options, (binding, source, the_default [] arguments), against))

val _ = Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_expr\<close>
          "Declare a uRust expression, optionally checking existing-frontend conformance by refl"
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
          "Declare a typed uRust function body, optionally checking existing-frontend conformance by refl"
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
