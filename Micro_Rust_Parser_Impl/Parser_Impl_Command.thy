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
\<open>urust_expr [OPTIONS] NAME [:: TYPE] src [with_args ARG...] [against TERM]\<close> parses,
elaborates, and checks once. A nonempty \<open>with_args\<close> suffix introduces lexical arguments in
source order and must precede \<open>against\<close>. Without a declaration type their types are inferred and
the result is \<open>\<lambda>ARG.... src\<close>. A declaration type supplies the complete curried type,
including one argument type per source argument. A terminal \<open>expression\<close> type produces an
ordinary expression abstraction, while a terminal \<open>function_body\<close> type wraps the body once in
\<open>FunctionBody\<close>. Other terminal constructors are rejected. The optional comma-separated inline
options override the corresponding scoped configurations.
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

\<open>urust_fun [OPTIONS] NAME :: TYPE (parameters) src [against TERM]\<close> remains the explicit
function facade. It requires a curried type ending in \<open>function_body\<close>, preserves its existing
parameter syntax and diagnostics, and delegates to the same elaborator as \<open>urust_expr\<close>.

Both commands accept the same extensible boolean-option list. Current options are
\<open>urust_conformance_check\<close>, \<open>urust_verbose\<close>, and \<open>urust_abbrev\<close>; they may appear in
any order.
\<close>
ML\<open>
signature URUST_COMMAND =
sig
  datatype elaboration_kind = Expression | Function

  val elaborate:
    local_theory ->
      {kind: elaboration_kind,
       source: Input.source,
       arguments: (string * Position.T) list,
       arguments_pos: Position.T,
       declared_type: (string * Position.T) option} ->
      term
end

(* THE expression pipeline, exported: every declaration command and programmatic client supplies an
   explicit elaboration kind to elaborate. Expression accepts no type or a complete declaration type
   ending in expression; Function requires a curried declaration type ending in function_body. Typed
   argument types are allocated before AST lowering, the complete unchecked term receives one
   Type.constraint, and the result passes through Syntax.check_term exactly once. Residual internal
   type variables that occur in neither the checked declaration type nor already-declared ambient
   fixed-parameter types are then closed with its terminal value channel. All failures are positioned.
   URust_Diagnostics.parse_source owns serialization of the generated runtime; elaboration and
   check_term remain outside that lock.

   Declaration installation, command-kind inference, conformance-proof assembly, both outer-command
   facades, and command registration are private implementation details. *)
structure URust_Command :> URUST_COMMAND =
struct
datatype elaboration_kind = Expression | Function

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

fun read_declared_type lthy (raw_type, type_pos) =
  (case Exn.result (Syntax.read_typ lthy) raw_type of
     Exn.Res declared_type => (declared_type, type_pos)
   | Exn.Exn exn =>
       if Exn.is_interrupt exn then Exn.reraise exn
       else
         error
           (Runtime.exn_message exn ^
             Position.here type_pos))

fun terminal_type declared_type =
  #2 (Term.strip_type declared_type)

fun is_terminal_type expected (Type (name, _)) = name = expected
  | is_terminal_type _ _ = false

fun is_function_body_type T =
  is_terminal_type \<^type_name>\<open>function_body\<close> T

fun command_name Expression = "urust_expr"
  | command_name Function = "urust_fun"

fun argument_role Expression = "argument"
  | argument_role Function = "parameter"

fun terminal_value_type kind type_pos declared_type =
  (case (kind, terminal_type declared_type) of
     (Expression, Type (name, [_, valueT, _, _, _, _])) =>
       if name = \<^type_name>\<open>expression\<close> then valueT
       else
         error
           ("urust_expr: declared result type must be expression" ^
             Position.here type_pos)
   | (Function, Type (name, [_, valueT, _, _, _])) =>
       if name = \<^type_name>\<open>function_body\<close> then valueT
       else
         error
           ("urust_fun: declared result type must be function_body" ^
             Position.here type_pos)
   | (Expression, _) =>
       error
         ("urust_expr: declared result type must be expression" ^
           Position.here type_pos)
   | (Function, _) =>
       error
         ("urust_fun: declared result type must be function_body" ^
           Position.here type_pos))

fun validate_argument_count kind arguments_pos arguments parameter_types =
  let
    val expected = length parameter_types
    val actual = length arguments
    val role = argument_role kind
    val count_pos =
      if actual > expected
      then #2 (nth arguments expected)
      else arguments_pos
  in
    if expected = actual then ()
    else
      error
        (command_name kind ^ ": declared type expects " ^ string_of_int expected ^
          " " ^ role ^ (if expected = 1 then "" else "s") ^
          ", but " ^ string_of_int actual ^
          (if actual = 1 then " name was" else " names were") ^
          " supplied" ^ Position.here count_pos)
  end

fun typed_arguments arguments parameter_types =
  map2 (fn argument => fn T => (argument, T))
    arguments parameter_types

fun prepare_arguments kind source arguments_pos arguments declared_type =
  (case (kind, declared_type) of
     (Expression, NONE) =>
       map (fn argument => (argument, dummyT)) arguments
   | (Expression, SOME (complete_type, type_pos)) =>
       let
         val _ =
           terminal_value_type Expression type_pos complete_type
         val (argument_types, _) = Term.strip_type complete_type
         val _ =
           validate_argument_count Expression
             arguments_pos arguments argument_types
       in typed_arguments arguments argument_types end
   | (Function, NONE) =>
       error
         ("urust_fun: function elaboration requires a declared type" ^
           Position.here (Input.pos_of source))
   | (Function, SOME (complete_type, type_pos)) =>
       let
         val _ = terminal_value_type Function type_pos complete_type
         val (argument_types, _) = Term.strip_type complete_type
         val _ =
           validate_argument_count Function
             arguments_pos arguments argument_types
       in typed_arguments arguments argument_types end)

fun lower kind lthy arguments ast =
  (case kind of
     Expression => URust_Translate.mk_expression lthy arguments ast
   | Function => URust_Translate.mk_function lthy arguments ast)

fun empty_source_message Expression = "urust_expr: empty expression"
  | empty_source_message Function = "urust_fun: empty function body"

fun reject_unresolved Function lthy source checked =
      let
        val unresolved =
          Term.add_frees checked []
          |> filter_out (Variable.is_fixed lthy o #1)
          |> sort_by #1
      in
        (case unresolved of
           (name, _) :: _ =>
             error
               ("urust_fun: unresolved body name " ^ quote name ^
                 Position.here (Input.pos_of source))
         | [] => ())
      end
  | reject_unresolved Expression _ _ _ = ()

fun close_typed_term kind lthy type_pos checked =
  let
    val declaration_type = fastype_of checked
    val declared_tvars = Term.add_tvarsT declaration_type []
    fun declared_tvar (xi, _) =
      exists (fn (declared_xi, _) => declared_xi = xi) declared_tvars
    val residual_tvars =
      Term.add_tvars checked []
      |> filter_out declared_tvar
      |> sort_by (Term.string_of_vname o #1)
    val declared_tfrees = Term.add_tfreesT declaration_type []
    fun declared_tfree tfree = member (op =) declared_tfrees tfree
    val used_fixed_types =
      map #2 (Variable.add_fixed lthy checked [])
    val declared_fixed_types =
      map_filter (Variable.default_type lthy o #2)
        (Variable.dest_fixes lthy)
    val ambient_tfrees =
      fold Term.add_tfreesT
        (used_fixed_types @ declared_fixed_types) []
    fun ambient_tfree tfree = member (op =) ambient_tfrees tfree
    val residual_tfrees =
      Term.add_tfrees checked []
      |> filter_out
           (fn tfree =>
             declared_tfree tfree orelse ambient_tfree tfree)
      |> sort_by #1
    val residual_types =
      map (fn variable as (_, sort) => (TVar variable, sort))
        residual_tvars @
      map (fn variable as (_, sort) => (TFree variable, sort))
        residual_tfrees
      |> sort_by (Syntax.string_of_typ lthy o #1)
    val value_type =
      terminal_value_type kind type_pos declaration_type
    val thy = Proof_Context.theory_of lthy
    val incompatible =
      filter_out (fn (_, sort) => Sign.of_sort thy (value_type, sort))
        residual_types
    val _ =
      (case incompatible of
         (variable_type, _) :: _ =>
           error
             (command_name kind ^
               ": inferred internal type variable " ^
               quote (Syntax.string_of_typ lthy variable_type) ^
               " is incompatible with the declared result value type" ^
               Position.here type_pos)
       | [] => ())
  in
    Term.subst_atomic_types
      (map (fn (variable_type, _) => (variable_type, value_type))
        residual_types)
      checked
  end

fun elaborate lthy
    {kind, source, arguments, arguments_pos, declared_type = raw_declared_type} : term =
  let
    val declared_type =
      Option.map (read_declared_type lthy) raw_declared_type
    val arguments_with_types =
      prepare_arguments kind source arguments_pos arguments declared_type
    val ast =
      (case URust_Diagnostics.parse_source lthy source of
         SOME expression => expression
       | NONE =>
           error
             (empty_source_message kind ^
               Position.here (Input.pos_of source)))
    val unchecked = lower kind lthy arguments_with_types ast
    val constrained =
      (case declared_type of
         SOME (complete_type, _) =>
           Type.constraint complete_type unchecked
       | NONE => unchecked)
    val checked = Syntax.check_term lthy constrained
    val closed =
      (case declared_type of
         SOME (_, type_pos) =>
           close_typed_term kind lthy type_pos checked
       | NONE => checked)
    val _ = reject_unresolved kind lthy source closed
  in
    closed
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

fun declare_urust_result abbreviation kind
    (binding, declared_type, source, arguments_pos, arguments) lthy =
  let
    val term =
      elaborate lthy
        {kind = kind,
         source = source,
         arguments = arguments,
         arguments_pos = arguments_pos,
         declared_type = declared_type}
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

fun command_elaboration_kind lthy declared_type =
  (case declared_type of
     NONE => Expression
   | SOME raw_type =>
       if is_function_body_type
           (terminal_type (#1 (read_declared_type lthy raw_type)))
       then Function
       else Expression)

fun close_declared_legacy kind declared_type lthy term =
  (case declared_type of
     SOME (_, type_pos) => close_typed_term kind lthy type_pos term
   | NONE => term)

fun define_urust
    (options,
     args as (binding, declared_type, source, _, arguments),
     against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_expr" options against
    val verbose = configured_flag lthy options verbose_flag
    val abbreviation = configured_flag lthy options abbrev_flag
    val kind = command_elaboration_kind lthy declared_type
    fun declaration lthy' =
      declare_urust_result abbreviation kind args lthy'
    fun checked old_body =
      declare_with_frontend_check declaration binding
        (fn ctxt => fn complete_type =>
          close_declared_legacy kind declared_type ctxt
            (case kind of
               Expression =>
                 old_frontend_expression ctxt complete_type arguments old_body
             | Function =>
                 old_frontend_function ctxt complete_type arguments old_body))
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
    (options,
     (binding, raw_type, parameters_pos, parameters, body),
     against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_fun" options against
    val verbose = configured_flag lthy options verbose_flag
    val abbreviation = configured_flag lthy options abbrev_flag
    fun declaration lthy' =
      declare_urust_result abbreviation Function
        (binding, SOME raw_type, body, parameters_pos, parameters) lthy'
    fun checked old_body =
      declare_with_frontend_check declaration binding
        (fn ctxt => fn complete_type =>
          close_typed_term Function ctxt (#2 raw_type)
            (old_frontend_function ctxt complete_type parameters old_body))
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
        else (pos, arguments)))

val parse_declared_type =
  Scan.option (Parse.$$$ "::" |-- Parse.position Parse.typ)

val parse_urust_expr =
  parse_command_options --
    (Parse.binding --
      parse_declared_type --
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source) >>
      (fn ((binding, declared_type), source) =>
        (binding, declared_type, source))) --
    parse_with_args --
    parse_against >>
  (fn (((options, (binding, declared_type, source)), argument_clause), against) =>
    let
      val (arguments_pos, arguments) =
        (case argument_clause of
           SOME clause => clause
         | NONE => (#2 (Input.range_of source), []))
    in
      (options,
       (binding, declared_type, source, arguments_pos, arguments),
       against)
    end)

val _ = Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_expr\<close>
          "Declare a typed or inferred uRust expression, optionally checking existing-frontend conformance by refl"
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
