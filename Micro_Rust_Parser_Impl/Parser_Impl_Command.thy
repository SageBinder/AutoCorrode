theory Parser_Impl_Command
  imports
    Parser_Impl
    Parser_Impl_Translate
    Micro_Rust_Parsing_Legacy_Frontend.Micro_Rust_Parsing_Legacy_Frontend
  keywords
    "urust_expr" :: thy_decl
    and "urust_fn" :: thy_decl
    and "urust_notation" :: thy_decl
    and "against"
begin

section\<open> The command \<close>

text\<open>
The two outer commands deliberately share one declaration-body parser:
\<open>COMMAND [OPTIONS] NAME|_ [:: TYPE] [(ARG, ...)] src [against TERM]\<close>.
\<open>urust_expr\<close> infers an untyped expression or accepts a complete declaration type. A terminal
\<open>expression\<close> type produces an ordinary expression abstraction, while a terminal
\<open>function_body\<close> type wraps the body once in \<open>FunctionBody\<close>. \<open>urust_fn\<close> selects function
elaboration explicitly and therefore requires a complete curried type ending in
\<open>function_body\<close>; the common parser accepts an omitted type so that this requirement is reported
as a positioned semantic diagnostic rather than encoded in a second grammar.

The optional parenthesized, comma-separated argument list occurs immediately before the source
cartouche and accepts an empty list or trailing comma. Omitting it is equivalent to \<open>()\<close>.
Arguments introduce lexical names in source order. Without a declaration type, \<open>urust_expr\<close>
infers their types and produces \<open>\<lambda>ARG.... src\<close>. A declaration type supplies the complete
curried type, including one argument type per source argument. Other terminal constructors and
argument-count mismatches are rejected. Source-level HOL frees not introduced by the argument list
remain free during elaboration; ordinary named definitions expose non-contextual frees as definition
parameters, while existing context fixes remain local-theory dependencies. The dummy name \<open>_\<close>
elaborates and checks the result without registering a constant, definition, abbreviation, or code
equation. It receives a stable source-position-based name only for conformance facts and
informational output.
\<open>urust_conformance_check\<close> defaults to false. When enabled, the command also checks the generated
declaration against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend and records
\<open>NAME_conformance\<close>. Contextual legacy bodies are parsed under temporary fixes carrying the
new declaration's inferred argument types, then abstracted in the same order.

An optional trailing \<open>against old_term\<close> supplies a distinct existing-frontend term and implies
conformance checking even when the configuration is false. Combining it with an explicit
\<open>[conformance_check = false]\<close> is rejected by either command.

The scoped \<open>urust_abbrev\<close> configuration defaults to false and applies only to
\<open>urust_expr\<close>; the corresponding inline option is \<open>abbrev\<close>. False uses Isabelle's
standard definition mechanism, supplying
\<open>NAME_def\<close> and one default code equation without adding the definition to the global simp set.
True uses an input-only \<open>Local_Theory.abbrev\<close>, supplying neither artifact; checked client terms
contain the expanded right-hand side, and normal pretty printing does not fold it back to
\<open>NAME\<close>. Definition conformance unfolds only \<open>NAME_def\<close> before \<open>refl\<close>; abbreviation
conformance closes directly by \<open>refl\<close>. \<open>urust_fn\<close> always installs an ordinary definition,
does not accept an inline \<open>abbrev\<close> option, and ignores the scoped setting.

Successful interactive command output is controlled by the scoped \<open>urust_verbose\<close> configuration,
an integer from 0 to 2 that defaults to 0. Level 0 is quiet; level 1 prints complete definition
statements or abbreviation equations; level 2 additionally prints \<open>NAME_conformance\<close> when
checking is enabled. The standard interactive and \<open>show_results\<close> gates still control enabled
output.

The option parser is parameterized by a command-specific schema. Both commands accept Boolean
\<open>conformance_check\<close> and integer \<open>verbose\<close>; only \<open>urust_expr\<close> accepts Boolean
\<open>abbrev\<close>. These short names are inline-only aliases for the globally prefixed configurations.
Options may appear in any order. For Boolean options, omitting \<open>= true\<close> enables the option, so
both commands accept \<open>[conformance_check]\<close> and \<open>urust_expr\<close> also accepts
\<open>[abbrev]\<close>. Explicit \<open>= true\<close> and \<open>= false\<close> remain available; integer options always
require a value.
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
   URust_Parser.parse_source owns serialization of the generated runtime; elaboration and
   check_term remain outside that lock.

   Declaration installation, command-kind inference, conformance-proof assembly, the shared
   declaration-body parser, command-specific option schemas, both outer-command facades, and command
   registration are private implementation details. *)
structure URust_Command :> URUST_COMMAND =
struct
datatype elaboration_kind = Expression | Function

val urust_conformance_check =
  Attrib.setup_config_bool \<^binding>\<open>urust_conformance_check\<close> (K false)

val urust_verbose =
  Attrib.setup_config_int \<^binding>\<open>urust_verbose\<close> (K 0)

val urust_abbrev =
  Attrib.setup_config_bool \<^binding>\<open>urust_abbrev\<close> (K false)

val conformance_option = "conformance_check"
val verbose_option = "verbose"
val abbrev_option = "abbrev"

(* Command configurations:
   - urust_conformance_check controls reflexive old-frontend comparison for both commands; its
     inline alias is conformance_check.
   - urust_verbose is cumulative: 0 prints nothing, 1 prints the generated definition or
     abbreviation, and 2 additionally prints the generated conformance theorem; its inline alias is
     verbose.
   - urust_abbrev controls input-only abbreviations for urust_expr only; its inline alias is abbrev,
     and urust_fn always defines.
   Verbosity values outside 0..2 are rejected. *)
datatype command_option_value =
    Boolean_Value of bool
  | Integer_Value of int

datatype command_option_config =
    Boolean_Config of bool Config.T
  | Integer_Config of int Config.T

val common_option_configs =
  [(conformance_option, Boolean_Config urust_conformance_check),
   (verbose_option, Integer_Config urust_verbose)]

val expression_option_configs =
  Symtab.make
    (common_option_configs @
      [(abbrev_option, Boolean_Config urust_abbrev)])

val function_option_configs = Symtab.make common_option_configs

type command_options = (command_option_value * Position.T) Symtab.table

fun verbosity_error level pos =
  error
    ("uRust command option " ^ quote verbose_option ^
      " must be 0, 1, or 2, but found " ^ string_of_int level ^
      Position.here pos)

fun validate_verbosity pos level =
  if 0 <= level andalso level <= 2 then level
  else verbosity_error level pos

fun option_type_error name expected pos =
  error
    ("uRust command option " ^ quote name ^
      " expects " ^ expected ^
      Position.here pos)

fun add_inline_option option_configs
    ((name, name_pos), value) options =
  (case Symtab.lookup option_configs name of
     NONE =>
       error
         ("unknown uRust command option " ^ quote name ^
           Position.here name_pos)
   | SOME config =>
       if Symtab.defined options name
       then
         error
           ("duplicate uRust command option " ^ quote name ^
             Position.here name_pos)
       else
         let
           val checked_value =
             (case (config, value) of
                (Boolean_Config _, NONE) =>
                  Boolean_Value true
              | (Integer_Config _, NONE) =>
                  option_type_error name "an integer from 0 to 2" name_pos
              | (Boolean_Config _, SOME (Boolean_Value enabled, _)) =>
                  Boolean_Value enabled
              | (Integer_Config _, SOME (Integer_Value level, value_pos)) =>
                  Integer_Value (validate_verbosity value_pos level)
              | (Boolean_Config _, SOME (Integer_Value _, value_pos)) =>
                  option_type_error name "true or false" value_pos
              | (Integer_Config _, SOME (Boolean_Value _, value_pos)) =>
                  option_type_error name "an integer from 0 to 2" value_pos)
         in Symtab.update (name, (checked_value, name_pos)) options end)

fun configured_flag lthy options name config =
  (case Symtab.lookup options name of
     SOME (Boolean_Value enabled, _) => enabled
   | SOME (Integer_Value _, _) =>
       error ("internal non-Boolean uRust command option " ^ quote name)
   | NONE => Config.get lthy config)

fun configured_verbosity lthy options =
  (case Symtab.lookup options verbose_option of
     SOME (Integer_Value level, _) => level
   | SOME (Boolean_Value _, _) =>
       error ("internal non-integer uRust command option " ^ quote verbose_option)
   | NONE => validate_verbosity Position.none (Config.get lthy urust_verbose))

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

fun command_label Expression = "urust_expr"
  | command_label Function = "urust_fn"

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
           ("urust_fn: declared result type must be function_body" ^
             Position.here type_pos)
   | (Expression, _) =>
       error
         ("urust_expr: declared result type must be expression" ^
           Position.here type_pos)
   | (Function, _) =>
       error
         ("urust_fn: declared result type must be function_body" ^
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
        (command_label kind ^ ": declared type expects " ^ string_of_int expected ^
          " " ^ role ^ (if expected = 1 then "" else "s") ^
          ", but " ^ string_of_int actual ^
          (if actual = 1 then " name was" else " names were") ^
          " supplied" ^ Position.here count_pos)
  end

fun typed_arguments arguments parameter_types =
  map2 (fn argument => fn T => (argument, T))
    arguments parameter_types

fun require_function_type source declared_type =
  (case declared_type of
     SOME raw_type => raw_type
   | NONE =>
       error
         ("urust_fn: function elaboration requires a declared type" ^
           Position.here (Input.pos_of source)))

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
   | (Function, function_type) =>
       let
         val (complete_type, type_pos) =
           require_function_type source function_type
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
  | empty_source_message Function = "urust_fn: empty function body"

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
               ("urust_fn: unresolved body name " ^ quote name ^
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
             (command_label kind ^
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
      (case URust_Parser.parse_source lthy source of
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
  | Anonymous_Result of
      {term: term, name: string, kind: elaboration_kind}

datatype declaration_target =
    Named_Target of Binding.binding
  | Anonymous_Target of Position.T

fun anonymous_binding kind pos =
  let
    val line = the_default 0 (Position.line_of pos)
    val offset = the_default 0 (Position.offset_of pos)
  in
    Binding.make
      (command_label kind ^ "_anonymous_" ^
        string_of_int line ^ "_" ^ string_of_int offset,
       pos)
  end

fun target_binding _ (Named_Target binding) = binding
  | target_binding kind (Anonymous_Target pos) =
      anonymous_binding kind pos

fun declaration_conformance_term
      (Definition_Result {lhs, ...}) = lhs
  | declaration_conformance_term
      (Abbreviation_Result {rhs, ...}) = rhs
  | declaration_conformance_term
      (Anonymous_Result {term, ...}) = term

fun declaration_name fallback lhs =
  (case Term.head_of lhs of
     Const (name, _) => name
   | Free (name, _) => name
   | _ => fallback)

fun install_urust_result abbreviation binding term lthy =
  let
    val name = Binding.name_of binding
    (* Keep declaration installation silent even when show_results is enabled; the cumulative
       urust_verbose levels below are the sole result-output policy. *)
    val show_results = Config.get lthy Proof_Display.show_results
    val silent_lthy = Config.put Proof_Display.show_results false lthy
    val definition_parameters =
      Term.add_frees term []
      |> filter_out (Variable.is_fixed lthy o #1)
      |> rev
      |> map Free
    val definition_lhs =
      list_comb
        (Free
          (name,
           map fastype_of definition_parameters --->
             fastype_of term),
         definition_parameters)
  in
    if abbreviation then
      let
        val ((lhs, rhs), lthy') =
          Local_Theory.abbrev Syntax.mode_input
            ((binding, NoSyn), term) silent_lthy
        val full_name =
          declaration_name (Local_Theory.full_name lthy binding) lhs
      in
        (Abbreviation_Result
          {lhs = lhs, rhs = rhs, name = full_name},
         Config.put Proof_Display.show_results show_results lthy')
      end
    else
      let
        val ((defined_lhs, (fact_name, theorem)), lthy') =
          Specification.definition
            (SOME (binding, NONE, NoSyn)) [] []
            ((Thm.def_binding binding, []),
              Logic.mk_equals (definition_lhs, term)) silent_lthy
        val lhs = list_comb (defined_lhs, definition_parameters)
      in
        (Definition_Result
          {lhs = lhs, fact_name = fact_name, theorem = theorem},
         Config.put Proof_Display.show_results show_results lthy')
      end
  end

fun declare_urust_result abbreviation kind
    (target, declared_type, source, arguments_pos, arguments) lthy =
  let
    val term =
      elaborate lthy
        {kind = kind,
         source = source,
         arguments = arguments,
         arguments_pos = arguments_pos,
         declared_type = declared_type}
  in
    (case target of
       Named_Target binding =>
         install_urust_result abbreviation binding term lthy
     | Anonymous_Target _ =>
         let
           val binding = target_binding kind target
         in
           (Anonymous_Result
              {term = term,
               name = Local_Theory.full_name lthy binding,
               kind = kind},
            lthy)
         end)
  end

fun old_frontend_source source = "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"

fun print_generated_result interactive verbosity minimum kind lthy (name, thms) =
  if verbosity >= minimum
  then
    Proof_Display.print_results
      {interactive = interactive, pos = Position.thread_data ()}
      lthy ((kind, name), [("", thms)])
  else ()

fun print_abbreviation interactive verbosity lthy name lhs rhs =
  if verbosity >= 1 andalso
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
  else ()

fun print_anonymous interactive verbosity lthy kind name term =
  if verbosity >= 1 andalso
     (interactive orelse Config.get lthy Proof_Display.show_results)
  then
    Pretty.writeln_urgent
      (Pretty.block1
        [Pretty.block
           [Pretty.mark_position (Position.thread_data ())
              (Pretty.keyword1 (command_label kind)),
            Pretty.brk 1,
            Pretty.str (Long_Name.base_name name),
            Pretty.str ":"],
         Pretty.fbrk,
         Syntax.pretty_term lthy term])
  else ()

fun print_declaration interactive verbosity lthy declaration =
  (case declaration of
     Definition_Result {fact_name, theorem, ...} =>
       print_generated_result interactive verbosity 1 "definition" lthy
         (fact_name, [theorem])
   | Abbreviation_Result {lhs, rhs, name} =>
       print_abbreviation interactive verbosity lthy name lhs rhs
   | Anonymous_Result {term, name, kind} =>
       print_anonymous interactive verbosity lthy kind name term)

fun note_conformance binding declaration old_frontend lthy =
  let
    val lhs = declaration_conformance_term declaration
    val equality =
      Syntax.check_term lthy
        (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ old_frontend)
    val unfixed_frees =
      Term.add_frees equality []
      |> filter_out (Variable.is_fixed lthy o #1)
      |> rev
    val fixes =
      map
        (fn (name, T) => (Binding.name name, SOME T, NoSyn))
        unfixed_frees
    val (internal_names, proof_ctxt) =
      Proof_Context.add_fixes fixes (Variable.set_body true lthy)
    val internal_frees =
      map2
        (fn (_, T) => fn internal_name => Free (internal_name, T))
        unfixed_frees internal_names
    val proof_equality =
      Term.subst_atomic
        (map Free unfixed_frees ~~ internal_frees)
        equality
    val conformance =
      Goal.prove proof_ctxt [] [] (HOLogic.mk_Trueprop proof_equality)
        (fn {context = ctxt, ...} =>
          (case declaration of
             Definition_Result {theorem, ...} =>
               Local_Defs.unfold_tac ctxt [theorem] THEN
               resolve_tac ctxt [@{thm refl}] 1
           | Abbreviation_Result _ =>
               resolve_tac ctxt [@{thm refl}] 1
           | Anonymous_Result _ =>
               resolve_tac ctxt [@{thm refl}] 1))
      |> singleton (Variable.export proof_ctxt lthy)
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
             "urust_fn: internal malformed function_body result type")
  in
    with_typed_fixes lthy "urust_fn" declared_type parameters
      body_type URust_Shallow_Terms.function_body old_body_source
  end

fun declare_with_frontend_check
    declaration binding make_old interactive verbosity lthy =
  let
    val (result, lthy') = declaration lthy
    val declaration_term = declaration_conformance_term result
    val old_frontend =
      make_old
        (Variable.declare_term declaration_term lthy')
        (fastype_of declaration_term)
    val (conformance, lthy'') =
      note_conformance binding result old_frontend lthy'
    val _ = print_declaration interactive verbosity lthy'' result
    val _ =
      print_generated_result interactive verbosity 2 Thm.theoremK lthy''
        conformance
  in
    lthy''
  end

fun declare_and_print declaration interactive verbosity lthy =
  let
    val (result, lthy') = declaration lthy
    val _ = print_declaration interactive verbosity lthy' result
  in lthy' end

fun reject_contradictory_against command options against =
  (case (Symtab.lookup options conformance_option, against) of
     (SOME (Boolean_Value false, pos), SOME _) =>
       error
         (command ^ ": [conformance_check = false] cannot be combined with `against`" ^
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

fun define_urust_expr
    (options,
     args as (target, declared_type, source, _, arguments),
     against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_expr" options against
    val verbosity = configured_verbosity lthy options
    val abbreviation =
      configured_flag lthy options abbrev_option urust_abbrev
    val kind = command_elaboration_kind lthy declared_type
    val binding = target_binding kind target
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
        interactive verbosity lthy
  in
    (case against of
       SOME (old_frontend, _) =>
         checked old_frontend
     | NONE =>
         if configured_flag lthy options conformance_option
              urust_conformance_check
         then checked (old_frontend_source source)
         else declare_and_print declaration interactive verbosity lthy)
  end

fun define_urust_fn
    (options,
     (target, declared_type, body, parameters_pos, parameters),
     against) interactive lthy =
  let
    val _ = reject_contradictory_against "urust_fn" options against
    val verbosity = configured_verbosity lthy options
    val raw_type = require_function_type body declared_type
    val binding = target_binding Function target
    fun declaration lthy' =
      declare_urust_result false Function
        (target, SOME raw_type, body, parameters_pos, parameters) lthy'
    fun checked old_body =
      declare_with_frontend_check declaration binding
        (fn ctxt => fn complete_type =>
          close_typed_term Function ctxt (#2 raw_type)
            (old_frontend_function ctxt complete_type parameters old_body))
        interactive verbosity lthy
  in
    (case against of
       SOME (old_frontend, _) =>
         checked old_frontend
     | NONE =>
         if configured_flag lthy options conformance_option
              urust_conformance_check
         then checked (old_frontend_source body)
         else declare_and_print declaration interactive verbosity lthy)
  end

val parse_option_value =
  Parse.position (Parse.reserved "true") >>
    (fn (_, pos) => (Boolean_Value true, pos)) ||
  Parse.position (Parse.reserved "false") >>
    (fn (_, pos) => (Boolean_Value false, pos)) ||
  Parse.position Parse.int >>
    (fn (level, pos) => (Integer_Value level, pos))

val parse_inline_option =
  Parse.name_position --
    Scan.option (Parse.$$$ "=" |-- parse_option_value)

fun parse_command_options option_configs =
  Scan.optional
    (Parse.$$$ "[" |--
      Parse.!!! (Parse.enum1 "," parse_inline_option --| Parse.$$$ "]") >>
      (fn options =>
        fold (add_inline_option option_configs) options Symtab.empty))
    Symtab.empty

val parse_against =
  Scan.option
    (Parse.position (Parse.$$$ "against") -- Parse.term >>
      (fn ((_, pos), term) => (term, pos)))

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

val parse_declared_type =
  Scan.option (Parse.$$$ "::" |-- Parse.position Parse.typ)

val parse_declaration_target =
  (Parse.position Parse.underscore >>
    (fn (_, pos) => Anonymous_Target pos)) ||
  (Parse.binding >> Named_Target)

fun parse_urust_declaration option_configs =
  parse_command_options option_configs --
    (parse_declaration_target --
      parse_declared_type --
      Scan.option parse_parameters --
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source) >>
      (fn (((target, declared_type), parameters), source) =>
        (target, declared_type, parameters, source))) --
    parse_against >>
  (fn ((options, (target, declared_type, parameter_clause, source)), against) =>
    let
      val (arguments_pos, arguments) =
        (case parameter_clause of
           SOME clause => clause
         | NONE => (#2 (Input.range_of source), []))
    in
      (options,
       (target, declared_type, source, arguments_pos, arguments),
       against)
    end)

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_expr\<close>
    "Declare a uRust expression, optionally checking existing-frontend conformance by refl"
    (parse_urust_declaration expression_option_configs >>
      define_urust_expr)

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_fn\<close>
    "Declare a typed uRust function body, optionally checking existing-frontend conformance by refl"
    (parse_urust_declaration function_option_configs >>
      define_urust_fn)
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
        (case URust_Parser.parse_source ctxt source of
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
