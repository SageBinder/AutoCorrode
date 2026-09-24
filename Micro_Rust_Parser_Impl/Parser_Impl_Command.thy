theory Parser_Impl_Command
  imports
    Parser_Impl_Grammar
    Parser_Impl_Printer_Output
    Parser_Impl_Translate
    Parser_Impl_Datatype
  keywords
    "urust_expr" :: thy_decl
    and "urust_fn" :: thy_decl
    and "urust_datatype" :: thy_decl
    and "urust_notation" :: thy_decl
begin

section\<open> The command \<close>

text\<open>
The expression and legacy function-body forms share one declaration-body parser:
\<open>COMMAND [OPTIONS] NAME|_ [:: TYPE] [(ARG|_, ...)] src\<close>.
\<open>urust_expr\<close> infers an untyped expression or accepts a complete declaration type. A terminal
\<open>expression\<close> type produces an ordinary expression abstraction, while a terminal
\<open>function_body\<close> type wraps the body once in \<open>FunctionBody\<close>. \<open>urust_fn\<close> selects function
elaboration explicitly and therefore requires a complete curried type ending in
\<open>function_body\<close>. An exact terminal type placeholder \<open>_\<close> is completed to a fresh
five-parameter \<open>function_body\<close> before the existing checked elaboration infers its channels.
Internal placeholders and declared argument types are preserved. The common parser accepts an omitted
type so that this requirement is reported as a positioned semantic diagnostic rather than encoded in
a second grammar.

The optional parenthesized, comma-separated argument list occurs immediately before the source
cartouche and accepts an empty list or trailing comma. Omitting it is equivalent to \<open>()\<close>.
\<open>Parse.liberal_name\<close> admits ordinary identifiers, symbolic names, quoted names, and minor
keywords such as \<open>for\<close>. Isabelle major command keywords delimit command spans before this parser
runs, so use string quoting for those names, for example \<open>("lemma")\<close>. Named arguments introduce
lexical names in source order. A bare \<open>_\<close> instead consumes one ordered type slot and produces a
typed anonymous abstraction without introducing a resolvable name; repeated and mixed wildcards are
permitted, while duplicate named arguments remain rejected. Without a declaration type,
\<open>urust_expr\<close> infers all slot types and produces the corresponding abstraction. A declaration type
supplies the complete curried type, including one argument type per source slot. Other terminal
constructors and argument-count mismatches are rejected. Source-level HOL frees not introduced by
the argument list remain free during elaboration; ordinary named definitions expose non-contextual
frees as definition parameters, while existing context fixes remain local-theory dependencies. The
dummy declaration target \<open>_\<close> elaborates and checks the result without registering a constant,
definition, abbreviation, or code equation. It receives a stable source-position-based name only for
informational output.
Ordinary named definitions preserve the complete curried term on the right-hand side of
\<open>NAME_def\<close> by default. The Boolean \<open>application_def\<close> option instead retains explicit source
arguments on the theorem's left-hand side, producing
\<open>NAME arg\<^sub>1 ... arg\<^sub>n \<equiv> body\<close>. Implicit definition parameters remain before those
explicit arguments. Both forms install the same curried constant value, attributes, and code
equation. The application form is useful when existing proofs fold a named
sub-expression, while the default form remains suitable for rewriting a bare function constant.
Pretty output follows the same shape: default definitions display source arguments as a uRust
closure on the right-hand side, while application definitions display them only on the left.
Zero-argument definitions are identical in either mode. Anonymous declarations are unchanged, and
input abbreviations reject an effective \<open>application_def = true\<close>; an inline false value may
override a true scoped setting.
\<open>urust_pp_test\<close> defaults to false. Its common Boolean inline alias is \<open>pp_test\<close>. When
enabled, the parsed AST is serialized, reparsed without source positions, and compared through the
position-independent serialized token stream before lowering. A successful check is silent. A
mismatch aborts before declaration installation and reports the generated source plus the first
differing token index.

\<open>urust_pretty\<close> defaults to false. Its common Boolean inline alias is \<open>pretty\<close>. At verbosity
levels 1 and 2, false retains the ordinary HOL rendering of generated definitions, abbreviations,
and anonymous results; true instead prints the same declaration heading and left-hand side with the
right-hand side rendered as human-readable uRust inside a symbolic \<open>\<mu>\<open>...\<close>\<close> wrapper.
The wrapper is presentation only and is unrelated to source quotation syntax. At verbosity 0 no
result is printed; an effective \<open>pretty = true\<close> receives a warning because it has no effect.
Source arguments appear as closure formals on the right unless
\<open>application_def = true\<close> puts them on the left.

The scoped \<open>urust_abbrev\<close> configuration defaults to false and applies to both commands; the
corresponding inline option is \<open>abbrev\<close>. False uses Isabelle's
standard definition mechanism, supplying
\<open>NAME_def\<close> and one default code equation without adding the definition to the global simp set.
True uses an input-only \<open>Local_Theory.abbrev\<close>, supplying neither artifact; checked client terms
contain the expanded right-hand side, and normal pretty printing does not fold it back to
\<open>NAME\<close>.

Both commands accept \<open>attrs = [ATTRIBUTE, ...]\<close> for named definitions. Isabelle's standard
attribute parser checks the list, including the empty list, and applies it only to the generated
\<open>NAME_def\<close> theorem. Anonymous declarations and abbreviation mode reject
\<open>attrs\<close>.

Successful interactive command output is controlled by the scoped \<open>urust_verbosity\<close> configuration,
an integer from 0 to 2 that defaults to 0. Level 0 is quiet; levels 1 and 2 print complete definition
statements or abbreviation equations. The standard interactive and \<open>show_results\<close> gates still
control enabled output.

\<open>urust_datatype\<close> accepts the common scoped/inline \<open>pp_test\<close>, \<open>pretty\<close>, and
\<open>verbosity\<close> options. It accepts an optional HOL binding followed by one required source
cartouche containing a complete Rust-shaped struct or enum item. Composite and user-defined HOL
field types use \<open>\<tau>\<open>TYPE\<close>\<close>, mirroring the \<open>\<epsilon>\<open>TERM\<close>\<close> expression
antiquotation. An omitted binding is inferred with acronym-aware ASCII snake case. Level 0 is quiet;
level 1 reports the completed public type, constructors, selectors, lenses, and exact Rust mappings;
level 2 adds the normalized generated HOL declaration and complete public selector/lens definitions.
With \<open>pretty = true\<close>, levels 1 and 2 additionally show the normalized human-readable uRust
declaration after the manifest. Its markup is replayed against the completed generated artifacts
without generating or registering anything again. Generation and item-scope registration run
silently and atomically before any result report. Datatype \<open>pp_test\<close> runs before generation.

The option parser is parameterized by a command-specific schema. Both commands accept Boolean
\<open>pp_test\<close>, \<open>pretty\<close>, \<open>application_def\<close>, and \<open>abbrev\<close>, integer
\<open>verbosity\<close>, and attribute-list \<open>attrs\<close>. The configuration-backed short names are
inline-only aliases for the globally prefixed configurations. Options may appear in any order. For
Boolean options, omitting \<open>= true\<close> enables the option, so both commands accept
\<open>[pp_test]\<close>, \<open>[pretty]\<close>, \<open>[application_def]\<close>, and \<open>[abbrev]\<close>. Explicit
\<open>= true\<close> and \<open>= false\<close> remain available; integer and attribute-list options always require a
value.

An argument-taking abbreviation declaration exposes a parser expression or function body as a HOL
helper. At HOL use sites, write \<open>(helper args)\<close> when surrounding syntax would otherwise group the
helper application incorrectly.
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
   ending in expression; Function requires a curried declaration type ending in function_body, or an
   exact terminal _ that is completed before checking. Typed declaration slots are allocated before
   AST lowering: named slots become lexical Frees and wildcard slots become typed anonymous
   abstractions without entering name resolution. The complete unchecked term receives one
   Type.constraint, and the result passes through Syntax.check_term exactly once. Residual internal
   type variables that occur in neither the checked declaration type nor already-declared ambient
   fixed-parameter types are then closed with its terminal value channel. All failures are positioned.
   URust_Parser.parse_source owns serialization of the generated runtime; elaboration and check_term
   remain outside that lock.

   Declaration installation, command-kind inference, the shared declaration-body parser,
   command-specific option schemas, both outer-command facades, and command registration are private
   implementation details. *)
structure URust_Command :> URUST_COMMAND =
struct
datatype elaboration_kind = Expression | Function
structure Navigation = Micro_Rust_Semantic_Navigation

val urust_pp_test =
  Attrib.setup_config_bool \<^binding>\<open>urust_pp_test\<close> (K false)

val urust_pretty =
  Attrib.setup_config_bool \<^binding>\<open>urust_pretty\<close> (K false)

val urust_verbosity =
  Attrib.setup_config_int \<^binding>\<open>urust_verbosity\<close> (K 0)

val urust_abbrev =
  Attrib.setup_config_bool \<^binding>\<open>urust_abbrev\<close> (K false)

val urust_application_def =
  Attrib.setup_config_bool \<^binding>\<open>urust_application_def\<close> (K false)

val pp_test_option = "pp_test"
val pretty_option = "pretty"
val verbosity_option = "verbosity"
val abbrev_option = "abbrev"
val application_def_option = "application_def"
val attributes_option = "attrs"

(* Command configurations:
   - urust_pp_test performs a serialized parse-print-parse token comparison for both commands; its
     inline alias is pp_test.
   - urust_pretty selects human uRust in a symbolic \<mu>\<open>...\<close> wrapper for
     verbosity-controlled declaration right-hand sides; its inline alias is pretty.
   - urust_verbosity is cumulative: 0 prints nothing, while 1 and 2 print the generated definition
     or abbreviation; its inline alias is verbosity.
   - urust_abbrev controls input-only abbreviations for both declaration commands; its inline alias
     is abbrev.
   - urust_application_def puts explicit source arguments on the generated definition theorem's
     left-hand side; its inline alias is application_def.
   - attrs is inline-only and carries Isabelle theorem attributes for the generated _def theorem of
     a named definition.
   Verbosity values outside 0..2 are rejected. *)
datatype command_option_value =
    Boolean_Value of bool
  | Integer_Value of int
  | Attributes_Value of Token.src list

datatype command_option_config =
    Boolean_Config of bool Config.T
  | Integer_Config of int Config.T
  | Attributes_Config

val common_option_configs =
  [(pp_test_option, Boolean_Config urust_pp_test),
   (pretty_option, Boolean_Config urust_pretty),
   (verbosity_option, Integer_Config urust_verbosity),
   (application_def_option, Boolean_Config urust_application_def),
   (attributes_option, Attributes_Config)]

val declaration_option_configs =
  Symtab.make
    (common_option_configs @
      [(abbrev_option, Boolean_Config urust_abbrev)])

val expression_option_configs = declaration_option_configs
val function_option_configs = declaration_option_configs

val datatype_option_configs =
  Symtab.make
    [(pp_test_option, Boolean_Config urust_pp_test),
     (pretty_option, Boolean_Config urust_pretty),
     (verbosity_option, Integer_Config urust_verbosity)]

type command_options = (command_option_value * Position.T) Symtab.table

fun verbosity_error name level pos =
  error
    ("uRust command option " ^ quote name ^
      " must be 0, 1, or 2, but found " ^ string_of_int level ^
      Position.here pos)

fun validate_verbosity name pos level =
  if 0 <= level andalso level <= 2 then level
  else verbosity_error name level pos

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
              | (Attributes_Config, NONE) =>
                  option_type_error name "an Isabelle attribute list" name_pos
              | (Boolean_Config _, SOME (Boolean_Value enabled, _)) =>
                  Boolean_Value enabled
              | (Integer_Config _, SOME (Integer_Value level, value_pos)) =>
                  Integer_Value (validate_verbosity name value_pos level)
              | (Attributes_Config, SOME (Attributes_Value attributes, _)) =>
                  Attributes_Value attributes
              | (Boolean_Config _, SOME (Integer_Value _, value_pos)) =>
                  option_type_error name "true or false" value_pos
              | (Boolean_Config _, SOME (Attributes_Value _, value_pos)) =>
                  option_type_error name "true or false" value_pos
              | (Integer_Config _, SOME (Boolean_Value _, value_pos)) =>
                  option_type_error name "an integer from 0 to 2" value_pos
              | (Integer_Config _, SOME (Attributes_Value _, value_pos)) =>
                  option_type_error name "an integer from 0 to 2" value_pos
              | (Attributes_Config, SOME (Boolean_Value _, value_pos)) =>
                  option_type_error name "an Isabelle attribute list" value_pos
              | (Attributes_Config, SOME (Integer_Value _, value_pos)) =>
                  option_type_error name "an Isabelle attribute list" value_pos)
         in Symtab.update (name, (checked_value, name_pos)) options end)

fun configured_flag lthy options name config =
  (case Symtab.lookup options name of
     SOME (Boolean_Value enabled, _) => enabled
   | SOME (Integer_Value _, _) =>
       error ("internal non-Boolean uRust command option " ^ quote name)
   | SOME (Attributes_Value _, _) =>
       error ("internal non-Boolean uRust command option " ^ quote name)
   | NONE => Config.get lthy config)

fun configured_integer lthy options name config =
  (case Symtab.lookup options name of
     SOME (Integer_Value level, _) => level
   | SOME (Boolean_Value _, _) =>
       error
         ("internal non-integer uRust command option " ^ quote name)
   | SOME (Attributes_Value _, _) =>
       error
         ("internal non-integer uRust command option " ^ quote name)
   | NONE => validate_verbosity name Position.none (Config.get lthy config))

fun configured_verbosity lthy options =
  configured_integer lthy options verbosity_option urust_verbosity

fun command_label Expression = "urust_expr"
  | command_label Function = "urust_fn"

fun complete_terminal_function_body Function declared_type =
      let
        val (parameter_types, result_type) =
          Term.strip_type declared_type
      in
        if result_type = dummyT
        then
          parameter_types --->
            Type
              (\<^type_name>\<open>function_body\<close>,
               replicate 5 dummyT)
        else declared_type
      end
  | complete_terminal_function_body Expression declared_type =
      declared_type

fun read_declared_type lthy kind (raw_type, type_pos) =
  (case Exn.result
      (fn () =>
        Syntax.parse_typ lthy raw_type
        |> complete_terminal_function_body kind
        |> Syntax.check_typ lthy) () of
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

fun first_differing_token_index left right =
  let
    fun first index [] [] = index
      | first index [] (_ :: _) = index
      | first index (_ :: _) [] = index
      | first index (left_token :: left_tokens)
          (right_token :: right_tokens) =
          if left_token = right_token
          then first (index + 1) left_tokens right_tokens
          else index
  in first 0 left right end

fun pretty_roundtrip ctxt source ast =
  let
    val original_tokens =
      URust_Printer.tokens_of_expr
        URust_Printer.serialized_options ast
    val generated =
      URust_Printer.string_of_expr
        URust_Printer.serialized_options ast
    fun mismatch index detail =
      error
        ("uRust pretty-printer roundtrip mismatch" ^
          Position.here (Input.pos_of source) ^ "\n" ^
          "generated source:\n" ^ generated ^ "\n" ^
          "first differing token index: " ^ string_of_int index ^
          (if detail = "" then "" else "\n" ^ detail))
    val reparsed =
      (case Exn.capture
          (URust_Parser.parse_source ctxt)
          (Parser_Lex_Util.text_source generated) of
         Exn.Res (SOME reparsed) => reparsed
       | Exn.Res NONE =>
           mismatch 0 "generated source reparsed as empty input"
       | Exn.Exn exn =>
           mismatch 0
             ("generated source failed to parse: " ^
               Runtime.exn_message exn))
    val reparsed_tokens =
      URust_Printer.tokens_of_expr
        URust_Printer.serialized_options reparsed
  in
    if original_tokens = reparsed_tokens then ()
    else
      mismatch
        (first_differing_token_index original_tokens reparsed_tokens) ""
  end

fun function_pretty_roundtrip ctxt source function =
  let
    val original_tokens =
      URust_Printer.tokens_of_function
        URust_Printer.serialized_options function
    val generated =
      URust_Printer.string_of_function
        URust_Printer.serialized_options function
    fun mismatch index detail =
      error
        ("uRust function pretty-printer roundtrip mismatch" ^
          Position.here (Input.pos_of source) ^ "\n" ^
          "generated source:\n" ^ generated ^ "\n" ^
          "first differing token index: " ^ string_of_int index ^
          (if detail = "" then "" else "\n" ^ detail))
    val reparsed =
      (case Exn.capture
          (URust_Parser.parse_function_source ctxt)
          (Parser_Lex_Util.text_source generated) of
         Exn.Res (SOME reparsed) => reparsed
       | Exn.Res NONE =>
           mismatch 0 "generated source reparsed as empty input"
       | Exn.Exn exn =>
           mismatch 0
             ("generated source failed to parse: " ^
               Runtime.exn_message exn))
    val reparsed_tokens =
      URust_Printer.tokens_of_function
        URust_Printer.serialized_options reparsed
  in
    if original_tokens = reparsed_tokens then ()
    else
      mismatch
        (first_differing_token_index original_tokens reparsed_tokens) ""
  end

type elaborated =
  {ast: URust_AST.ur_expr,
   term: term}

fun prepare_declaration lthy
    kind source arguments_pos arguments raw_declared_type =
  let
    val declared_type =
      Option.map (read_declared_type lthy kind) raw_declared_type
    val arguments_with_types =
      prepare_arguments kind source arguments_pos arguments declared_type
  in
    (declared_type, arguments_with_types)
  end

fun elaborate_prepared_ast lthy
    {kind, source, declared_type, arguments_with_types, ast} : elaborated =
  let
    val (((closed, field_reports), function_reports),
          navigation_reports) =
      Navigation.capture (fn () =>
        URust_Item_Scope.capture_function_reports (fn () =>
          URust_Item_Scope.capture_field_reports (fn () =>
            let
              val unchecked =
                lower kind lthy arguments_with_types ast
              val checked =
                let
                  val constrained =
                    (case declared_type of
                       SOME (complete_type, _) =>
                         Type.constraint complete_type unchecked
                     | NONE => unchecked)
                in
                  Syntax.check_term lthy constrained
                end
              val closed =
                (case declared_type of
                   SOME (_, type_pos) =>
                     close_typed_term kind lthy type_pos checked
                 | NONE => checked)
              val _ =
                reject_unresolved kind lthy source closed
            in
              closed
            end)))
    val _ =
      URust_Item_Scope.replay_field_reports
        lthy field_reports
    val _ =
      URust_Item_Scope.replay_function_reports
        lthy function_reports
    val _ =
      Navigation.replay lthy navigation_reports
  in
    {ast = ast, term = closed}
  end

fun elaborate_ast lthy
    {kind, source, arguments, arguments_pos,
     declared_type = raw_declared_type, ast} : elaborated =
  let
    val (declared_type, arguments_with_types) =
      prepare_declaration lthy
        kind source arguments_pos arguments raw_declared_type
  in
    elaborate_prepared_ast lthy
      {kind = kind,
       source = source,
       declared_type = declared_type,
       arguments_with_types = arguments_with_types,
       ast = ast}
  end

fun elaborate_result pp_test lthy
    {kind, source, arguments, arguments_pos, declared_type} : elaborated =
  let
    val (prepared_type, arguments_with_types) =
      prepare_declaration lthy
        kind source arguments_pos arguments declared_type
    val ast =
      (case URust_Parser.parse_source lthy source of
         SOME expression => expression
       | NONE =>
           error
             (empty_source_message kind ^
               Position.here (Input.pos_of source)))
    val _ =
      if pp_test then pretty_roundtrip lthy source ast else ()
  in
    elaborate_prepared_ast lthy
      {kind = kind,
       source = source,
       declared_type = prepared_type,
       arguments_with_types = arguments_with_types,
       ast = ast}
  end

fun elaborate lthy
    args =
  #term (elaborate_result (Config.get lthy urust_pp_test) lthy args)

datatype declaration_result =
    Definition_Result of
      {lhs: term, display_lhs: term,
       fact_name: string, theorem: thm,
       pretty_arguments: string list,
       pretty_body: Pretty.T option}
  | Abbreviation_Result of
      {lhs: term, rhs: term, name: string,
       pretty_arguments: string list,
       pretty_body: Pretty.T option}
  | Anonymous_Result of
      {term: term, name: string, kind: elaboration_kind,
       pretty_arguments: string list,
       pretty_body: Pretty.T option}

datatype declaration_target =
    Named_Target of Binding.binding
  | Anonymous_Target of Position.T

fun declaration_attributes lthy command target abbreviation options =
  (case Symtab.lookup options attributes_option of
     NONE => []
   | SOME (Attributes_Value attributes, option_pos) =>
       (case target of
          Anonymous_Target _ =>
            error
              (command ^
                ": attrs is not supported for anonymous declarations" ^
                Position.here option_pos)
        | Named_Target _ =>
            if abbreviation
            then
              error
                (command ^
                  ": attrs is not supported in abbreviation mode" ^
                  Position.here option_pos)
            else map (Attrib.check_src lthy) attributes)
   | SOME (_, option_pos) =>
       error
         ("internal non-attribute uRust command option " ^
           quote attributes_option ^ Position.here option_pos))

fun anonymous_binding kind pos =
  Binding.make
    (command_label kind ^ "_anonymous_" ^ string_of_int (serial ()),
     pos)

fun target_binding _ (Named_Target binding) = binding
  | target_binding kind (Anonymous_Target pos) =
      anonymous_binding kind pos

fun declaration_name fallback lhs =
  (case Term.head_of lhs of
     Const (name, _) => name
   | Free (name, _) => name
   | _ => fallback)

fun install_urust_result abbreviation application_definition
    attributes binding arguments pretty_body term lthy =
  let
    val name = Binding.name_of binding
    (* Keep declaration installation silent even when show_results is enabled; the cumulative
       urust_verbosity levels below are the sole result-output policy. *)
    val show_results = Config.get lthy Proof_Display.show_results
    val silent_lthy = Config.put Proof_Display.show_results false lthy
    val definition_parameters =
      Term.add_frees term []
      |> filter_out (Variable.is_fixed lthy o #1)
      |> rev
      |> map Free
    val (definition_arguments, definition_rhs) =
      if application_definition
      then Term.strip_abs_eta (length arguments) term
      else ([], term)
    val display_arguments =
      if application_definition then
        map2
          (fn (source_name, _) => fn (_, T) => Free (source_name, T))
          arguments definition_arguments
      else []
    val definition_lhs =
      list_comb
        (Free
          (name,
           map fastype_of definition_parameters --->
             fastype_of term),
         definition_parameters @ map Free definition_arguments)
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
          {lhs = lhs, rhs = rhs, name = full_name,
           pretty_arguments = map #1 arguments,
           pretty_body = pretty_body},
         Config.put Proof_Display.show_results show_results lthy')
      end
    else
      let
        val ((defined_lhs, (fact_name, theorem)), lthy') =
          Specification.definition
            (SOME (binding, NONE, NoSyn)) [] []
            ((Thm.def_binding binding, attributes),
              Logic.mk_equals (definition_lhs, definition_rhs)) silent_lthy
        val lhs = list_comb (defined_lhs, definition_parameters)
        val display_lhs =
          list_comb
            (defined_lhs,
             definition_parameters @ display_arguments)
      in
        (Definition_Result
          {lhs = lhs, display_lhs = display_lhs,
           fact_name = fact_name, theorem = theorem,
           pretty_arguments =
             if application_definition then [] else map #1 arguments,
           pretty_body = pretty_body},
         Config.put Proof_Display.show_results show_results lthy')
      end
  end

fun declare_urust_result pp_test render_pretty
    abbreviation application_definition attributes binding kind
    (target, declared_type, source, arguments_pos, arguments) lthy =
  let
    val {ast, term} =
      elaborate_result pp_test lthy
        {kind = kind,
         source = source,
         arguments = arguments,
         arguments_pos = arguments_pos,
         declared_type = declared_type}
    val pretty_body =
      if render_pretty then
        let
          fun reparse pretty_source =
            ignore
              (elaborate_result false lthy
                {kind = kind,
                 source = pretty_source,
                 arguments = arguments,
                 arguments_pos = arguments_pos,
                 declared_type = declared_type})
        in
          SOME
            (URust_Printer_Output.pretty_human_expr_with_reparse
              reparse ast)
        end
      else NONE
  in
    (case target of
       Named_Target _ =>
         install_urust_result abbreviation application_definition attributes binding
           arguments pretty_body term lthy
     | Anonymous_Target _ =>
         (Anonymous_Result
            {term = term,
             name = Local_Theory.full_name lthy binding,
             kind = kind,
             pretty_arguments = map #1 arguments,
             pretty_body = pretty_body},
          lthy))
  end

fun function_parameter_argument parameter =
  let
    val URust_AST.Function_Parameter
      (mutable_pos, pattern, _, _) = parameter
    fun unsupported pos =
      error
        ("urust_fn: unsupported function parameter pattern" ^
          Position.here pos)
  in
    (case (mutable_pos, pattern) of
       (NONE, URust_AST.P_Wild pos) => ("_", pos)
     | (SOME pos, URust_AST.P_Wild _) => unsupported pos
     | (_, URust_AST.P_Ident ("self", pos)) =>
         error
           ("urust_fn: receiver parameters are not supported" ^
             Position.here pos)
     | (_, URust_AST.P_Ident (name, pos)) => (name, pos)
     | (SOME pos, _) => unsupported pos
     | (NONE, _) =>
         unsupported (URust_AST.pattern_position pattern))
  end

fun function_arguments function =
  map function_parameter_argument
    (URust_AST.function_parameters function)

fun source_subrange source range =
  let
    val source_start =
      the (Position.offset_of (Input.pos_of source))
    val range_start =
      the (Position.offset_of range)
    val range_stop =
      the (Position.end_offset_of range)
    val symbols = Symbol.explode (Input.string_of source)
    val left = range_start - source_start
    val count = range_stop - range_start
    val _ =
      if 0 <= left andalso 0 <= count andalso
          left + count <= length symbols
      then ()
      else error "urust_fn: internal function body source range mismatch"
    val text =
      symbols |> drop left |> take count |> String.concat
    val start = range
    val stop = Parser_Lex_Util.exclusive_end range
  in
    Input.source true text (Position.range (start, stop))
  end

fun function_body_source source function =
  source_subrange source
    (URust_AST.expression_position
      (URust_AST.function_body function))

fun function_arguments_position function =
  (case
      URust_AST.source_token_positions
        (URust_AST.function_source_layout function)
        (URust_AST.Delimiter_Token ")") of
     pos :: _ => pos
   | [] => URust_AST.function_item_position function)

fun elaborate_function_item pp_test lthy
    source raw_type function =
  let
    val arguments = function_arguments function
    val body_source = function_body_source source function
    val _ =
      if pp_test
      then function_pretty_roundtrip lthy source function
      else ()
    val {term, ...} =
      elaborate_ast lthy
        {kind = Function,
         source = body_source,
         arguments = arguments,
         arguments_pos = function_arguments_position function,
         declared_type = SOME raw_type,
         ast = URust_AST.function_body function}
  in
    {term = term,
     arguments = arguments,
     body_source = body_source}
  end

fun declaration_registered_term
      (Definition_Result {lhs, ...}) = lhs
  | declaration_registered_term
      (Abbreviation_Result {lhs, ...}) = lhs
  | declaration_registered_term
      (Anonymous_Result {term, ...}) = term

fun reject_function_item_conflict lthy (rust_name, rust_pos) =
  if is_some (URust_Item_Scope.lookup_function lthy rust_name)
  then
    error
      ("urust_fn: Rust function path " ^ quote rust_name ^
        " is already owned by a Rust function item" ^
        Position.here rust_pos)
  else if is_some
      (URust_Item_Scope.lookup_constructor lthy rust_name)
  then
    error
      ("urust_fn: Rust function path " ^ quote rust_name ^
        " is already owned by a Rust constructor item" ^
        Position.here rust_pos)
  else if not
      (null
        (Micro_Rust_Names.lookups
          lthy Micro_Rust_Names.NFunction rust_name))
  then
    error
      ("urust_fn: Rust function path " ^ quote rust_name ^
        " conflicts with an existing micro_rust_notation (call) declaration" ^
        Position.here rust_pos)
  else ()

fun register_function_result target (rust_name, rust_pos)
    declaration lthy =
  (case target of
     Anonymous_Target _ => lthy
   | Named_Target _ =>
       URust_Item_Scope.register_function
         {rust_name = rust_name,
          rust_pos = rust_pos,
          function = declaration_registered_term declaration}
         lthy)

fun declare_urust_function_result pp_test render_pretty
    abbreviation application_definition attributes binding
    target raw_type source function lthy =
  let
    val {term, arguments, ...} =
      elaborate_function_item pp_test lthy
        source raw_type function
    val pretty_body =
      if render_pretty then
        let
          fun reparse pretty_source =
            (case URust_Parser.parse_function_source lthy pretty_source of
               SOME pretty_function =>
                 ignore
                   (elaborate_function_item false lthy
                     pretty_source raw_type pretty_function)
             | NONE =>
                 error "urust_fn: pretty function reparsed as empty input")
        in
          SOME
            (URust_Printer_Output.pretty_human_function_with_reparse
              reparse function)
        end
      else NONE
    val (declaration, lthy') =
      (case target of
         Named_Target _ =>
           install_urust_result abbreviation application_definition
             attributes binding arguments pretty_body term lthy
       | Anonymous_Target _ =>
           (Anonymous_Result
              {term = term,
               name = Local_Theory.full_name lthy binding,
               kind = Function,
               pretty_arguments = [],
               pretty_body = pretty_body},
            lthy))
    val lthy'' =
      register_function_result target
        (URust_AST.function_name function) declaration lthy'
  in
    (declaration, lthy'')
  end
fun verbosity_output_enabled interactive lthy =
  interactive orelse Config.get lthy Proof_Display.show_results

fun pretty_generated_result kind name lthy thms =
  Pretty.block1
    [Pretty.block
       [Pretty.mark_position (Position.thread_data ())
          (Pretty.keyword1 kind),
        Pretty.brk 1,
        Pretty.str (Long_Name.base_name name),
        Pretty.str ":"],
     Pretty.fbrk,
     Proof_Context.pretty_fact lthy ("", thms)]

fun print_generated_result interactive verbosity minimum kind lthy (name, thms) =
  if verbosity >= minimum andalso
      verbosity_output_enabled interactive lthy
  then Pretty.writeln (pretty_generated_result kind name lthy thms)
  else ()

fun print_abbreviation interactive verbosity lthy name lhs rhs =
  if verbosity >= 1 andalso
     verbosity_output_enabled interactive lthy
  then
    Pretty.writeln
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
     verbosity_output_enabled interactive lthy
  then
    Pretty.writeln
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

fun pretty_declaration_heading kind name =
  Pretty.block
    [Pretty.mark_position (Position.thread_data ())
       (Pretty.keyword1 kind),
     Pretty.brk 1,
     Pretty.str (Long_Name.base_name name),
     Pretty.str ":"]

fun the_pretty_body (SOME pretty) = pretty
  | the_pretty_body NONE =
      error "uRust command: internal missing pretty-print body"

val symbolic_urust_open =
  Pretty.block
    [Pretty.mark_str (Markup.keyword1, "\<mu>"),
     Pretty.mark_str (Markup.delimiter, Symbol.open_)]

val symbolic_urust_close =
  Pretty.mark_str (Markup.delimiter, Symbol.close)

fun pretty_urust_formals arguments =
  Pretty.block
    ([Pretty.mark_str (Markup.operator, "|")] @
     Pretty.commas
       (map (Pretty.mark_str o pair Markup.bound) arguments) @
     [Pretty.mark_str (Markup.operator, "|")])

fun pretty_urust_lines opening arguments pretty_body =
  let
    val pretty = the_pretty_body pretty_body
    val contents =
      if null arguments
      then [Pretty.indent 2 pretty]
      else
        [Pretty.indent 2 (pretty_urust_formals arguments),
         Pretty.indent 4 pretty]
  in
    Pretty.chunks (opening :: contents @ [symbolic_urust_close])
  end

fun pretty_urust_equation lthy lhs pretty_arguments pretty_body =
  let
    val opening =
      Pretty.block1
        [Syntax.pretty_term
           (Config.put Proof_Context.show_abbrevs false lthy)
           lhs,
         Pretty.brk 1,
         Pretty.str "\<equiv>",
         Pretty.str " ",
         symbolic_urust_open]
  in
    pretty_urust_lines opening pretty_arguments pretty_body
  end

fun pretty_urust_declaration lthy declaration =
  (case declaration of
     Definition_Result
       {fact_name, display_lhs, pretty_arguments, pretty_body, ...} =>
       Pretty.chunks
         [pretty_declaration_heading "definition" fact_name,
          pretty_urust_equation lthy display_lhs
            pretty_arguments pretty_body]
   | Abbreviation_Result
       {lhs, name, pretty_arguments, pretty_body, ...} =>
       Pretty.chunks
         [pretty_declaration_heading "abbreviation" name,
          pretty_urust_equation lthy lhs
            pretty_arguments pretty_body]
   | Anonymous_Result
       {name, kind, pretty_arguments, pretty_body, ...} =>
       Pretty.chunks
       [pretty_declaration_heading (command_label kind) name,
        pretty_urust_lines symbolic_urust_open
          pretty_arguments pretty_body])

fun print_pretty_declaration interactive verbosity lthy declaration =
  if verbosity >= 1 andalso
     verbosity_output_enabled interactive lthy
  then Pretty.writeln (pretty_urust_declaration lthy declaration)
  else ()

fun print_declaration interactive verbosity pretty lthy declaration =
  if pretty then
    print_pretty_declaration interactive verbosity lthy declaration
  else
  (case declaration of
     Definition_Result {fact_name, theorem, ...} =>
       print_generated_result interactive verbosity 1 "definition" lthy
         (fact_name, [theorem])
   | Abbreviation_Result {lhs, rhs, name, ...} =>
       print_abbreviation interactive verbosity lthy name lhs rhs
   | Anonymous_Result {term, name, kind, ...} =>
       print_anonymous interactive verbosity lthy kind name term)

fun declare_and_print declaration interactive verbosity pretty lthy =
  let
    val (result, lthy') = declaration lthy
    val _ = print_declaration interactive verbosity pretty lthy' result
  in lthy' end

fun warn_ineffective_pretty options source pretty verbosity =
  if pretty andalso verbosity = 0 then
    let
      val pos =
        (case Symtab.lookup options pretty_option of
           SOME (_, option_pos) => option_pos
         | NONE => Input.pos_of source)
    in
      warning
        ("uRust command option " ^ quote pretty_option ^
          " has no effect when verbosity = 0" ^
          Position.here pos)
    end
  else ()
fun command_elaboration_kind lthy declared_type =
  (case declared_type of
     NONE => Expression
   | SOME raw_type =>
       if is_function_body_type
           (terminal_type (#1 (read_declared_type lthy Expression raw_type)))
       then Function
       else Expression)

fun reject_abbreviation_application_definition command
    abbreviation application_definition =
  if abbreviation andalso application_definition
  then
    error
      (command ^
        ": abbreviation mode cannot be combined with `application_def`")
  else ()

fun define_urust_expr
    (options,
     args as (target, declared_type, source, _, _)) interactive lthy =
  let
    val pp_test =
      configured_flag lthy options pp_test_option urust_pp_test
    val verbosity = configured_verbosity lthy options
    val pretty =
      configured_flag lthy options pretty_option urust_pretty
    val _ = warn_ineffective_pretty options source pretty verbosity
    val render_pretty =
      pretty andalso verbosity >= 1 andalso
        verbosity_output_enabled interactive lthy
    val abbreviation =
      configured_flag lthy options abbrev_option urust_abbrev
    val application_definition =
      configured_flag lthy options application_def_option
        urust_application_def
    val _ =
      reject_abbreviation_application_definition
        "urust_expr" abbreviation application_definition
    val attributes =
      declaration_attributes lthy "urust_expr" target abbreviation options
    val kind = command_elaboration_kind lthy declared_type
    val binding = target_binding kind target
    fun declaration lthy' =
      declare_urust_result pp_test render_pretty
        abbreviation application_definition
        attributes binding kind args lthy'
  in
    declare_and_print declaration interactive verbosity pretty lthy
  end

fun define_legacy_urust_fn
    (options,
     (target, declared_type, body, parameters_pos, parameters)) interactive lthy =
  let
    val pp_test =
      configured_flag lthy options pp_test_option urust_pp_test
    val verbosity = configured_verbosity lthy options
    val pretty =
      configured_flag lthy options pretty_option urust_pretty
    val _ = warn_ineffective_pretty options body pretty verbosity
    val render_pretty =
      pretty andalso verbosity >= 1 andalso
        verbosity_output_enabled interactive lthy
    val abbreviation =
      configured_flag lthy options abbrev_option urust_abbrev
    val application_definition =
      configured_flag lthy options application_def_option
        urust_application_def
    val _ =
      reject_abbreviation_application_definition
        "urust_fn" abbreviation application_definition
    val attributes =
      declaration_attributes lthy "urust_fn" target abbreviation options
    val raw_type = require_function_type body declared_type
    val binding = target_binding Function target
    fun declaration lthy' =
      declare_urust_result pp_test render_pretty
        abbreviation application_definition attributes binding Function
        (target, SOME raw_type, body, parameters_pos, parameters) lthy'
  in
    declare_and_print declaration interactive verbosity pretty lthy
  end

fun define_rust_item_urust_fn
    (options, (target_option, declared_type, source))
    interactive lthy =
  let
    val function =
      (case URust_Parser.parse_function_source lthy source of
         SOME function => function
       | NONE =>
           error
             ("urust_fn: empty function item" ^
               Position.here (Input.pos_of source)))
    val (rust_name, rust_pos) =
      URust_AST.function_name function
    val target =
      (case target_option of
         SOME target => target
       | NONE =>
           Named_Target
             (Binding.make
               (URust_AST.rust_snake_case rust_name, rust_pos)))
    val _ =
      (case target of
         Named_Target _ =>
           reject_function_item_conflict lthy (rust_name, rust_pos)
       | Anonymous_Target _ => ())
    val raw_type = require_function_type source declared_type
    val pp_test =
      configured_flag lthy options pp_test_option urust_pp_test
    val verbosity = configured_verbosity lthy options
    val pretty =
      configured_flag lthy options pretty_option urust_pretty
    val _ = warn_ineffective_pretty options source pretty verbosity
    val render_pretty =
      pretty andalso verbosity >= 1 andalso
        verbosity_output_enabled interactive lthy
    val abbreviation =
      configured_flag lthy options abbrev_option urust_abbrev
    val application_definition =
      configured_flag lthy options application_def_option
        urust_application_def
    val _ =
      reject_abbreviation_application_definition
        "urust_fn" abbreviation application_definition
    val attributes =
      declaration_attributes lthy "urust_fn" target abbreviation options
    val binding = target_binding Function target
    fun declaration lthy' =
      declare_urust_function_result pp_test render_pretty
        abbreviation application_definition attributes binding
        target raw_type source function lthy'
  in
    declare_and_print declaration interactive verbosity pretty lthy
  end

fun define_urust_fn
    (options,
     (target_option, declared_type, source, parameter_clause)) interactive lthy =
  (case parameter_clause of
     SOME (parameters_pos, parameters) =>
       let
         val target =
           (case target_option of
              SOME target => target
            | NONE =>
                error
                  ("urust_fn: legacy body syntax requires an explicit HOL declaration target" ^
                    Position.here (Input.pos_of source)))
       in
         define_legacy_urust_fn
           (options,
            (target, declared_type, source,
             parameters_pos, parameters))
           interactive lthy
       end
   | NONE =>
       define_rust_item_urust_fn
         (options, (target_option, declared_type, source))
         interactive lthy)

fun define_urust_datatype
    ((options, explicit_binding), source) interactive lthy =
  let
    val verbosity = configured_verbosity lthy options
    val pp_test =
      configured_flag lthy options pp_test_option urust_pp_test
    val pretty =
      configured_flag lthy options pretty_option urust_pretty
    val _ =
      warn_ineffective_pretty options source pretty verbosity
  in
    URust_Datatype.define
      {source = source,
       explicit_binding = explicit_binding,
       interactive = interactive,
       verbosity = verbosity,
       pp_test = pp_test,
       pretty = pretty}
      lthy
  end

val parse_option_value =
  Parse.position Parse.attribs >>
    (fn (attributes, pos) => (Attributes_Value attributes, pos)) ||
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
        (target, declared_type, parameters, source))) >>
  (fn (options, (target, declared_type, parameter_clause, source)) =>
    let
      val (arguments_pos, arguments) =
        (case parameter_clause of
           SOME clause => clause
         | NONE => (#2 (Input.range_of source), []))
    in
      (options,
       (target, declared_type, source, arguments_pos, arguments))
    end)

fun parse_urust_fn_declaration option_configs =
  parse_command_options option_configs --
    (Scan.option parse_declaration_target --
      parse_declared_type --
      Scan.option parse_parameters --
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source) >>
      (fn (((target, declared_type), parameters), source) =>
        (target, declared_type, source, parameters))) >>
  (fn (options, payload) =>
    (options, payload))

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_expr\<close>
    "Declare a uRust expression"
    (parse_urust_declaration expression_option_configs >>
      define_urust_expr)

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_fn\<close>
    "Declare a typed uRust function body or Rust-shaped function item"
    (parse_urust_fn_declaration function_option_configs >>
      define_urust_fn)

val parse_datatype_binding =
  (Parse.position Parse.underscore >>
    (fn (_, pos) =>
      error
        ("urust_datatype: _ is not a datatype naming placeholder" ^
          Position.here pos))) ||
  Parse.binding

val parse_urust_datatype =
  parse_command_options datatype_option_configs --
    Scan.option parse_datatype_binding --
    (Parse.token Parse.cartouche >>
      Parser_Lex_Util.cartouche_source)

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_datatype\<close>
    "Declare a Rust-shaped struct or enum as an Isabelle datatype"
    (parse_urust_datatype >> define_urust_datatype)
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
    let
      val canonical = canonical_name lthy rust_name
      val pos = #2 rust_name
      val _ =
        if is_some
            (URust_Item_Scope.lookup_type lthy canonical) orelse
           is_some
            (URust_Item_Scope.lookup_constructor lthy canonical)
        then
          error
            ("urust_notation: Rust path " ^ quote canonical ^
              " is already owned by urust_datatype" ^
              Position.here pos)
        else if is_some
            (URust_Item_Scope.lookup_function lthy canonical)
        then
          error
            ("urust_notation: Rust path " ^ quote canonical ^
              " is already owned by urust_fn" ^
              Position.here pos)
        else ()
    in
      Micro_Rust_Notation_Cmd.do_register kind_opt
        (hol_src, (canonical, pos)) lthy
    end

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
