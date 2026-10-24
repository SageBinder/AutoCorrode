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
    and "urust_type_alias" :: thy_decl
    and "urust_notation" :: thy_decl
    and "\<rightarrow>"
begin

section\<open> The command \<close>

text\<open>
The expression surface is
\<open>urust_expr [OPTIONS] NAME|_ [:: TYPE] [(ARG|_, ...)] src\<close>.
It infers an untyped expression or accepts a complete declaration type. A terminal
\<open>expression\<close> type produces an ordinary expression abstraction, while a terminal
\<open>function_body\<close> type wraps the body once in \<open>FunctionBody\<close>.

The function surface is
\<open>urust_fn [OPTIONS] [HOL_NAME|_] [:: TYPE] src\<close>, where the cartouche contains one complete
\<open>fn RustName[<'lifetime, ...>](parameter: RustType, ...) [-> RustType] { body }\<close> item.
A declared \<open>TYPE\<close> is the complete curried HOL declaration type, with one argument type per
Rust parameter and a terminal \<open>function_body\<close>, or an exact terminal \<open>_\<close> that infers every
channel. It replaces the Rust signature's types, which are then neither resolved nor checked;
only the parameter count and the lifetime scope rules below still apply. Named variables, sorts,
locale variables and \<open>_\<close> holes follow ordinary HOL type reading, as for \<open>urust_expr\<close>. The
declared type also supplies every channel: it cannot be combined with the channel options below,
and scoped channel defaults do not apply to it.
Without a declared type, the Rust signature is authoritative: parameter and explicit result
types resolve through \<open>urust_type\<close>, including qualified and generic mappings and structural
tuples. The shared type grammar permits \<open>\<tau>\<open>HOL type\<close>\<close> anywhere a type occurs.
Function escapes support polymorphic variables, shared sort constraints, higher-order types and
independent inference holes. Raw pointers and mutable references \<open>&mut T\<close> resolve to the same
\<open>Global_Store.ref\<close> model and share implicit address/global backend parameters across the
complete signature, constrained by its body and expected types. Datatype fields introduce those
backend parameters for raw pointers while continuing to reject unrelated free type variables.
The optional generic list declares only lifetimes. Reference and generic-argument lifetimes,
such as \<open>&'a mut T\<close> and \<open>Cursor<'a, T>\<close>,
must be declared there unless they are \<open>'static\<close> or \<open>'_\<close>; lifetimes are then erased and
never change the definition. Type generics and lifetime bounds are rejected. Literal function-pointer
types, \<open>impl Trait\<close>, lifetime generic arguments, associated type bindings, const-expression
generic arguments, and unexpanded macro type variables are parsed as unresolved syntax. They
require a declared HOL type; the type resolver supplies no interpretation for them.
Shared references \<open>&T\<close> are also rejected without a declared type. An omitted return
means Rust unit, just like explicit \<open>-> ()\<close>. Non-unit results require a return annotation.
The independently optional inline \<open>state\<close>, \<open>abort\<close>, \<open>input\<close> and
\<open>output\<close> options take positioned HOL types and constrain the actual constant's channels.
Input and output are the actual types, including any \<open>prompt\<close> or \<open>prompt_output\<close>
wrappers. Omitted channels infer from the body/signature and generalize when unconstrained.
Named variables and sorts are shared across all channel options and Rust type escapes.
Ambient locale variables remain rigid, and separate \<open>_\<close> holes infer independently.
The scoped attributes \<open>urust_state\<close>, \<open>urust_abort\<close>, \<open>urust_input\<close> and
\<open>urust_output\<close> set a default HOL type for each channel, for example
\<open>context notes [[urust_abort = \<open>bool\<close>]] begin \<dots> end\<close>. A function that omits a
channel option inherits that default, an inline option or \<omega> annotation overrides its own
channel, and an exact \<open>_\<close> default removes it. The attribute checks its source once where it is
declared; every inheriting function rereads that source with its own signature, as if written
inline, so named variables are fresh per function and may be captured by a locale.
Parameters lower identifiers, \<open>_\<close>, and \<open>mut identifier\<close>.
Explicitly typed \<open>self: T\<close> and \<open>mut self: T\<close> use the same signature typing
and lexical binding as other identifiers, including field/method receivers and HOL escapes.
A free function rejects the shorthand receivers \<open>self\<close>, \<open>mut self\<close>, \<open>&self\<close> and
\<open>&mut self\<close>, and \<open>Self\<close> outside an impl member; inside an impl member of a \<open>urust\<close>
chunk the shorthands are their typed spellings and \<open>Self\<close> names the implementing type.
An explicit outer name chooses the HOL binding; otherwise acronym-aware snake case derives it from
the Rust name. An anonymous \<open>_\<close> checks without installing artifacts.
Named functions register their Rust name by default for later direct calls. The Boolean
\<open>register_notation\<close> option, using the shared scoped
\<open>urust_register_notation\<close> configuration, can suppress this entry while retaining the HOL
definition or abbreviation and its native declaration navigation. Inline values override the scoped
setting. Enabled registration is a morphism-aware call notation: distinct backends accumulate and
calls select the unique type-compatible backend. Explicit notation for the same backend is idempotent.
Indistinguishable backends report ambiguity at their use; same-typed locale instances therefore retain
the opt-out workaround. Function/constructor declaration collisions remain rejected in both
registration and theory merge. Mapping references are reported only after successful declaration
completion.

The optional parenthesized, comma-separated expression argument list occurs immediately before the source
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
explicit arguments. Each argument keeps its source spelling, made an Isabelle identifier by
\<open>Name.desymbolize\<close> when necessary (\<open>_tmp\<close> becomes \<open>x_tmp\<close>) and renamed away from context
fixes, the defined name, and free variables of the body. Wildcard slots become \<open>uu\<close>. Both forms
install the same curried constant value, attributes, and code equation. The application form is
useful when existing proofs fold a named
sub-expression, while the default form remains suitable for rewriting a bare function constant.
Pretty output is presentation-only: \<open>urust_fn\<close> displays source parameters on the left-hand side
even for a default curried definition, while \<open>urust_expr\<close> retains source arguments as a uRust
closure on the right. Application definitions also display arguments only on the left.
Zero-argument definitions are identical in either mode. Anonymous declarations retain closure
formals because they have no equation left-hand side. Input abbreviations reject an effective
\<open>application_def = true\<close>; an inline false value may override a true scoped setting.
\<open>urust_pp_test\<close> defaults to false. Its common Boolean inline alias is \<open>pp_test\<close>. When
enabled, the parsed AST is serialized, reparsed without source positions, and compared through the
position-independent serialized token stream before lowering. A successful check is silent. A
mismatch aborts before declaration installation and reports the generated source plus the first
differing token index.

\<open>urust_pretty\<close> defaults to false. Its common Boolean inline alias is \<open>pretty\<close>. At verbosity
level 1, both settings print only a compact declaration heading followed by \<open>...\<close>. At level 2,
false retains the ordinary HOL rendering of generated definitions, abbreviations, and anonymous
results; true instead prints the same declaration heading and left-hand side with the right-hand side
rendered as human-readable uRust inside a symbolic \<open>\<mu>\<open>...\<close>\<close> wrapper. The wrapper is
presentation only and is unrelated to source quotation syntax. At verbosity 0 no result is printed;
an effective \<open>pretty = true\<close> receives a warning because it has no effect.
Named \<open>urust_fn\<close> parameters appear on the left of \<open>\<equiv>\<close>; Rust-shaped function items print
only their body on the right, omitting its outer braces and the Rust name and signature.
Printed function bodies are prefixed by \<open>FunctionBody\<close> before the symbolic uRust wrapper,
distinguishing them from expression declarations.
Other source arguments appear as closure formals on the right unless
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
an integer from 0 to 2 that defaults to 0. Level 0 is quiet; level 1 prints only compact declaration
headings; level 2 prints complete definition statements, abbreviation equations, or anonymous
results. The standard interactive and \<open>show_results\<close> gates still control enabled output.

\<open>urust_datatype\<close> accepts the common scoped/inline \<open>pp_test\<close>, \<open>pretty\<close>, and
\<open>verbosity\<close> options, plus Boolean \<open>register_notation\<close> (default true, scoped
configuration \<open>urust_register_notation\<close>). A bare \<open>[register_notation]\<close> enables it;
explicit true and false values override the scoped setting for that declaration only. False
suppresses automatic field-lens aliases for named structs while retaining the datatype, lenses and
their proofs, constructor paths, source-field metadata, and type mappings. Existing aliases remain
installed; the setting affects subsequent declarations only. Unit/tuple structs and enums accept
the option but do not generate field-lens aliases. A generated lens can be registered later with,
for example, \<open>urust_notation (field) packet_packet_sample_value_lens ("sampleValue")\<close>.
The inline-only structured option \<open>hol_names = ["source" \<rightarrow> \<open>HOL\<close>]\<close>
chooses named-struct selector basenames, enum constructor basenames, or enum payload selector
basenames. Keys are quoted strings and targets are cartouches. Struct keys are unqualified source
field names. Enum keys are source variant names, which rename only constructors, or payload keys
\<open>"Variant.field"\<close> and \<open>"Variant.N"\<close> with the source variant name and a named
field or 0-based decimal tuple index. A positional key adds a selector for that field on the HOL
and custom enum backends; tuple structs have no keys. Targets are used as written, subject to
native binding rules. Missing entries and an empty list retain the defaults. Duplicate keys, unknown variants, fields or
indices, invalid bindings, and duplicate effective names (including untouched defaults) are
positioned errors. Every name uRust chooses for the declaration (a target, an unprefixed name, an
untouched constructor or an untouched default selector) must also differ from the other
per-constructor and per-field names it generates: constructors, automatic Ctr_Sugar
\<open>un_\<close> selectors and \<open>is_\<close> discriminators, other selectors, and record
constructors and updates. A conflict is reported at the chosen name, or at the later of two
chosen names. Coinciding automatic Ctr_Sugar names keep their native behaviour, and per-type
names are outside the check. Field lenses follow the actual selector names; Rust aliases and
paths always retain their source spellings. The outer HOL type binding is independent, and struct
constructors remain automatic. Automatic named-struct selectors are prefixed by the HOL type
name and automatic named enum payload selectors by the type and snake-case variant names. The
inline-only Boolean \<open>[unprefixed_selectors]\<close>, canonically bare, names both after the
snake-case field alone; explicit and payload keys still override it. It has no attribute or
scoped setting, and the \<open>simple_word_enum\<close> backend, which generates no selectors,
rejects it.
Type/const parameters retain source order, including unused parameters. Const parameters use
HOL length types, initially \<open>len0\<close> and strengthened where fields require \<open>len\<close>.
The option \<open>hol_type_parameters = ["T" \<rightarrow> \<open>'a::address_type\<close>]\<close> supplies local
HOL names/sorts, with the same quoted keys and cartouche targets.
Unused type parameters are retained independently of fields. Automatic \<open>PhantomData\<close> field
handling is deferred; ordinary explicit HOL definitions and manual type/notation mappings remain
available, with all mapped fields stored and required.
The default \<open>backend = auto\<close> chooses the custom enum for ordinary enums and the word backend
for explicit unsigned representations without payload. Use \<open>backend = hol\<close> for native
BNF artifacts, or quoted \<open>backend = "enum"\<close> / \<open>backend = "simple_word_enum"\<close> to protect
Isabelle command keywords. \<open>word_width = N\<close> must agree with an explicit Rust repr width.
Native plugin filtering uses \<open>plugins = (plugins only: word_conversion)\<close>.
It accepts an optional HOL binding followed by one required source
cartouche containing a complete Rust-shaped struct or enum item. Nominal and primitive field types
resolve only through context-local \<open>urust_type\<close> declarations; qualified and generic mappings use
ordered placeholders that exactly match the HOL template's free type variables. Rust tuples are
encoded structurally as right-nested products ending in \<open>tnil\<close>. The explicit
\<open>\<tau>\<open>TYPE\<close>\<close> form is the only registry bypass. An omitted binding is inferred with
acronym-aware ASCII snake case. Successful structs and enums register their Rust names for later
datatype fields. Level 0 is quiet;
level 1 reports the completed public type, constructors, selectors, lenses, and exact Rust mappings;
level 2 adds the normalized generated HOL declaration and complete public selector/lens definitions.
With \<open>pretty = true\<close>, levels 1 and 2 additionally show the normalized human-readable uRust
declaration after the manifest. Its markup is replayed against the completed generated artifacts
without generating or registering anything again. Generation and item-scope registration run
silently and atomically before any result report. Datatype \<open>pp_test\<close> runs before generation.

The command \<open>urust_type_alias ["QUALIFIED_PATH"] src\<close> accepts one complete Rust type
item such as \<open>type Width = u16;\<close>, \<open>type Pair<T> = (T, T);\<close>, or
\<open>type Ptr<T> = *const T;\<close>. Its optional quoted path must end with the item name.
Aliases are ordinary local-theory declarations, available immediately and inherited through theory
imports. They share the type-mapping namespace, capture dependencies at declaration time and retain
inferred generic sorts. Signatures, datatype fields and cast targets all expand them.
Semantic declaration and dependency navigation reports wait until successful installation.

The source-ordered chunk command \<open>urust\<close> is registered by the opt-in theory
\<open>Parser_Impl_Chunk\<close>, so importing this theory keeps \<open>urust\<close> an ordinary name. It uses
the option schemas, annotation reader and prepare/declare operations exported here, which the
single-item commands share. Impl blocks are prepared here too: each member is a function
declaration whose registration key is its associated path \<open>T::f\<close>, owned as an associated
function of the impl's Self type, with an additional method-only entry \<open>f\<close> when its first
parameter is a \<open>self\<close> receiver. Members elaborate in a context that carries the impl's Self
type, and at verbosity 1 and 2 each member's registrations follow its declaration output. Preparation is pure; declaration runs native backends in invisible
contexts inside the caller's report transaction and regenerates the authored definition entities
afterwards.

Rust use items in chunks and bodies accept complete declarations, such as
\<open>use demo::{increment as inc, Width};\<close> or \<open>use Choice::{self as Selection, Empty};\<close>.
Each alias captures the canonical exact key of a generated item, Rust type mapping or literal/call
notation in its scope. Value, call,
constructor, pattern, type and cast occurrences resolve an alias to that key and its owning
registry; a binding that is unusable in the requested role is rejected without falling back.
Like Rust module-level imports, chunk aliases are shadowed by lexical locals and parameters.
Use statements in bodies follow Rust block scope and are prepared by expression translation:
they shadow same-named locals and parameters bound outside their block.
Aliases never survive their chunk or block. The whole batch validates before any binding is
prepared, and its reports wait until success.

The option parser is parameterized by a command-specific schema. Both commands accept Boolean
\<open>pp_test\<close>, \<open>pretty\<close>, \<open>application_def\<close>, and \<open>abbrev\<close>, integer
\<open>verbosity\<close>, and attribute-list \<open>attrs\<close>. The configuration-backed short names are
inline-only aliases for the globally prefixed configurations. Options may appear in any order. For
Boolean options, omitting \<open>= true\<close> enables the option, so both commands accept
\<open>[pp_test]\<close>, \<open>[pretty]\<close>, \<open>[application_def]\<close>, and \<open>[abbrev]\<close>. Explicit
\<open>= true\<close> and \<open>= false\<close> remain available; integer and attribute-list options always require a
value. Function declarations additionally accept Boolean \<open>register_notation\<close>,
including its bare enabling spelling, and the HOL type options \<open>state\<close>, \<open>abort\<close>,
\<open>input\<close> and \<open>output\<close>, which override the scoped defaults \<open>urust_state\<close>,
\<open>urust_abort\<close>, \<open>urust_input\<close> and \<open>urust_output\<close>. A declared \<open>:: TYPE\<close> is a
command argument rather than an option, so \<open>urust\<close> chunk members cannot declare one.

An argument-taking abbreviation declaration exposes a parser expression or function body as a HOL
helper. At HOL use sites, write \<open>(helper args)\<close> when surrounding syntax would otherwise group the
helper application incorrectly.
\<close>

ML\<open>
signature URUST_COMMAND =
sig
  datatype elaboration_kind = Expression | Function

  val urust_pp_test: bool Config.T

  val elaborate:
    local_theory ->
      {kind: elaboration_kind,
       source: Input.source,
       arguments: (string * Position.T) list,
       arguments_pos: Position.T,
       declared_type: (string * Position.T) option} ->
      term

  (* Shared option entries and parsed-item declaration operations for item-list commands. *)
  type command_options
  datatype option_schema =
    Chunk_Defaults | Function_Annotation | Datatype_Annotation | Impl_Annotation |
    Impl_Member_Annotation
  val parse_options: option_schema -> command_options parser
  val read_annotation_options:
    Proof.context -> option_schema -> URust_AST.item_annotation -> command_options
  val override_options: command_options -> command_options -> command_options
  val configured_pp_test: Proof.context -> command_options -> bool
  type prepared_function
  val prepare_function_item:
    local_theory ->
      {interactive: bool, roundtrip: bool, options: command_options,
       source: Input.source, function: URust_AST.urust_function} ->
      prepared_function
  val declare_prepared_function:
    prepared_function -> local_theory -> (unit -> unit) * local_theory
  val prepared_function_registrations: prepared_function -> URust_Imports.registrations
  type prepared_datatype
  val prepare_datatype_item:
    local_theory ->
      {interactive: bool, roundtrip: bool, options: command_options,
       source: Input.source, item: URust_AST.urust_datatype} ->
      prepared_datatype
  val declare_prepared_datatype:
    prepared_datatype -> local_theory -> (unit -> unit) * local_theory
  val prepared_datatype_registrations:
    Proof.context -> prepared_datatype -> URust_Imports.registrations
  type prepared_impl
  val prepare_impl_item:
    local_theory ->
      {interactive: bool, options: command_options, impl: URust_AST.urust_impl} ->
      prepared_impl
  type checked_owner = {name: string, self_type: typ, identity: serial, pos: Position.T}
  val declare_prepared_impl:
    {enter: local_theory -> local_theory, leave: local_theory -> local_theory} ->
      prepared_impl -> local_theory * checked_owner list ->
      (unit -> unit) * (local_theory * checked_owner list)
  val prepared_impl_registrations: prepared_impl -> URust_Imports.registrations
  val prepared_impl_associated_keys: Proof.context -> prepared_impl -> string list
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
   implementation details. Item-list commands use the exported option schemas, annotation reader
   and the prepare/declare operations that the single-item commands also use; preparation is
   pure, and declaration runs inside the caller's report transaction. *)
structure URust_Command :> URUST_COMMAND =
struct
datatype elaboration_kind = Expression | Function
structure Navigation = Micro_Rust_Semantic_Navigation

val urust_pp_test =
  Attrib.setup_config_bool \<^binding>\<open>urust_pp_test\<close> (K false)

val urust_pretty =
  Attrib.setup_config_bool \<^binding>\<open>urust_pretty\<close> (K false)

val urust_verbosity =
  URust_Parser_Config.verbosity

val urust_abbrev =
  Attrib.setup_config_bool \<^binding>\<open>urust_abbrev\<close> (K false)

val urust_application_def =
  Attrib.setup_config_bool \<^binding>\<open>urust_application_def\<close> (K false)

val urust_register_notation =
  Attrib.setup_config_bool \<^binding>\<open>urust_register_notation\<close> (K true)

(* Scoped channel defaults keep the positioned source of their declaration. The attribute checks
   it once in the declaring context; the stored declaration value is reused when the attribute is
   applied again, so a replay neither rechecks nor reports. Each inheriting function rereads the
   source together with its own signature. An exact _ removes the default. *)
structure Channel_Defaults = Generic_Data
(
  type T = Input.source Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun channel_default_declaration ctxt name source =
  let
    val typ =
      (case Exn.result (fn () => Syntax.read_typ ctxt (Syntax.implode_input source)) () of
         Exn.Res typ => typ
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else error (name ^ ": " ^ Runtime.exn_message exn ^ Position.here (Input.pos_of source)))
    val update =
      if typ = dummyT then Symtab.delete_safe name else Symtab.update (name, source)
  in Morphism.entity (K (Channel_Defaults.map update)) end

fun setup_channel_default binding =
  let
    val name = Binding.name_of binding
    val parser =
      Scan.state :|-- (fn context =>
        Scan.lift
          (Parse.$$$ "=" |--
            Args.embedded_declaration
              (channel_default_declaration (Context.proof_of context) name))) >>
      (fn declaration => Thm.declaration_attribute (K (Morphism.form declaration)))
    val _ =
      Theory.setup
        (Attrib.setup binding parser
          "scoped default HOL type for an omitted uRust function channel")
  in name end

val urust_state = setup_channel_default \<^binding>\<open>urust_state\<close>
val urust_abort = setup_channel_default \<^binding>\<open>urust_abort\<close>
val urust_input = setup_channel_default \<^binding>\<open>urust_input\<close>
val urust_output = setup_channel_default \<^binding>\<open>urust_output\<close>

val pp_test_option = "pp_test"
val pretty_option = "pretty"
val verbosity_option = "verbosity"
val abbrev_option = "abbrev"
val application_def_option = "application_def"
val attributes_option = "attrs"
val register_notation_option = "register_notation"
val hol_names_option = "hol_names"
val hol_type_parameters_option = "hol_type_parameters"
val state_option = "state"
val abort_option = "abort"
val input_option = "input"
val output_option = "output"
val name_option = "name"

(* Command configurations:
   - urust_pp_test performs a serialized parse-print-parse token comparison for both commands; its
     inline alias is pp_test.
   - urust_pretty selects human uRust in a symbolic \<mu>\<open>...\<close> wrapper for
     verbosity-controlled declaration right-hand sides; its inline alias is pretty.
   - urust_verbosity is cumulative: 0 prints nothing, 1 prints compact declaration headings, and 2
     prints complete generated definitions, abbreviations, or anonymous results; its inline alias is
     verbosity.
   - urust_abbrev controls input-only abbreviations for both declaration commands; its inline alias
     is abbrev.
   - urust_application_def puts explicit source arguments on the generated definition theorem's
     left-hand side; its inline alias is application_def.
   - attrs is inline-only and carries Isabelle theorem attributes for the generated _def theorem of
     a named definition.
   - urust_register_notation controls function callable entries and datatype field-lens aliases;
     its inline alias is register_notation.
   - hol_names is inline-only and carries positioned source-to-HOL pairs for datatype generation.
   - hol_type_parameters is inline-only and carries positioned source-to-HOL type parameter names
     for datatype generation.
   - state, abort, input and output are positioned HOL channel types for functions. Each falls
     back to the source of its scoped default attribute urust_state, urust_abort, urust_input or
     urust_output, and otherwise remains unconstrained.
   - name is annotation-only and carries a positioned HOL binding for one chunk declaration; the
     function schema also admits _ for a checked declaration without artifacts.
   Verbosity values outside 0..2 are rejected. *)
datatype command_option_value =
    Boolean_Value of bool
  | Integer_Value of int
  | Attributes_Value of Token.src list
  | Renames_Value of URust_Datatype.rename list
  | Type_Value of Input.source
  | Backend_Value of string
  | Plugins_Value of (Proof.context -> Plugin_Name.filter)
  | Name_Value of binding option

datatype command_option_config =
    Boolean_Config of bool Config.T
  | Integer_Config of int Config.T
  | Attributes_Config
  | Renames_Config
  | Type_Config of string
  | Backend_Config
  | Width_Config
  | Plugins_Config
  | Name_Config of {anonymous: bool}

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
val function_option_configs =
  fold Symtab.update
    [(register_notation_option, Boolean_Config urust_register_notation),
     (state_option, Type_Config urust_state), (abort_option, Type_Config urust_abort),
     (input_option, Type_Config urust_input), (output_option, Type_Config urust_output)]
    declaration_option_configs

(* unprefixed_selectors is an inline-only Boolean. Its configuration only gives the schema entry
   its Boolean value type: it is never set up as an attribute, and datatype_declaration reads the
   inline value and its position alone. *)
val unprefixed_selectors_option = "unprefixed_selectors"
val unprefixed_selectors_inline =
  Config.declare_bool (unprefixed_selectors_option, \<^here>) (K false)

val datatype_option_configs =
  Symtab.make
    [(pp_test_option, Boolean_Config urust_pp_test),
     (pretty_option, Boolean_Config urust_pretty),
     (verbosity_option, Integer_Config urust_verbosity),
     (register_notation_option, Boolean_Config urust_register_notation),
     (hol_names_option, Renames_Config),
     (unprefixed_selectors_option, Boolean_Config unprefixed_selectors_inline),
     (hol_type_parameters_option, Renames_Config),
     ("backend", Backend_Config),
     ("word_width", Width_Config),
     ("plugins", Plugins_Config)]

(* A chunk's outer list shares only the options meaningful for every declaration kind. Annotation
   schemas extend the single-item schemas by the command-layer HOL binding. *)
val chunk_option_configs =
  Symtab.make
    [(pp_test_option, Boolean_Config urust_pp_test),
     (pretty_option, Boolean_Config urust_pretty),
     (verbosity_option, Integer_Config urust_verbosity),
     (register_notation_option, Boolean_Config urust_register_notation)]

val function_annotation_configs =
  Symtab.update (name_option, Name_Config {anonymous = true}) function_option_configs

val datatype_annotation_configs =
  Symtab.update (name_option, Name_Config {anonymous = false}) datatype_option_configs

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

val rename_list_expectation = "a rename list of \"key\" \<rightarrow> \<open>HOL\<close> pairs"

fun name_expectation anonymous =
  if anonymous then "a HOL binding or _" else "a HOL binding"

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
              | (Renames_Config, NONE) =>
                  option_type_error name rename_list_expectation name_pos
              | (Type_Config _, NONE) =>
                  option_type_error name "a HOL type" name_pos
              | (Name_Config {anonymous}, NONE) =>
                  option_type_error name (name_expectation anonymous) name_pos
              | (Name_Config _, SOME (Name_Value binding, _)) =>
                  Name_Value binding
              | (Name_Config {anonymous}, SOME (_, value_pos)) =>
                  option_type_error name (name_expectation anonymous) value_pos
              | (Backend_Config, SOME (Backend_Value value, pos)) =>
                  if member (op =) ["auto", "enum", "hol", "simple_word_enum"] value
                  then Backend_Value value
                  else error ("urust_datatype: backend expects auto, enum, hol, or simple_word_enum" ^
                    Position.here pos)
              | (Width_Config, SOME (Integer_Value width, pos)) =>
                  if width > 0 then Integer_Value width
                  else option_type_error name "a positive word width" pos
              | (Plugins_Config, SOME (Plugins_Value value, _)) => Plugins_Value value
              | (Backend_Config, _) => option_type_error name "auto, enum, hol, or simple_word_enum" name_pos
              | (Width_Config, _) => option_type_error name "a positive word width" name_pos
              | (Plugins_Config, _) => option_type_error name "a native plugin filter" name_pos
              | (Boolean_Config _, SOME (Boolean_Value enabled, _)) =>
                  Boolean_Value enabled
              | (Integer_Config _, SOME (Integer_Value level, value_pos)) =>
                  Integer_Value (validate_verbosity name value_pos level)
              | (Attributes_Config, SOME (Attributes_Value attributes, _)) =>
                  Attributes_Value attributes
              | (Renames_Config, SOME (Renames_Value renames, _)) =>
                  Renames_Value renames
              | (Type_Config _, SOME (Type_Value source, _)) =>
                  Type_Value source
              | (Boolean_Config _, SOME (_, value_pos)) =>
                  option_type_error name "true or false" value_pos
              | (Integer_Config _, SOME (_, value_pos)) =>
                  option_type_error name "an integer from 0 to 2" value_pos
              | (Attributes_Config, SOME (_, value_pos)) =>
                  option_type_error name "an Isabelle attribute list" value_pos
              | (Renames_Config, SOME (_, value_pos)) =>
                  option_type_error name rename_list_expectation value_pos
              | (Type_Config _, SOME (_, value_pos)) =>
                  option_type_error name "a HOL type" value_pos)
         in Symtab.update (name, (checked_value, name_pos)) options end)

fun configured_flag lthy options name config =
  (case Symtab.lookup options name of
     SOME (Boolean_Value enabled, _) => enabled
   | SOME _ =>
       error ("internal non-Boolean uRust command option " ^ quote name)
   | NONE => Config.get lthy config)

fun configured_integer lthy options name config =
  (case Symtab.lookup options name of
     SOME (Integer_Value level, _) => level
   | SOME _ =>
       error
         ("internal non-integer uRust command option " ^ quote name)
   | NONE => validate_verbosity name Position.none (Config.get lthy config))

(* An authored channel option wins over the scoped default; the function name is the use site
   that an inherited default's failures cite. *)
fun configured_channel lthy rust_name options name scoped =
  (case Symtab.lookup options name of
     SOME (Type_Value source, _) => SOME (URust_Type_Mappings.Authored_Channel source)
   | SOME (_, pos) => option_type_error name "a HOL type" pos
   | NONE =>
       Symtab.lookup (Channel_Defaults.get (Context.Proof lthy)) scoped
       |> Option.map (fn source =>
            URust_Type_Mappings.Inherited_Channel
              {label = "scoped default " ^ scoped, source = source,
               use_pos = #2 rust_name}))

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
               quote (Syntax.string_of_typ (Config.put show_sorts true lthy) variable_type) ^
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
    val (((closed, import_reports), field_reports),
          navigation_reports) =
      URust_Report_Transaction.capture (fn () =>
      URust_Report_Transaction.release_on_failure lthy (fn () =>
          URust_Item_Scope.capture_field_reports (fn () =>
          URust_Import_Scope.capture_reports (fn () =>
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
                  URust_Report_Transaction.check_term lthy constrained
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
            end))))
    (* Native resolved targets precede the authored Rust field/function reference, which remains
       the final navigation destination; an import declaration follows every target reached
       through it. Release every queue only after complete checking. All queues replay through
       deferred navigation, so an enclosing declaration transaction keeps them until it commits. *)
    val _ =
      URust_Report_Transaction.replay lthy navigation_reports
    val _ =
      URust_Item_Scope.replay_field_reports
        lthy field_reports
    val _ =
      URust_Import_Scope.replay_use_reports lthy import_reports
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
       fact_name: string, theorem: thm, kind: elaboration_kind,
       pretty_lhs_arguments: string list,
       pretty_arguments: string list,
       pretty_body: Pretty.T option}
  | Abbreviation_Result of
      {lhs: term, rhs: term, name: string, kind: elaboration_kind,
       pretty_lhs_arguments: string list,
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
            else
              map (fn source =>
                  URust_Report_Transaction.native lthy
                    (fn ctxt => Attrib.check_src ctxt source))
                attributes)
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

fun install_urust_result abbreviation application_definition kind
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
    (* Argument abstractions carry source spellings, which need not be identifiers and may clash
       with context fixes or the defined name once they become left-hand-side Frees. *)
    val (definition_arguments, definition_rhs) =
      if application_definition then
        let
          val used =
            Variable.names_of lthy
            |> Name.declare name
            |> Term.declare_free_names term
          fun identifier x =
            if Symbol_Pos.is_identifier x then x else Name.desymbolize NONE x
          val definition_arguments =
            #1 (Term.strip_abs_eta (length arguments) term)
            |> map (apfst identifier)
            |> Name.variant_names used
        in
          (definition_arguments,
           Term.betapplys (term, map Free definition_arguments))
        end
      else ([], term)
    val definition_lhs =
      list_comb
        (Free
          (name,
           map fastype_of definition_parameters --->
             fastype_of term),
         definition_parameters @ map Free definition_arguments)
    val pretty_argument_names = map #1 arguments
    val (pretty_lhs_arguments, pretty_arguments) =
      if application_definition then ([], [])
      else if kind = Function
      then (pretty_argument_names, [])
      else ([], pretty_argument_names)
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
          {lhs = lhs, rhs = rhs, name = full_name, kind = kind,
           pretty_lhs_arguments = pretty_lhs_arguments,
           pretty_arguments = pretty_arguments,
           pretty_body = pretty_body},
         Config.put Proof_Display.show_results show_results lthy')
      end
    else if not application_definition andalso
        null definition_parameters andalso null definition_arguments then
      (* The body is already checked and the defining equation has no arguments, so the
         theorem from Local_Theory.define is exactly the stated equation. This replays the
         remaining steps of Specification.definition -- the internal-name check, the default
         code equation and the Spec_Rules entry -- without re-checking the body and re-proving
         the equation by rewriting over it, which dominates the cost for large bodies. *)
      let
        val _ = Name.reject_internal (name, [])
        val def_binding = Thm.def_binding binding
        val ((defined_lhs, (fact_name, theorem)), lthy') =
          Local_Theory.define
            ((binding, NoSyn),
              ((def_binding, Code.singleton_default_equation_attrib :: attributes), term))
            silent_lthy
        val lthy'' =
          Spec_Rules.add def_binding Spec_Rules.equational [defined_lhs] [theorem] lthy'
      in
        (* Without parameters or arguments, the display and stored left-hand sides coincide. *)
        (Definition_Result
          {lhs = defined_lhs, display_lhs = defined_lhs,
           fact_name = fact_name, theorem = theorem, kind = kind,
           pretty_lhs_arguments = pretty_lhs_arguments,
           pretty_arguments = pretty_arguments,
           pretty_body = pretty_body},
         Config.put Proof_Display.show_results show_results lthy'')
      end
    else
      let
        val ((defined_lhs, (fact_name, theorem)), lthy') =
          Specification.definition
            (SOME (binding, NONE, NoSyn)) [] []
            ((Thm.def_binding binding, attributes),
              Logic.mk_equals (definition_lhs, definition_rhs)) silent_lthy
        val lhs = list_comb (defined_lhs, definition_parameters)
        (* The theorem's argument names: raw source spellings would be captured by context names
           when the export morphism transfers this term. *)
        val display_lhs = list_comb (lhs, map Free definition_arguments)
      in
        (Definition_Result
          {lhs = lhs, display_lhs = display_lhs,
           fact_name = fact_name, theorem = theorem, kind = kind,
           pretty_lhs_arguments = pretty_lhs_arguments,
           pretty_arguments = pretty_arguments,
           pretty_body = pretty_body},
         Config.put Proof_Display.show_results show_results lthy')
      end
  end

(* Authored definition entities of an installed result, regenerated after its invisible
   backend run. *)
fun result_definitions lthy binding declaration =
  let val consts = Consts.space_of (Proof_Context.consts_of lthy) in
    (case declaration of
       Definition_Result {lhs, ...} =>
         [(consts, declaration_name (Local_Theory.full_name lthy binding) lhs)]
     | Abbreviation_Result {name, ...} =>
         (* The backend-local head need not name the installed constant; the binding's full
            name in the returned context does. *)
         map (pair consts) (distinct (op =) [Local_Theory.full_name lthy binding, name])
     | Anonymous_Result _ => [])
  end

(* An installed definition is stated in its backend's auxiliary context; the export morphism
   restates it in the returned context, with the installed constant and no local definition.
   Input abbreviations carry no hypothesis and keep their syntactic left-hand side. *)
fun transfer_declaration phi
      (Definition_Result
        {lhs, display_lhs, fact_name, theorem, kind, pretty_lhs_arguments,
         pretty_arguments, pretty_body}) =
      Definition_Result
        {lhs = Morphism.term phi lhs, display_lhs = Morphism.term phi display_lhs,
         fact_name = fact_name, theorem = Morphism.thm phi theorem, kind = kind,
         pretty_lhs_arguments = pretty_lhs_arguments, pretty_arguments = pretty_arguments,
         pretty_body = pretty_body}
  | transfer_declaration _ result = result

fun install_invisibly install binding lthy =
  let
    val (declaration, lthy') =
      URust_Report_Transaction.invisible_declarations transfer_declaration install lthy
    val _ =
      URust_Report_Transaction.defer_definitions lthy'
        (result_definitions lthy' binding declaration)
  in (declaration, lthy') end

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
         install_invisibly
           (install_urust_result abbreviation application_definition
             kind attributes binding arguments pretty_body term)
           binding lthy
     | Anonymous_Target _ =>
         (Anonymous_Result
            {term = term,
             name = Local_Theory.full_name lthy binding,
             kind = kind,
             pretty_arguments = map #1 arguments,
             pretty_body = pretty_body},
          lthy))
  end

(* Receiver shorthands denote a type only inside an impl member, whose Self type the free
   function signature lacks. In a member they are exactly their typed spellings: self: Self,
   mut self: Self and self: &'a mut Self, where Self resolves through the member's impl context;
   the reference type spans the receiver, so &self reports the shared-reference rejection there. *)
fun receiver_shorthand_error parameter =
  error
    ("urust: receiver shorthand is only allowed in impl members" ^
      Position.here (URust_AST.function_parameter_position parameter))

fun desugar_parameter ctxt
      (parameter as URust_AST.Receiver_Parameter (form, self_pos, layout)) =
      if is_none (URust_Type_Mappings.impl_self ctxt) then receiver_shorthand_error parameter
      else
        let
          val no_layout = URust_AST.make_source_layout Position.none []
          val self_type =
            URust_AST.Path_Type
              ([URust_AST.Rust_Type_Path_Segment ("Self", Position.none, NONE, no_layout)],
               no_layout)
          val (mutable_pos, typ) =
            (case form of
               URust_AST.Receiver_Value => (NONE, self_type)
             | URust_AST.Receiver_Mut_Value =>
                 (SOME (URust_AST.the_source_token_position layout
                    (URust_AST.Keyword_Token "mut")), self_type)
             | URust_AST.Receiver_Ref {mutable, lifetime} =>
                 (NONE,
                  URust_AST.Reference_Type
                    (if mutable then URust_AST.BM_Mut else URust_AST.BM_Imm, lifetime,
                     self_type, layout)))
        in
          URust_AST.Function_Parameter
            (mutable_pos, URust_AST.P_Ident ("self", self_pos), typ, layout)
        end
  | desugar_parameter _ parameter = parameter

fun function_parameter_argument ctxt parameter =
  (case desugar_parameter ctxt parameter of
     URust_AST.Function_Parameter (mutable_pos, pattern, _, _) =>
      let
        fun unsupported pos =
          error
            ("urust_fn: unsupported function parameter pattern" ^
              Position.here pos)
      in
        (case (mutable_pos, pattern) of
           (NONE, URust_AST.P_Wild pos) => ("_", pos)
         | (SOME pos, URust_AST.P_Wild _) => unsupported pos
         | (SOME _, URust_AST.P_Ident ("Self", pos)) =>
             error
               ("urust: Self is a path pattern and cannot be a mutable binding" ^
                 Position.here pos)
         | (_, URust_AST.P_Ident (name, pos)) => (name, pos)
         | (SOME pos, _) => unsupported pos
         | (NONE, _) =>
             unsupported (URust_AST.pattern_position pattern))
      end
   | URust_AST.Receiver_Parameter _ => raise Fail "urust_fn: receiver was not desugared")

fun function_parameter_type ctxt parameter =
  (case desugar_parameter ctxt parameter of
     URust_AST.Function_Parameter (_, _, typ, _) => typ
   | URust_AST.Receiver_Parameter _ => raise Fail "urust_fn: receiver was not desugared")

fun function_arguments ctxt function =
  map (function_parameter_argument ctxt)
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

fun function_pretty_body function =
  (case URust_AST.function_body function of
     URust_AST.UE_Block (body, _) => body
   | _ =>
       error
         "urust_fn: internal Rust-shaped function body is not a block")

(* The source of a function's declaration type: a declared HOL type, or the Rust signature with
   its optional channels. *)
datatype function_signature =
    Declared_Signature of string * Position.T
  | Rust_Signature of URust_Type_Mappings.function_channels

fun function_parameter_types ctxt function =
  map (function_parameter_type ctxt) (URust_AST.function_parameters function)

fun reject_function_type_generics function =
  (case URust_AST.function_type_parameters function of
     [] => ()
   | URust_AST.Generic_Parameter (_, pos, _) :: _ =>
       error ("urust_fn: type generics are not supported" ^ Position.here pos))

(* A declared type is read like a urust_expr declaration type and alone supplies the parameter
   slots: the Rust parameter and return types are never resolved and do not constrain it. Lifetime
   scope and the lexical Self/self scope, path-start and keyword rules remain Rust rules of the item.

   Otherwise resolve the optional channels and every Rust signature type together. Shared names
   retain their sorts and relationships; independent inference holes stay distinct. The constructed
   complete type supplies the lexical parameter slots and the sole body-checking pipeline. *)
fun prepare_function_signature lthy (Declared_Signature declared) function =
      let
        val _ = reject_function_type_generics function
        val arguments = function_arguments lthy function
        val rust_types =
          function_parameter_types lthy function @
            the_list (URust_AST.function_return_type function)
        val _ =
          URust_Type_Mappings.check_lifetimes
            (URust_AST.function_lifetime_parameters function) rust_types
        val _ = URust_Type_Mappings.check_signature_syntax lthy rust_types
        val (complete_type, type_pos) =
          URust_Report_Transaction.native lthy (fn read_ctxt =>
            read_declared_type read_ctxt Function declared)
        val _ = terminal_value_type Function type_pos complete_type
        val _ =
          validate_argument_count Function type_pos arguments (binder_types complete_type)
      in
        (SOME (complete_type, type_pos),
         typed_arguments arguments (binder_types complete_type))
      end
  | prepare_function_signature lthy (Rust_Signature channels) function =
      let
        val _ = reject_function_type_generics function
        val arguments = function_arguments lthy function
        val parameter_types = function_parameter_types lthy function
        val return_type =
          the_default
            (URust_AST.Primitive_Type
              (URust_AST.DPT_Unit, URust_AST.function_item_position function))
            (URust_AST.function_return_type function)
        val complete_type =
          URust_Type_Mappings.resolve_function_signature lthy channels
            (URust_AST.function_lifetime_parameters function)
            parameter_types return_type
        (* An inherited default belongs to an earlier command; only authored channels position the
           declaration type. *)
        fun authored (SOME (URust_Type_Mappings.Authored_Channel source)) =
              SOME (Input.pos_of source)
          | authored _ = NONE
        val type_pos =
          (case map_filter authored
              [#state channels, #abort channels, #input channels, #output channels] of
             pos :: _ => pos
           | [] => URust_AST.rust_type_position return_type)
      in
        (SOME (complete_type, type_pos),
         typed_arguments arguments (binder_types complete_type))
      end

fun elaborate_function_item pp_test lthy signature_source source function =
  let
    val arguments = function_arguments lthy function
    val body_source = function_body_source source function
    val (declared_type, arguments_with_types) =
      prepare_function_signature lthy signature_source function
    val _ =
      if pp_test
      then function_pretty_roundtrip lthy source function
      else ()
    val {term, ...} =
      elaborate_prepared_ast lthy
        {kind = Function,
         source = body_source,
         declared_type = declared_type,
         arguments_with_types = arguments_with_types,
         ast = URust_AST.function_body function}
  in
    {term = term,
     arguments = arguments,
     declared_type = declared_type,
     arguments_with_types = arguments_with_types}
  end

fun declaration_registered_term
      (Definition_Result {lhs, ...}) = lhs
  | declaration_registered_term
      (Abbreviation_Result {lhs, ...}) = lhs
  | declaration_registered_term
      (Anonymous_Result {term, ...}) = term

(* How a named function with enabled registration becomes callable. A free function registers
   its Rust name. An impl member registers its associated path, whose source serial is the
   member's identity and which owns the path as an associated function of the member's Self
   type; a member with a self receiver also registers the method-only entry under its bare
   name, which reserves nothing. Identity and Self type are fixed before the declaration
   callback, so replays and interpretations keep them. *)
datatype function_registration =
    Free_Function
  | Impl_Function of
      {associated_key: string, method: bool, self_type: typ, identity: serial}

fun reject_function_item_conflict lthy registration (rust_name, rust_pos) =
  (case registration of
     Free_Function =>
       ignore (Micro_Rust_Names.reserve_declaration Micro_Rust_Names.Function_Declaration
         rust_name rust_pos (Context.Proof lthy))
   | Impl_Function {associated_key, self_type, identity, ...} =>
       ignore (Micro_Rust_Names.reserve_associated_function
         {name = associated_key, self_type = self_type, identity = identity, pos = rust_pos}
         (Context.Proof lthy)))

(* Overlap is a property of the impl, not of its registrations: a member without registered
   notations still owns its associated path. *)
fun reserve_impl_owner (Impl_Function {associated_key, self_type, identity, ...}) (_, rust_pos)
      lthy =
      Local_Theory.declaration {pervasive = false, syntax = true, pos = rust_pos}
        (fn phi =>
          Micro_Rust_Names.reserve_associated_function
            {name = associated_key, self_type = Morphism.typ phi self_type,
             identity = identity, pos = rust_pos})
        lthy
  | reserve_impl_owner Free_Function _ lthy = lthy

fun register_function_result target registration bare_name (rust_name, rust_pos) declaration
    lthy =
  (case target of
     Anonymous_Target _ => lthy
   | Named_Target _ =>
       let
         val term = declaration_registered_term declaration
         val source_const =
           (case Term.strip_comb term of (constant as Const _, _) => SOME constant | _ => NONE)
         fun register name s phi =
           Micro_Rust_Names.register_with_source_serial Micro_Rust_Names.NFunction name
             (Morphism.term phi term) (Option.map (Morphism.term phi) source_const) rust_pos s
         val (declare, registrations) =
           (case registration of
              Free_Function =>
                let val registration_serial = serial () in
                  (fn phi =>
                    Micro_Rust_Names.reserve_declaration Micro_Rust_Names.Function_Declaration
                      rust_name rust_pos #>
                    Micro_Rust_Names.mark_automatic registration_serial #>
                    register rust_name registration_serial phi,
                   [(rust_name, registration_serial)])
                end
            | Impl_Function {associated_key, method, self_type, identity} =>
                let
                  val method_serial = serial ()
                  fun method_entry phi =
                    if method then
                      Micro_Rust_Names.mark_automatic method_serial #>
                      Micro_Rust_Names.mark_method_only method_serial #>
                      register bare_name method_serial phi
                    else I
                in
                  (fn phi =>
                    Micro_Rust_Names.reserve_associated_function
                      {name = associated_key, self_type = Morphism.typ phi self_type,
                       identity = identity, pos = rust_pos} #>
                    Micro_Rust_Names.mark_automatic identity #>
                    register associated_key identity phi #>
                    method_entry phi,
                   (associated_key, identity) ::
                     (if method then [(bare_name, method_serial)] else []))
                end)
       in
         lthy |> Local_Theory.declaration {pervasive = false, syntax = true, pos = rust_pos} declare
         |> tap (fn completed =>
           (Navigation.defer_report completed rust_pos Markup.keyword3;
            List.app
              (fn (name, s) => Micro_Rust_Names.report_registration completed name rust_pos s)
              registrations))
       end)

fun declare_urust_function_result pp_test render_pretty
    abbreviation application_definition attributes binding
    target register_notation registration rust_name elaboration signature_source source function lthy =
  let
    (* Elaboration reads in the member context; the declaration installs in lthy. *)
    val elaboration_lthy = elaboration lthy
    val {term, arguments, declared_type, arguments_with_types} =
      elaborate_function_item pp_test elaboration_lthy signature_source source function
    val pretty_body =
      if render_pretty then
        let
          val body = function_pretty_body function
          fun reparse pretty_source =
            let
              val ast =
                (case URust_Parser.parse_source elaboration_lthy pretty_source of
                   SOME ast => ast
                 | NONE => error "urust_fn: empty pretty replay")
            in
              ignore
                (elaborate_prepared_ast elaboration_lthy
                  {kind = Function,
                   source = pretty_source,
                   declared_type = declared_type,
                   arguments_with_types = arguments_with_types,
                   ast = ast})
            end
        in
          SOME
            (URust_Printer_Output.pretty_human_expr_with_reparse
              reparse body)
        end
      else NONE
    (* The callable entry is registered in the same backend context as the definition. *)
    fun install backend_lthy =
      let
        val (declaration, installed) =
          install_urust_result abbreviation application_definition
            Function attributes binding arguments pretty_body term backend_lthy
      in
        (declaration,
         if register_notation then
           register_function_result target registration
             (#1 (URust_AST.function_name function)) rust_name declaration installed
         else reserve_impl_owner registration rust_name installed)
      end
    val (declaration, lthy') =
      (case target of
         Named_Target _ => install_invisibly install binding lthy
       | Anonymous_Target _ =>
           (Anonymous_Result
              {term = term,
               name = Local_Theory.full_name lthy binding,
               kind = Function,
               pretty_arguments = map #1 arguments,
               pretty_body = pretty_body},
            lthy))
    (* Native HOL declaration navigation is independent of the callable entry. *)
    val _ =
      (case target of
         Named_Target _ =>
           Navigation.defer_report lthy'
             (#2 rust_name)
             (Name_Space.markup
               (Consts.space_of (Proof_Context.consts_of lthy'))
               (Proof_Context.intern_const lthy'
                 (Local_Theory.full_name lthy binding)))
       | Anonymous_Target _ => ())
  in
    (declaration, lthy')
  end
fun verbosity_output_enabled interactive lthy =
  interactive orelse Config.get lthy Proof_Display.show_results

fun pretty_declaration_heading kind name =
  Pretty.block
    [Pretty.mark_position (Position.thread_data ())
       (Pretty.keyword1 kind),
     Pretty.brk 1,
     Pretty.str (Long_Name.base_name name),
     Pretty.str ":"]

fun pretty_compact_result kind name =
  Pretty.block1
    [pretty_declaration_heading kind name,
     Pretty.fbrk,
     Pretty.str "..."]

fun pretty_generated_result kind name lthy thms =
  Pretty.block1
    [pretty_declaration_heading kind name,
     Pretty.fbrk,
     Proof_Context.pretty_fact lthy ("", thms)]

fun print_declaration_result interactive verbosity kind name lthy full =
  if verbosity_output_enabled interactive lthy
  then
    if verbosity = 1
    then Pretty.writeln (pretty_compact_result kind name)
    else if verbosity >= 2
    then Pretty.writeln (full ())
    else ()
  else ()

fun print_generated_result interactive verbosity kind lthy (name, thms) =
  print_declaration_result interactive verbosity kind name lthy
    (fn () => pretty_generated_result kind name lthy thms)

fun print_abbreviation interactive verbosity lthy name lhs rhs =
  print_declaration_result interactive verbosity "abbreviation" name lthy
    (fn () =>
      Pretty.block1
        [pretty_declaration_heading "abbreviation" name,
         Pretty.fbrk,
         Syntax.pretty_term
           (Config.put Proof_Context.show_abbrevs false lthy)
           (Logic.mk_equals (lhs, rhs))])

fun print_anonymous interactive verbosity lthy kind name term =
  print_declaration_result interactive verbosity (command_label kind) name lthy
    (fn () =>
      Pretty.block1
        [pretty_declaration_heading (command_label kind) name,
         Pretty.fbrk,
         Syntax.pretty_term lthy term])

fun the_pretty_body (SOME pretty) = pretty
  | the_pretty_body NONE =
      error "uRust command: internal missing pretty-print body"

val symbolic_urust_open =
  Pretty.block
    [Pretty.mark_str (Markup.keyword1, "\<mu>"),
     Pretty.mark_str (Markup.delimiter, Symbol.open_)]

val symbolic_urust_close =
  Pretty.mark_str (Markup.delimiter, Symbol.close)

fun pretty_function_body lthy =
  Pretty.mark
    (Name_Space.markup
      (Consts.space_of (Proof_Context.consts_of lthy))
      \<^const_name>\<open>FunctionBody\<close>)
    (Pretty.str "FunctionBody")

fun pretty_urust_open _ Expression = symbolic_urust_open
  | pretty_urust_open lthy Function =
      Pretty.block
        [pretty_function_body lthy,
         Pretty.brk 1,
         symbolic_urust_open]

fun pretty_urust_argument "_" = Pretty.str "_"
  | pretty_urust_argument argument =
      Pretty.mark_str (Markup.bound, argument)

fun pretty_urust_formals arguments =
  Pretty.block
    ([Pretty.mark_str (Markup.operator, "|")] @
     Pretty.commas
       (map pretty_urust_argument arguments) @
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

fun pretty_urust_lhs lthy lhs arguments =
  Pretty.block
    (Syntax.pretty_term
       (Config.put Proof_Context.show_abbrevs false lthy)
       lhs ::
     maps
       (fn argument =>
         [Pretty.brk 1, pretty_urust_argument argument])
       arguments)

fun pretty_urust_equation lthy kind lhs pretty_lhs_arguments
    pretty_arguments pretty_body =
  let
    val opening =
      Pretty.block1
        [pretty_urust_lhs lthy lhs pretty_lhs_arguments,
         Pretty.brk 1,
         Pretty.str "\<equiv>",
         Pretty.str " ",
         pretty_urust_open lthy kind]
  in
    pretty_urust_lines opening pretty_arguments pretty_body
  end

fun pretty_urust_declaration lthy declaration =
  (case declaration of
     Definition_Result
       {fact_name, display_lhs, kind, pretty_lhs_arguments,
        pretty_arguments, pretty_body, ...} =>
       Pretty.chunks
         [pretty_declaration_heading "definition" fact_name,
          pretty_urust_equation lthy kind display_lhs
            pretty_lhs_arguments pretty_arguments pretty_body]
   | Abbreviation_Result
       {lhs, name, kind, pretty_lhs_arguments,
        pretty_arguments, pretty_body, ...} =>
       Pretty.chunks
         [pretty_declaration_heading "abbreviation" name,
          pretty_urust_equation lthy kind lhs
            pretty_lhs_arguments pretty_arguments pretty_body]
   | Anonymous_Result
       {name, kind, pretty_arguments, pretty_body, ...} =>
       Pretty.chunks
       [pretty_declaration_heading (command_label kind) name,
        pretty_urust_lines (pretty_urust_open lthy kind)
          pretty_arguments pretty_body])

fun print_pretty_declaration interactive verbosity lthy declaration =
  let
    val (kind, name) =
      (case declaration of
         Definition_Result {fact_name, ...} =>
           ("definition", fact_name)
       | Abbreviation_Result {name, ...} =>
           ("abbreviation", name)
       | Anonymous_Result {name, kind, ...} =>
           (command_label kind, name))
  in
    print_declaration_result interactive verbosity kind name lthy
      (fn () => pretty_urust_declaration lthy declaration)
  end

fun print_declaration interactive verbosity pretty lthy declaration =
  if pretty then
    print_pretty_declaration interactive verbosity lthy declaration
  else
  (case declaration of
     Definition_Result {fact_name, theorem, ...} =>
       print_generated_result interactive verbosity "definition" lthy
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

fun pretty_warning options source pretty verbosity =
  if pretty andalso verbosity = 0 then
    let
      val pos =
        (case Symtab.lookup options pretty_option of
           SOME (_, option_pos) => option_pos
         | NONE => Input.pos_of source)
    in
      fn () =>
        warning
          ("uRust command option " ^ quote pretty_option ^
            " has no effect when verbosity = 0" ^
            Position.here pos)
    end
  else K ()

fun warn_ineffective_pretty options source pretty verbosity =
  pretty_warning options source pretty verbosity ()
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
    (* As for function items, authored reports wait until the declaration is installed. *)
    fun declaration lthy' =
      let
        val ((result, completed), reports) =
          Navigation.capture (fn () =>
            declare_urust_result pp_test render_pretty
              abbreviation application_definition
              attributes binding kind args lthy')
        val _ = Navigation.replay completed reports
      in (result, completed) end
  in
    declare_and_print declaration interactive verbosity pretty lthy
  end

fun default_function_target function =
  let val (rust_name, rust_pos) = URust_AST.function_name function in
    Named_Target (Binding.make (URust_AST.rust_snake_case rust_name, rust_pos))
  end

(* The pure part of a function declaration: effective options, their compatibility, attribute
   checks and the HOL target. A multi-item command prepares every member before its first
   declaration; the ineffective-pretty warning is released with the successful output. *)
(* rust_name is the registration key and its position: the Rust name of a free function, the
   associated path of an impl member. The AST keeps the source name for printing. An impl member
   also carries its impl's Self context, in which it elaborates. *)
datatype prepared_function =
  Prepared_Function of
    {interactive: bool, pp_test: bool, verbosity: int, pretty: bool, render_pretty: bool,
     abbreviation: bool, application_definition: bool, attributes: Token.src list,
     binding: binding, target: declaration_target, register_notation: bool,
     signature_source: function_signature,
     rust_name: string * Position.T, registration: function_registration,
     impl_self: URust_Type_Mappings.impl_self option,
     source: Input.source, function: URust_AST.urust_function, warnings: unit -> unit}

(* A declared type supplies every channel, so an authored channel option beside it is rejected
   and scoped channel defaults are not consulted. *)
fun configured_signature lthy rust_name options NONE =
      let fun channel name scoped = configured_channel lthy rust_name options name scoped in
        Rust_Signature
          {state = channel state_option urust_state, abort = channel abort_option urust_abort,
           input = channel input_option urust_input, output = channel output_option urust_output}
      end
  | configured_signature _ _ options (SOME declared) =
      (case
          map_filter (fn name => Option.map (pair name o #2) (Symtab.lookup options name))
            [state_option, abort_option, input_option, output_option] of
         [] => Declared_Signature declared
       | (name, pos) :: _ =>
           error
             ("urust_fn: option " ^ quote name ^
               " cannot be combined with a declared type, which supplies every channel" ^
               Position.here pos))

fun prepare_function lthy
    {interactive, roundtrip, options, target, declared_type, source, function} =
  let
    val _ = URust_AST.reject_keyword_name "urust" "a function" (URust_AST.function_name function)
    val register_notation =
      configured_flag lthy options register_notation_option urust_register_notation
    val pp_test =
      roundtrip andalso configured_flag lthy options pp_test_option urust_pp_test
    val verbosity = configured_verbosity lthy options
    val pretty =
      configured_flag lthy options pretty_option urust_pretty
    val warnings = pretty_warning options source pretty verbosity
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
    val rust_name = URust_AST.function_name function
  in
    Prepared_Function
      {interactive = interactive, pp_test = pp_test, verbosity = verbosity, pretty = pretty,
       render_pretty = render_pretty, abbreviation = abbreviation,
       application_definition = application_definition, attributes = attributes,
       binding = target_binding Function target, target = target,
       register_notation = register_notation,
       signature_source = configured_signature lthy rust_name options declared_type,
       rust_name = rust_name, registration = Free_Function, impl_self = NONE,
       source = source, function = function, warnings = warnings}
  end

fun registered_constant lthy binding declaration =
  declaration_name (Local_Theory.full_name lthy binding) (declaration_registered_term declaration)

(* Verbosity 1 and 2 list the callable entries of an impl member after its declaration. *)
fun print_registration interactive verbosity lthy binding register_notation target registration
    bare_name declaration =
  (case (register_notation, target, registration) of
     (true, Named_Target _, Impl_Function {associated_key, method, ...}) =>
       if verbosity >= 1 andalso verbosity_output_enabled interactive lthy then
         let
           val name = registered_constant lthy binding declaration
           val constant =
             Pretty.mark_str
               (Name_Space.markup (Consts.space_of (Proof_Context.consts_of lthy)) name,
                Proof_Context.extern_const lthy name)
           val (kind, keys) =
             if method then ("method", associated_key ^ " / ." ^ bare_name)
             else ("associated", associated_key)
         in
           Pretty.writeln
             (Pretty.block
               [Pretty.keyword1 kind, Pretty.brk 1, Pretty.str keys, Pretty.brk 1,
                Pretty.str "\<mapsto>", Pretty.brk 1, constant])
         end
       else ()
   | _ => ())

(* The shared function declaration operation for an already prepared item. Registration
   conflicts and signature types depend on earlier declarations and are checked here. uRust
   reports join the enclosing report transaction; the successful result output is returned for
   the caller to emit after its whole transaction. *)
(* Every impl member is checked for overlap, registered or not and declared or not; a free
   function only when it registers its name. *)
fun check_registration_conflict lthy
    (Prepared_Function {register_notation, target, registration, rust_name, ...}) =
  (case (registration, register_notation, target) of
     (Impl_Function _, _, _) => reject_function_item_conflict lthy registration rust_name
   | (Free_Function, true, Named_Target _) =>
       reject_function_item_conflict lthy registration rust_name
   | _ => ())

fun declare_prepared_function
    (Prepared_Function
      {interactive, pp_test, verbosity, pretty, render_pretty, abbreviation,
       application_definition, attributes, binding, target, register_notation, signature_source,
       rust_name, registration, impl_self, source, function, warnings}) lthy =
  let
    val _ =
      check_registration_conflict lthy
        (Prepared_Function
          {interactive = interactive, pp_test = pp_test, verbosity = verbosity, pretty = pretty,
           render_pretty = render_pretty, abbreviation = abbreviation,
           application_definition = application_definition, attributes = attributes,
           binding = binding, target = target, register_notation = register_notation,
           signature_source = signature_source, rust_name = rust_name,
           registration = registration,
           impl_self = impl_self, source = source, function = function, warnings = warnings})
    val elaboration =
      (case impl_self of
         SOME self => URust_Type_Mappings.with_impl_self self
       | NONE => I)
    val (result, lthy') =
      declare_urust_function_result pp_test render_pretty
        abbreviation application_definition attributes binding
        target register_notation registration rust_name elaboration signature_source source
        function lthy
    val bare_name = #1 (URust_AST.function_name function)
  in
    (fn () =>
      (warnings ();
       print_declaration interactive verbosity pretty lthy' result;
       print_registration interactive verbosity lthy' binding register_notation target
         registration bare_name result),
     lthy')
  end

(* The registrations that declaring a prepared function makes, by the same decision as
   declare_prepared_function: a named free function with callable registration enabled installs
   its Rust callable entry. Impl members contribute no import entities: associated functions
   and methods are not namespace items. *)
fun prepared_function_registrations
    (Prepared_Function {register_notation, target, rust_name, registration, ...})
    : URust_Imports.registrations =
  {item_types = [], type_mappings = [], constructors = [], literal_notations = [],
   call_notations =
     (case (register_notation, target, registration) of
        (true, Named_Target _, Free_Function) => [#1 rust_name]
      | _ => [])}

(* A complete single-declaration transaction: replay deferred reports, then print. A failing
   declaration releases its own queued markup with its error. *)
fun run_declaration declaration lthy =
  let
    val ((output, completed), reports) =
      URust_Report_Transaction.capture (fn () =>
        URust_Report_Transaction.release_on_failure lthy (fn () => declaration lthy))
    val _ = URust_Report_Transaction.replay completed reports
    val _ = output ()
  in completed end

fun define_urust_fn
    (options, ((target_option, declared_type), source))
    interactive lthy =
  let
    val function =
      (case URust_Parser.parse_function_source lthy source of
         SOME function => function
       | NONE =>
           error
             ("urust_fn: empty function item" ^
               Position.here (Input.pos_of source)))
  in
    run_declaration
      (declare_prepared_function
        (prepare_function lthy
          {interactive = interactive, roundtrip = true, options = options,
           target = the_default (default_function_target function) target_option,
           declared_type = declared_type, source = source, function = function}))
      lthy
  end

(* Effective datatype options for the shared declaration operation, with the
   ineffective-pretty warning that accompanies successful output. *)
fun datatype_declaration
    {interactive, roundtrip, options, explicit_binding, source} lthy =
  let
    val verbosity = configured_verbosity lthy options
    val pp_test =
      roundtrip andalso configured_flag lthy options pp_test_option urust_pp_test
    val pretty =
      configured_flag lthy options pretty_option urust_pretty
    val register_notation =
      configured_flag lthy options register_notation_option urust_register_notation
    val warnings = pretty_warning options source pretty verbosity
    val declaration : URust_Datatype.declaration =
      {source = source,
       explicit_binding = explicit_binding,
       interactive = interactive,
       verbosity = verbosity,
       pp_test = pp_test,
       pretty = pretty,
       register_notation = register_notation,
       backend = (case Symtab.lookup options "backend" of
         SOME (Backend_Value value, _) => value | _ => "auto"),
       word_width = (case Symtab.lookup options "word_width" of
         SOME (Integer_Value value, _) => SOME value | _ => NONE),
       parameters = (case Symtab.lookup options hol_type_parameters_option of
         SOME (Renames_Value value, _) => value | _ => []),
       plugins = (case Symtab.lookup options "plugins" of
         SOME (Plugins_Value value, _) => value | _ => K Plugin_Name.default_filter),
       renames =
         (case Symtab.lookup options hol_names_option of
            SOME (Renames_Value renames, _) => renames
          | NONE => []
          | SOME (_, pos) =>
              option_type_error hol_names_option rename_list_expectation pos),
       unprefixed_selectors =
         (case Symtab.lookup options unprefixed_selectors_option of
            SOME (Boolean_Value true, pos) => SOME pos
          | _ => NONE)}
  in (declaration, warnings) end

datatype prepared_datatype =
  Prepared_Datatype of URust_Datatype.prepared * (unit -> unit)

fun prepared_datatype_registrations ctxt (Prepared_Datatype (prepared, _)) =
  URust_Datatype.prepared_registrations ctxt prepared

fun prepare_datatype lthy {interactive, roundtrip, options, explicit_binding, source, item} =
  let
    val (declaration, warnings) =
      datatype_declaration
        {interactive = interactive, roundtrip = roundtrip, options = options,
         explicit_binding = explicit_binding, source = source} lthy
  in Prepared_Datatype (URust_Datatype.prepare declaration item lthy, warnings) end

fun declare_prepared_datatype (Prepared_Datatype (prepared, warnings)) lthy =
  URust_Datatype.declare_prepared prepared lthy
  |>> (fn output => fn () => (warnings (); output ()))

fun define_urust_datatype
    ((options, explicit_binding), source) interactive lthy =
  let
    val item =
      (case URust_Parser.parse_datatype_source lthy source of
         SOME item => item
       | NONE =>
           error
             ("urust_datatype: empty datatype item" ^
               Position.here (Input.pos_of source)))
  in
    run_declaration
      (declare_prepared_datatype
        (prepare_datatype lthy
          {interactive = interactive, roundtrip = true, options = options,
           explicit_binding = explicit_binding, source = source, item = item}))
      lthy
  end

(* Naming choices carried by an annotation's command-layer name option. *)
fun option_target options default =
  (case Symtab.lookup options name_option of
     NONE => default
   | SOME (Name_Value (SOME binding), _) => Named_Target binding
   | SOME (Name_Value NONE, pos) => Anonymous_Target pos
   | SOME (_, pos) => option_type_error name_option (name_expectation true) pos)

fun option_datatype_binding options =
  (case Symtab.lookup options name_option of
     NONE => NONE
   | SOME (Name_Value (SOME binding), _) => SOME binding
   | SOME (_, pos) => option_type_error name_option (name_expectation false) pos)

fun option_function_target options function =
  option_target options (default_function_target function)

fun prepare_function_item lthy {interactive, roundtrip, options, source, function} =
  prepare_function lthy
    {interactive = interactive, roundtrip = roundtrip,
     options = Symtab.delete_safe name_option options,
     target = option_function_target options function, declared_type = NONE,
     source = source, function = function}

fun prepare_datatype_item lthy {interactive, roundtrip, options, source, item} =
  prepare_datatype lthy
    {interactive = interactive, roundtrip = roundtrip,
     options = Symtab.delete_safe name_option options,
     explicit_binding = option_datatype_binding options, source = source, item = item}

(* Source keys are quoted Rust names; targets are HOL names or types, written as cartouches and
   positioned at their content, like the content of a quoted key. *)
val parse_rename_target =
  Parse.token Parse.cartouche >> Parser_Lex_Util.cartouche_source >>
    (fn source => (Input.string_of source, Input.pos_of source))

val parse_renames =
  Parse.$$$ "[" |--
    Parse.!!! (Parse.enum ","
      (Parse.string_position --| Parse.$$$ "\<rightarrow>" -- parse_rename_target)
      --| Parse.$$$ "]")

fun parse_option_value config =
  Parse.position (Parse.reserved "true") >>
    (fn (_, pos) => (Boolean_Value true, pos)) ||
  Parse.position (Parse.reserved "false") >>
    (fn (_, pos) => (Boolean_Value false, pos)) ||
  Parse.position Parse.int >>
    (fn (level, pos) => (Integer_Value level, pos)) ||
  (case config of
     SOME (Type_Config _) =>
       Parse.embedded_input >>
         (fn source => (Type_Value source, Input.pos_of source))
   | SOME Renames_Config =>
       Parse.position parse_renames >>
         (fn (renames, pos) => (Renames_Value renames, pos))
   | SOME Backend_Config =>
       Parse.position Parse.name >>
         (fn (backend, pos) => (Backend_Value backend, pos))
   | SOME Plugins_Config =>
       Parse.position (Parse.$$$ "(" |-- Plugin_Name.parse_filter --| Parse.$$$ ")") >>
         (fn (filter, pos) => (Plugins_Value filter, pos))
   | SOME (Name_Config {anonymous}) =>
       (Parse.position Parse.underscore >>
         (fn (_, pos) =>
           if anonymous then (Name_Value NONE, pos)
           else
             error
               ("urust: _ is not a datatype naming placeholder" ^
                 Position.here pos))) ||
       (Parse.binding >>
         (fn binding => (Name_Value (SOME binding), Binding.pos_of binding)))
   | _ =>
       Parse.position Parse.attribs >>
         (fn (attributes, pos) => (Attributes_Value attributes, pos)))

fun unknown_option (name, pos) =
  error ("unknown uRust command option " ^ quote name ^ Position.here pos)

(* A minor keyword such as output can name an option. Its later report replaces the keyword colour
   with that of Isabelle's unhighlighted keywords, so it renders like every other option name. *)
val parse_option_name =
  Scan.ahead Parse.not_eof -- Parse.position Parse.liberal_name >>
    (fn (token, name) =>
      (if Token.is_kind Token.Keyword token then Position.report (#2 name) Markup.delimiter
       else ();
       name))

(* One entry parser and schema check serve both clients: bracketed command lists and omega
   annotation payloads. A client-specific rejection explains names outside its schema. *)
fun parse_inline_option_with reject option_configs =
  parse_option_name :|-- (fn name =>
    (case Symtab.lookup option_configs (fst name) of
       NONE => reject name
     | SOME config =>
         Scan.option (Parse.$$$ "=" |-- parse_option_value (SOME config)) >>
           pair name))

fun parse_option_entries reject option_configs =
  Parse.enum1 "," (parse_inline_option_with reject option_configs) >>
    (fn options => fold (add_inline_option option_configs) options Symtab.empty)

fun parse_command_options_with reject option_configs =
  Scan.optional
    (Parse.$$$ "[" |--
      Parse.!!! (parse_option_entries reject option_configs --| Parse.$$$ "]"))
    Symtab.empty

fun parse_command_options option_configs =
  parse_command_options_with unknown_option option_configs

fun reject_chunk_option (name, pos) =
  if Symtab.defined function_annotation_configs name orelse
      Symtab.defined datatype_annotation_configs name
  then
    let
      val scoped =
        (case Symtab.lookup function_annotation_configs name of
           SOME (Type_Config scoped) => " or set the scoped " ^ scoped ^ " default"
         | _ => "")
    in
      error
        ("urust: option " ^ quote name ^
          " is declaration-specific; supply it in an \<omega> annotation" ^ scoped ^
          Position.here pos)
    end
  else unknown_option (name, pos)

fun reject_annotation_option kind other_configs (name, pos) =
  if Symtab.defined other_configs name
  then
    error
      ("urust: option " ^ quote name ^ " does not apply to " ^ kind ^ " declarations" ^
        Position.here pos)
  else unknown_option (name, pos)

(* Item-list commands: the shared defaults of an outer list and the per-declaration schemas of
   annotations, each with the client-specific rejection of names outside it. *)
(* An impl annotation supplies function defaults to every member; the HOL binding belongs to
   one member. *)
fun reject_impl_option (name, pos) =
  if name = name_option then
    error
      ("urust: option " ^ quote name_option ^ " names one function; supply it in an " ^
        "\<omega> annotation on the member" ^ Position.here pos)
  else reject_annotation_option "impl" datatype_annotation_configs (name, pos)

(* The chunk roundtrips an impl envelope as a whole, so pp_test belongs to the impl. *)
fun reject_impl_member_option (name, pos) =
  if name = pp_test_option then
    error
      ("urust: " ^ pp_test_option ^ " applies to the whole impl; set it on the impl annotation" ^
        Position.here pos)
  else reject_annotation_option "fn" datatype_annotation_configs (name, pos)

datatype option_schema =
  Chunk_Defaults | Function_Annotation | Datatype_Annotation | Impl_Annotation |
  Impl_Member_Annotation

fun schema_configs Chunk_Defaults = (reject_chunk_option, chunk_option_configs)
  | schema_configs Impl_Annotation = (reject_impl_option, function_option_configs)
  | schema_configs Impl_Member_Annotation =
      (reject_impl_member_option, Symtab.delete pp_test_option function_annotation_configs)
  | schema_configs Function_Annotation =
      (reject_annotation_option "fn" datatype_annotation_configs, function_annotation_configs)
  | schema_configs Datatype_Annotation =
      (reject_annotation_option "struct or enum" function_annotation_configs,
       datatype_annotation_configs)

fun parse_options schema =
  let val (reject, option_configs) = schema_configs schema
  in parse_command_options_with reject option_configs end

(* Annotation payloads are positioned Isabelle source in the theory's outer-syntax keyword
   context. The complete payload must be one nonempty entry list. *)
fun read_annotation_options lthy schema annotation =
  let
    val (reject, option_configs) = schema_configs schema
    val keywords = Thy_Header.get_keywords' lthy
    val tokens =
      Token.tokenize keywords {strict = true}
        (Input.source_explode (URust_AST.annotation_payload annotation))
      |> filter Token.is_proper
    val _ = Context_Position.reports_text lthy (maps (Token.reports keywords) tokens)
    val _ =
      if null tokens
      then
        error
          ("urust: an \<omega> annotation must contain at least one option; " ^
            "omit an empty annotation" ^
            Position.here (URust_AST.annotation_position annotation))
      else ()
    val entries =
      Parse.!!!
        (parse_option_entries reject option_configs --|
          Scan.ahead (Parse.group (fn () => "\",\" or end of annotation") Parse.eof))
  in
    (case Scan.read Token.stopper entries tokens of
       SOME options => options
     | NONE =>
         error
           ("urust: malformed \<omega> annotation" ^
             Position.here (URust_AST.annotation_position annotation)))
  end

(* Entries of the first table replace those of the second; neither list is concatenated. *)
fun override_options overrides defaults = Symtab.fold Symtab.update overrides defaults

fun configured_pp_test lthy options =
  configured_flag lthy options pp_test_option urust_pp_test

(* Impl blocks. Preparation is pure, like that of the other chunk members: every member's
   options and HOL binding are fixed before the first declaration of the chunk. The target is
   resolved when the impl is declared, in its own member context, so it may name an earlier
   member of the same chunk. *)
type prepared_impl_member = {prepared: prepared_function, method: bool, default_name: bool}

datatype prepared_impl =
  Prepared_Impl of {target: URust_AST.rust_type, members: prepared_impl_member list}

fun is_self_parameter (URust_AST.Receiver_Parameter _) = true
  | is_self_parameter (URust_AST.Function_Parameter (_, URust_AST.P_Ident ("self", _), _, _)) =
      true
  | is_self_parameter _ = false

(* Rust admits self only as the first parameter of an associated function, typed or not. *)
fun check_member_receiver function =
  (case URust_AST.function_parameters function of
     [] => ()
   | _ :: rest =>
       (case find_first is_self_parameter rest of
          SOME (URust_AST.Function_Parameter (_, URust_AST.P_Ident (_, pos), _, _)) =>
            error ("urust: a self receiver must be the first parameter" ^ Position.here pos)
        | SOME parameter =>
            error
              ("urust: a self receiver must be the first parameter" ^
                Position.here (URust_AST.function_parameter_position parameter))
        | NONE => ()))

fun is_method function =
  (case URust_AST.function_parameters function of
     first :: _ => is_self_parameter first
   | [] => false)

(* The final segment of the written target names the default HOL bindings, which are therefore
   known before the target resolves. Every other target shape is rejected here already. *)
fun impl_target_segment lthy target =
  (case target of
     URust_AST.Path_Type (segments, _) =>
       (case List.last segments of URust_AST.Rust_Type_Path_Segment (name, _, _, _) => name)
   | _ =>
       (ignore (URust_Type_Mappings.resolve_impl_target lthy target);
        raise Fail "urust: a non-path impl target was accepted"))

fun prepare_impl_item lthy {interactive, options, impl} =
  let
    val target = URust_AST.impl_target impl
    val segment = URust_AST.rust_snake_case (impl_target_segment lthy target)
    fun prepare_member member =
      let
        val function = URust_AST.impl_member_function member
        val member_options =
          (case URust_AST.impl_member_annotation member of
             NONE => options
           | SOME annotation =>
               override_options
                 (read_annotation_options lthy Impl_Member_Annotation annotation) options)
        val _ = check_member_receiver function
        val (name, name_pos) = URust_AST.function_name function
        val default =
          Named_Target
            (Binding.make (segment ^ "_" ^ URust_AST.rust_snake_case name, name_pos))
      in
        {prepared =
           prepare_function lthy
             {interactive = interactive, roundtrip = false,
              options = Symtab.delete_safe name_option member_options,
              target = option_target member_options default, declared_type = NONE,
              source = URust_AST.impl_member_source member, function = function},
         method = is_method function,
         default_name = not (Symtab.defined member_options name_option)}
      end
  in
    Prepared_Impl {target = target, members = map prepare_member (URust_AST.impl_members impl)}
  end

fun impl_member_function_of
    ({prepared = Prepared_Function {interactive, pp_test, verbosity, pretty, render_pretty,
       abbreviation, application_definition, attributes, binding, target, register_notation,
       signature_source, rust_name = (name, pos), source, function, warnings, ...}, method, ...}
     : prepared_impl_member)
    (self as {canonical_path, self_type, ...}: URust_Type_Mappings.impl_self) =
  let val associated_key = canonical_path ^ "::" ^ name in
    Prepared_Function
      {interactive = interactive, pp_test = pp_test, verbosity = verbosity, pretty = pretty,
       render_pretty = render_pretty, abbreviation = abbreviation,
       application_definition = application_definition, attributes = attributes,
       binding = binding, target = target, register_notation = register_notation,
       signature_source = signature_source, rust_name = (associated_key, pos),
       registration =
         Impl_Function
           {associated_key = associated_key, method = method, self_type = self_type,
            identity = serial ()},
       impl_self = SOME self, source = source, function = function, warnings = warnings}
  end

(* The default HOL name of a member (O3) does not distinguish the impls of different instances of
   one type. A clash with an existing constant is reported at the member, before any declaration,
   with the position of the earlier declaration and the remedy. *)
fun reject_default_name_clash lthy ({canonical_path, ...}: URust_Type_Mappings.impl_self)
    ({prepared = Prepared_Function {binding, target, function, ...}, default_name, ...}
      : prepared_impl_member) =
  (case target of
     Named_Target _ =>
       if not default_name then ()
       else
         let
           val space = Consts.space_of (Proof_Context.consts_of lthy)
           val full_name = Local_Theory.full_name lthy binding
         in
           if not (Name_Space.declared space full_name) then ()
           else
             let
               val other_pos = #pos (Name_Space.the_entry space full_name)
               val (name, pos) = URust_AST.function_name function
               (* Another impl only when the constant is the backend of an impl member's path
                  entry, whose serial is that member's identity. *)
               val key = canonical_path ^ "::" ^ name
               val identities = map #identity (Micro_Rust_Names.associated_functions lthy key)
               fun impl_member ({serial, hol_term, ...}: Micro_Rust_Names.entry) =
                 member (op =) identities serial andalso
                   (case Term.head_of hol_term of
                      Const (constant, _) => constant = full_name
                    | _ => false)
               val other =
                 if exists impl_member
                     (Micro_Rust_Names.lookups lthy Micro_Rust_Names.NFunction key)
                 then "another impl of " ^ quote canonical_path
                 else "an earlier declaration"
             in
               error
                 ("urust: the default HOL name " ^ quote (Binding.name_of binding) ^
                   " of member " ^ quote name ^ Position.here pos ^ " is already used by " ^
                   other ^ Position.here other_pos ^
                   "; choose another HOL name with \<omega>\<open>name = \"...\"\<close> on one of them")
             end
         end
   | Anonymous_Target _ => ())

(* Each member declares in the context that the next command of an equivalent sequence would
   receive: enter prepares that context (for a chunk, its import frame), and leave closes it.
   The target resolves once, in the first such context, before any member. *)
(* The associated-function owners of checked-only (name = _) members, which declare nothing: the
   caller threads them through every later impl of its command. *)
type checked_owner = {name: string, self_type: typ, identity: serial, pos: Position.T}

fun declare_prepared_impl {enter, leave} (Prepared_Impl {target, members}) (lthy, checked0) =
  let
    val target_lthy = enter lthy
    val self =
      URust_Report_Transaction.release_on_failure target_lthy
        (fn () => URust_Type_Mappings.resolve_impl_target target_lthy target)
    (* A checked-only member (name = _) declares nothing, so later members of the impl see its
       owner only through this list. *)
    fun declare member (lthy', checked) =
      let
        val member_lthy = enter lthy'
        val prepared as Prepared_Function {target = member_target, registration, rust_name, ...} =
          impl_member_function_of member self
        val with_checked =
          Context.proof_of (fold Micro_Rust_Names.reserve_associated_function checked
            (Context.Proof member_lthy))
        val (output, lthy'') =
          URust_Report_Transaction.release_on_failure member_lthy
            (fn () =>
              (* A duplicate member is Rust's overlap error first; only a member that passes it
                 can clash by its default HOL name. *)
              (check_registration_conflict with_checked prepared;
               reject_default_name_clash member_lthy self member;
               declare_prepared_function prepared member_lthy))
          ||> leave
        val checked' =
          (case (member_target, registration) of
             (Anonymous_Target _, Impl_Function {associated_key, self_type, identity, ...}) =>
               {name = associated_key, self_type = self_type, identity = identity,
                pos = #2 rust_name} :: checked
           | _ => checked)
      in (output, (lthy'', checked')) end
    val (outputs, (lthy'', checked'')) = fold_map declare members (lthy, checked0)
  in (fn () => List.app (fn output => output ()) outputs, (lthy'', checked'')) end

fun prepared_impl_registrations (_: prepared_impl) = URust_Imports.no_registrations

(* The associated paths an impl's members own, as far as they are known before it is
   declared: the target head resolves through registered aliases and imports, and a target that
   a later chunk member declares keeps its written path. *)
fun prepared_impl_associated_keys ctxt (Prepared_Impl {target, members}) =
  (case URust_Type_Mappings.impl_target_key ctxt target of
     NONE => []
   | SOME path =>
       (* Every member owns its associated path, registered, unregistered or checked-only. *)
       map (fn {prepared = Prepared_Function {rust_name, ...}, ...} => path ^ "::" ^ #1 rust_name)
         members)

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
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source))

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_expr\<close>
    "Declare a uRust expression"
    (parse_urust_declaration expression_option_configs >>
      define_urust_expr)

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_fn\<close>
    "Declare a uRust function from a Rust item, optionally with a declared HOL type"
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

fun define_urust_type_alias (registration, source) lthy =
  let
    val (completed, reports) =
      URust_Report_Transaction.capture (fn () =>
        let
          val item =
            (case URust_Parser.parse_type_alias_source lthy source of
               SOME item => item
             | NONE =>
                 error
                   ("urust_type_alias: empty type alias item" ^
                     Position.here (Input.pos_of source)))
          val reject = URust_AST.reject_keyword_name "urust_type_alias"
          val _ = reject "a type" (URust_AST.type_alias_name item)
          val _ =
            List.app
              (fn URust_AST.Generic_Parameter (name, pos, URust_AST.Type_Parameter) =>
                    reject "a type parameter" (name, pos)
                | URust_AST.Generic_Parameter (name, pos, URust_AST.Const_Parameter) =>
                    reject "a const parameter" (name, pos))
              (URust_AST.type_alias_parameter_descriptors item)
        in
          URust_Type_Mappings.declare_generic_alias
            {registration = registration,
             item_name = URust_AST.type_alias_name item,
             parameters = URust_AST.type_alias_parameter_descriptors item,
             rhs = URust_AST.type_alias_rhs item}
            lthy
        end)
    val _ = URust_Report_Transaction.replay completed reports
  in completed end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>urust_type_alias\<close>
    "Declare a context-local Rust type synonym"
    (Scan.option Parse.string_position --
      (Parse.token Parse.cartouche >> Parser_Lex_Util.cartouche_source) >>
        define_urust_type_alias)

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
