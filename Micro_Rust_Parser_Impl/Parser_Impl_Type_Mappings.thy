theory Parser_Impl_Type_Mappings
  imports
    Parser_Impl_AST
    Parser_Impl_Grammar
    Parser_Impl_Printer
    Parser_Utils
    Parser_Impl_Model_Parameters
    Parser_Impl_Import_Scope
    Shallow_Micro_Rust.Semantic_Navigation
    Shallow_Micro_Rust.Micro_Rust_Notations
    Shallow_Micro_Rust.Tuple
    Shallow_Micro_Rust.Global_Store
    Misc.Array
  keywords "urust_type" :: thy_decl
begin

section\<open> Extensible Rust-to-HOL type mappings \<close>

text\<open>
Named Rust types, including lexical primitive spellings, acquire HOL meanings only through this
context-local registry. A mapping key may be qualified and may contain ordered generic
placeholders. The placeholders are mapping parameters rather than Rust lifetimes. Without options
they must be exactly the checked HOL template's free type variables. The positioned
\<open>implicit\<close> option instead assigns additional variables to the existing address/global
backend roles. The positioned \<open>erase\<close> option names source placeholders absent from the
template. Every template variable still belongs to exactly one retained source slot or implicit
role, and retained source slots keep their original indexes.

Function signatures additionally resolve mutable references \<open>&mut T\<close>, optionally with a Rust
lifetime, to the same \<open>Global_Store.ref\<close> model as raw pointers, sharing the signature's
address/global backend roles. Manual mappings request zero, one or both roles from the same lazy
environment, and generated datatype schemes preserve those roles explicitly. Lifetimes are checked against the function's declared lifetime
parameters and then erased; they never change the resolved type. Shared signature references
\<open>&T\<close> require an explicit nominal or item policy selecting value, reference, or readonly,
except that slices have the fixed readonly representation. Structural \<open>[T]\<close> denotes
the recursively resolved element's HOL list type. Slice aliases retain this meaning, including
the canonical borrow policy. The reference carriers use the same backend environment.
References in datatype fields, aliases and cast targets remain rejected. A function with a
declared HOL type resolves no signature type while retaining these lifetime scope rules and the
lexical restrictions on Self and self in Rust type paths.

The common header traversal also checks direct outlives relations against complete declared and
inherited lifetime scopes. Relations erase and create no HOL sort, witness, backend role or borrow
law. \<open>check_impl_header\<close> gives predicates lexical Self scope before the target is checked;
it installs no denotation. After the single target check, \<open>check_outlives_head\<close> validates
the pure head's supported source shape and scoped generic kinds, without lookup, inference,
reports or use events. The common header traversal has already checked its lifetime references.
This source-only policy does not consult nominal HOL mapping metadata. Opaque HOL, macro and
const-expression payloads remain opaque; no expansion, Rust type-name resolution or body binding
is claimed. The separate erased call/target-argument policy below is unchanged.

An impl target resolves like a signature type, expanding type aliases to their nominal target; its
canonical registry key and HOL Self type form the context of the impl's members, in which every
type resolution reads \<open>Self\<close> as that type. Source-sensitive owners additionally retain
expanded structural argument identity, transported alongside their HOL Self type. Outside such a
context \<open>Self\<close> is rejected.
Concrete impl targets finalize only their explicitly allocated backend roles; unrelated authored
or source inference holes remain rejected. Member signatures reuse checked Self role bindings
obtained by matching declared canonical scheme metadata, so Self, mapped aliases, pointers and
mutable references share roles even when the body does not relate their values. Role names are
fresh with respect to authored/ambient variables; no ambient default is inferred.
Incompatible demands on fixed Self or ambient types reject.

The per-function Proof_Data generic scope resolves after Self and before the parameter hook or
registry. Type and const roles are checked recursively through tuples, references, pointers and
arrays; grouped errors retain the parameter leaf position. Named HOL variables share final sorts
with checked escapes and channel types. The scope never enters a later declaration's context.
This lower owner also stores source-specific ordered generic schemes: native named identities,
complete backends and used/unused parameter witnesses are jointly typed and morphism-transformed.
Existing registration serials distinguish equal expanded abbreviation bodies. Candidate alignment
uses the native-fresh backend without freshening caller variables again; final unification and
selection remain in the notation dispatcher.

The complete single-view getters \<open>binding_generic_scheme_for_source\<close> and
\<open>binding_generic_scheme\<close> require identical transported metadata.
\<open>binding_generic_schemes_for_source\<close> instead returns all complete instances of one
source declaration after checking their shared declaration invariants. Locale interpretations
may differ in concrete witnesses, callable channels and Self types; these stay together in each
instance and are checked jointly against the actual candidate. Source routing reads only common
declaration descriptors, without selecting a concrete instance before native dispatch.

Erased arguments accept supported nominal paths, grouping, primitives and normalized unsigned
numeric leaves. Known schemes check all source arities, kinds and available bound evidence.
Source-only validation requests no semantic backend, even for a known implicit mapping nested in
an erased argument. Unsupported forms and scoped associated projections fail positionally.
Retained arrays keep structural element and length meaning for alias substitution. Authored HOL
meaning leaves receive the enclosing inference state's final substitution; canonical mapped
templates retain their own scheme variables.

The source-slot view \<open>generic_source_scheme_for_source\<close> preserves order, kind, bounds,
sort, observed source use and optional witness availability. Legacy registrations mark source
use unknown. Only actual witnesses are transported with the backend and native identity.
The old exact generic records and registration APIs remain adapters; their witness view is absent
for a sparse scheme. Sparse instantiation requires exactly the recorded availability mask.
The entry getters retain full source arities, kinds, sorts and ordered erasure indexes.
\<open>entry_backend_roles\<close> orders roles address then global, preserving canonical global
index 1 even for a singleton. \<open>resolve_declaration_roles\<close>,
\<open>preflight_declaration_role_scheme\<close> and \<open>register_declaration_role_scheme\<close>
carry named roles through datatype resolution and registration. The old exact positional
registration records remain adapters for an empty role list or the established address/global
pair; a singleton needs the role-aware API.

\<open>generic_source_parameter\<close> exposes the exact optional witness field \<open>hol\<close>
alongside Rust name/kind, sort, bounds and optional observed source use. \<open>NONE\<close> source use
means unknown legacy metadata; it does not mean erased. \<open>register_generic_source_scheme\<close>
and \<open>instantiate_generic_source_scheme_for_source\<close> preserve all source slots and the
exact witness availability mask. \<open>resolve_source_arguments\<close> validates every slot and
returns optional HOL arguments plus independent source identities. The old
\<open>generic_scheme_parameter = {rust, kind, hol}\<close> record remains unchanged; old witness
getters return no scheme for sparse registrations. Re-registration through the old API keeps
authoritative usage/bounds only for a unique matching existing source scheme with agreeing slots.

\<open>capture_generic_use_events\<close> separates source occurrence from witness demand, excluding
inference seeds and foreign scopes. The compatible \<open>capture_generic_uses\<close> observes witness
demand. \<open>report_generic_reference\<close> checks
the current full parameter identity and forwards the original reference callback exactly once.
Scope records and callbacks remain unchanged. Nested captures retain actual same-scope observations
and deactivate on every exit; no observer or captured context is installed in declarations.
Source-only body references are valid, while a request for an unavailable HOL witness rejects.
Unmapped erased tags require no HOL declaration when no bound demands denotation. This structural
subset includes recursively checked slices but excludes references, pointers, arrays, callable types, impl Trait, macros, HOL
escapes, lifetimes, associated bindings and general const expressions, recursively. Known bounds
require rigid existing evidence, without strengthening a discarded implicit role.
\<close>

ML\<open>
signature URUST_TYPE_MAPPINGS =
sig
  type entry
  datatype shared_policy = Shared_Value | Shared_Reference | Shared_Readonly
  val entry_shared_policy: entry -> (shared_policy * Position.T) option
  val with_shared_references:
    URust_Model_Parameters.rename list -> URust_AST.rust_type list ->
      URust_AST.rust_type -> Proof.context -> Proof.context
  val configure_shared_references:
    URust_Model_Parameters.rename list -> Proof.context -> Proof.context
  val prepare_shared_references:
    URust_AST.rust_type list -> URust_AST.rust_type -> Proof.context -> Proof.context
  val prepare_impl_shared_references: Proof.context -> Proof.context
  val inherit_shared_references: Proof.context -> Proof.context -> Proof.context
  val activate_shared_references: Proof.context -> Proof.context
  val without_shared_references: Proof.context -> Proof.context
  datatype backend_role = datatype URust_Model_Parameters.role
  val model_parameter_requirements: Proof.context -> (backend_role * sort) list
  val with_model_parameters:
    URust_Model_Parameters.rename list -> Proof.context -> Proof.context
  val model_parameters_declaration:
    Proof.context -> URust_Model_Parameters.rename list ->
      (Context.generic -> Context.generic) Morphism.entity
  val inherit_model_parameters: Proof.context -> Proof.context -> Proof.context
  val without_model_parameters: Proof.context -> Proof.context
  val capture_impl_model_parameters:
    Proof.context -> (Proof.context -> 'a) -> 'a * (backend_role * typ) list
  val with_impl_model_parameters: (backend_role * typ) list -> Proof.context -> Proof.context
  val inherit_impl_model_parameters: Proof.context -> Proof.context -> Proof.context
  val with_ambient_type_parameters:
    URust_AST.generic_parameter list -> URust_Model_Parameters.rename list ->
      Proof.context -> Proof.context
  val ambient_parameter_names:
    Proof.context -> URust_AST.generic_parameter list ->
      ((string * Position.T) * (string * Position.T)) list -> (string * sort) list
  val ambient_parameter_sort: Proof.context -> string -> sort -> sort

  val resolve: Proof.context -> URust_AST.rust_type -> typ
  val resolve_signature:
    Proof.context -> URust_AST.rust_type list -> typ list
  datatype channel_source =
      Authored_Channel of Input.source
    | Inherited_Channel of {label: string, source: Input.source, use_pos: Position.T}
  type function_channels =
    {state: channel_source option, abort: channel_source option,
     input: channel_source option, output: channel_source option}
  val resolve_function_signature:
    Proof.context -> function_channels -> URust_AST.rust_lifetime list ->
      URust_AST.rust_type list -> URust_AST.rust_type -> typ
  val check_lifetimes: URust_AST.rust_lifetime list -> URust_AST.rust_type list -> unit
  val check_signature_syntax: Proof.context -> URust_AST.rust_type list -> unit
  val check_function_header: Proof.context -> URust_AST.urust_function -> unit
  val check_impl_header: Proof.context -> URust_AST.urust_function -> unit
  val check_outlives_head: Proof.context -> URust_AST.rust_type -> unit
  val with_header_lifetimes: URust_AST.rust_lifetime list -> Proof.context -> Proof.context
  val inherit_header_lifetimes: Proof.context -> Proof.context -> Proof.context
  val rust_type_operands: URust_AST.rust_type -> URust_AST.rust_type list
  val resolve_fields:
    Proof.context -> URust_AST.rust_type list ->
      {types: typ list, backend_parameters: (string * sort) list}
  val resolve_declaration:
    Proof.context -> URust_AST.generic_parameter list ->
      ((string * Position.T) * (string * Position.T)) list ->
      URust_AST.rust_type list ->
      {types: typ list, source_parameters: (string * sort) list,
       backend_parameters: (string * sort) list}
  val resolve_declaration_roles:
    Proof.context -> URust_AST.generic_parameter list ->
      ((string * Position.T) * (string * Position.T)) list ->
      URust_AST.rust_type list ->
      {types: typ list, source_parameters: (string * sort) list,
       backend_parameters: (backend_role * (string * sort)) list}
  type field_representation =
    {source_head: string, representation: string, declaration_pos: Position.T,
     declaration_identity: serial}
  val resolve_declaration_roles_with_representations:
    Proof.context -> URust_AST.generic_parameter list ->
      ((string * Position.T) * (string * Position.T)) list ->
      ((string * Position.T) option * URust_AST.rust_type) list ->
      {types: typ list, source_parameters: (string * sort) list,
       backend_parameters: (backend_role * (string * sort)) list,
       representations: field_representation option list}
  val instantiate_constructor:
    Proof.context -> string -> URust_AST.rust_generic_argument list -> term -> term
  val preflight_declaration_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, source_parameters: (string * sort) list,
     parameter_kinds: URust_AST.generic_parameter_kind list,
     backend_parameters: (string * sort) list} -> local_theory -> unit
  val register_declaration_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, source_parameters: (string * sort) list,
     parameter_kinds: URust_AST.generic_parameter_kind list,
     backend_parameters: (string * sort) list} -> local_theory -> local_theory
  val preflight_declaration_role_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, source_parameters: (string * sort) list,
     parameter_kinds: URust_AST.generic_parameter_kind list,
     backend_parameters: (backend_role * (string * sort)) list} -> local_theory -> unit
  val register_declaration_role_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, source_parameters: (string * sort) list,
     parameter_kinds: URust_AST.generic_parameter_kind list,
     backend_parameters: (backend_role * (string * sort)) list} -> local_theory -> local_theory
  val resolve_cast:
    Proof.context -> URust_AST.source_cast_target -> URust_AST.cast_target
  val declare_alias:
    {registration: (string * Position.T) option,
     item_name: string * Position.T,
     parameters: (string * Position.T) list,
     rhs: URust_AST.rust_type} ->
    local_theory -> local_theory
  val declare_generic_alias:
    {registration: (string * Position.T) option,
     item_name: string * Position.T,
     parameters: URust_AST.generic_parameter list,
     rhs: URust_AST.rust_type} -> local_theory -> local_theory
  val lookup: Proof.context -> string -> entry option
  val dump: Proof.context -> (string * entry) list
  val lookup_representation: Proof.context -> string -> string -> entry option
  val dump_representations: Proof.context -> ((string * string) * entry) list

  type impl_self =
    {canonical_path: string, self_type: typ, target_pos: Position.T,
     report_reference: Position.T -> unit}
  val resolve_impl_target: Proof.context -> URust_AST.rust_type -> impl_self
  type source_identity
  val resolve_impl_target_selection:
    Proof.context -> URust_AST.rust_type ->
      impl_self * source_identity option * Micro_Rust_Names.target_selection
  val resolve_target_selection:
    Proof.context -> URust_AST.rust_type -> Micro_Rust_Names.target_selection
  val resolve_target_selection_with_inputs:
    Proof.context -> (Position.T * Input.source) list -> URust_AST.rust_type ->
      Micro_Rust_Names.target_selection
  val resolve_impl_target_identity:
    Proof.context -> URust_AST.rust_type -> impl_self * source_identity option
  val with_impl_self_identity:
    impl_self * source_identity option -> Proof.context -> Proof.context
  val impl_source_identity: Proof.context -> source_identity option
  val source_identity_name: source_identity -> string
  val morph_source_identity: morphism -> source_identity -> source_identity
  val resolve_type_identity:
    Proof.context -> URust_AST.rust_type -> typ * source_identity option
  val impl_target_key: Proof.context -> URust_AST.rust_type -> string option
  val with_impl_self: impl_self -> Proof.context -> Proof.context
  val impl_self: Proof.context -> impl_self option

  type generic_parameter =
    {rust: string, pos: Position.T, kind: URust_AST.generic_parameter_kind,
     hol: string * sort, bounds: string list, report_reference: Position.T -> unit}
  type generic_scope = {parameters: generic_parameter list}
  val with_generic_scope: generic_scope -> Proof.context -> Proof.context
  val generic_scope: Proof.context -> generic_scope option
  val source_target_template:
    Proof.context -> {self_type: typ, source: source_identity,
      declarations: serial list, witnesses: typ option list} -> Micro_Rust_Names.target_template
  type generic_declaration_identity = serial
  val fresh_generic_declaration_identity: unit -> generic_declaration_identity
  val generic_scope_identities: Proof.context -> generic_declaration_identity list option
  val with_identified_generic_scope:
    generic_scope -> generic_declaration_identity list -> Proof.context -> Proof.context
  val capture_generic_uses:
    Proof.context -> (Proof.context -> 'a) -> 'a * string list
  val report_generic_reference:
    Proof.context -> generic_parameter -> Position.T -> unit
  val report_generic_source_reference:
    Proof.context -> generic_parameter -> Position.T -> unit
  val capture_generic_use_events:
    Proof.context -> (Proof.context -> 'a) ->
      'a * {source_uses: string list, witness_uses: string list}
  val capture_generic_argument_events:
    Proof.context -> (Proof.context -> 'a) ->
      'a * {source_uses: string list, witness_uses: string list}
  val replay_generic_argument_events:
    Proof.context -> {source_uses: string list, witness_uses: string list} -> unit
  val with_source_only_parameters: string list -> Proof.context -> Proof.context
  val with_declared_body_parameters: string list -> Proof.context -> Proof.context
  val declared_generic_scope: Proof.context -> bool
  val parameter_available: Proof.context -> generic_parameter -> bool
  val parameter_has_witness: Proof.context -> generic_parameter -> bool
  val generic_reference_requires_witness: unit -> bool
  val parameter_names:
    Proof.context -> URust_AST.generic_parameter list ->
      ((string * Position.T) * (string * Position.T)) list -> (string * sort) list
  type generic_scheme_parameter =
    {rust: string, kind: URust_AST.generic_parameter_kind, hol: string * sort}
  type generic_source_parameter =
    {rust: string, kind: URust_AST.generic_parameter_kind,
     hol: (string * sort) option, sort: sort, bounds: string list, source_used: bool option}
  type impl_scheme =
    {parameters: generic_source_parameter list, declarations: generic_declaration_identity list,
     target: Micro_Rust_Names.target_template}
  type scoped_scheme_registration =
    {identity: term, backend: term, sources: serial list, owner: impl_scheme option,
     parameters: generic_source_parameter list, pos: Position.T}
  type scoped_generic_scheme
  val register_scoped_generic_source_scheme:
    scoped_scheme_registration -> local_theory -> local_theory
  val scoped_generic_scheme_for_source: Proof.context -> serial -> scoped_generic_scheme option
  val scoped_generic_scheme: Proof.context -> term -> scoped_generic_scheme option
  val scoped_owner: scoped_generic_scheme -> impl_scheme option
  val scoped_parameters: scoped_generic_scheme -> generic_source_parameter list
  val instantiate_scoped_generic_scheme_for_source:
    Proof.context -> serial -> term ->
      {target: Micro_Rust_Names.target_selection option,
       arguments: (typ option * Position.T) list option} -> term option
  val prepare_scoped_target_selection:
    Proof.context -> serial -> Micro_Rust_Names.target_selection -> Micro_Rust_Names.target_selection
  val generic_source_scheme_for_source:
    Proof.context -> serial -> generic_source_parameter list option
  val register_generic_source_scheme:
    {identity: term, backend: term, sources: serial list,
     parameters: generic_source_parameter list, pos: Position.T} ->
      local_theory -> local_theory
  val instantiate_generic_source_scheme_for_source:
    Proof.context -> serial -> term -> (typ option * Position.T) list -> term option
  val resolve_source_arguments:
    Proof.context -> generic_source_parameter list -> URust_AST.rust_generic_argument list ->
      {arguments: (typ option * Position.T) list, identities: string list}
  val generic_scheme: Proof.context -> term -> generic_scheme_parameter list option
  val generic_scheme_for_source:
    Proof.context -> serial -> generic_scheme_parameter list option
  val register_generic_scheme:
    {identity: term, backend: term, sources: serial list,
     parameters: generic_scheme_parameter list, pos: Position.T} ->
      local_theory -> local_theory
  val instantiate_generic_scheme:
    Proof.context -> term -> term -> (typ * Position.T) list -> term option
  val instantiate_generic_scheme_for_source:
    Proof.context -> serial -> term -> (typ * Position.T) list -> term option

  val entry_template: entry -> typ
  val entry_arities: entry -> int list
  val entry_parameter_sorts: entry -> sort list
  val entry_parameter_kinds: entry -> URust_AST.generic_parameter_kind list
  val entry_erased_parameters: entry -> int list
  val entry_backend_parameter_sorts: entry -> sort list
  (* Role-aware schemes preserve singleton identity. Legacy positional registration APIs accept
     the empty scheme or the established address/global pair. *)
  val entry_backend_roles: entry -> backend_role list
  val entry_declaration_position: entry -> Position.T
  val entry_origin: entry -> string
  val entry_identity: entry -> serial
  val report_reference: Proof.context -> Position.T -> string -> entry -> unit

  val preflight_generated:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string} ->
    local_theory -> unit
  val register_generated:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string} ->
    local_theory -> local_theory
  val preflight_generated_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, backend_parameters: (string * sort) list} ->
    local_theory -> unit
  val register_generated_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, backend_parameters: (string * sort) list} ->
    local_theory -> local_theory
  type callable_origin =
    {path: string, identity: serial, declaration_pos: Position.T, bound_pos: Position.T}
  type callable_recipe =
    {origin: callable_origin, inputs: URust_AST.rust_type list,
     output: URust_AST.rust_type option}
  type binding_spec =
    {parameter: generic_parameter,
     declaration: generic_declaration_identity,
     callables: callable_recipe list}
  type computation_channels = {state: typ, abort: typ, input: typ, output: typ}
  type callable_relation =
    {inputs: (typ * source_identity) list,
     result: typ * source_identity, channels: computation_channels}
  type generic_binding
  type binding_scope
  type binding_events
  val prepare_binding_scope: binding_spec list -> Proof.context -> binding_scope
  val binding_scope: Proof.context -> binding_scope option
  val with_binding_scope: binding_scope -> Proof.context -> Proof.context
  val scope_bindings: binding_scope -> generic_binding list
  val binding_spec: generic_binding -> binding_spec
  val binding_template: generic_binding -> typ option
  val binding_callable_relation: generic_binding -> callable_relation option
  val binding_available: Proof.context -> generic_binding -> bool
  val binding_has_witness: Proof.context -> generic_binding -> bool
  val with_binding_availability:
    {unavailable: serial list, source_only: serial list, declared_body: bool} ->
      Proof.context -> Proof.context
  val report_binding_reference:
    Proof.context -> generic_binding -> {witness: bool, pos: Position.T} -> unit
  val capture_binding_events:
    Proof.context -> (Proof.context -> 'a) -> 'a * binding_events
  val capture_binding_argument_events:
    Proof.context -> (Proof.context -> 'a) -> 'a * binding_events
  val binding_event_declarations:
    binding_events -> {source_uses: serial list, witness_uses: serial list}
  val replay_binding_argument_events: Proof.context -> binding_events -> unit
  val observe_binding_syntax_types: Proof.context -> typ list -> unit
  val with_binding_type_aliases: Proof.context -> Proof.context

  val binding_signature_events: binding_scope -> binding_events

  val resolve_function_signature_with_bindings:
    Proof.context -> function_channels -> URust_AST.rust_lifetime list ->
      URust_AST.rust_type list -> URust_AST.rust_type -> {typ: typ, scope: binding_scope}

  type binding_scheme_parameter =
    {rust: string, kind: URust_AST.generic_parameter_kind, declaration: serial, hol_name: string,
     witness: typ option, sort: sort, bounds: string list, callable_origins: callable_origin list,
     callable_relation: callable_relation option, source_used: bool option}
  type binding_impl_scheme =
    {parameters: binding_scheme_parameter list, declarations: generic_declaration_identity list,
     target: Micro_Rust_Names.target_template}
  type binding_scheme_registration =
    {identity: term, backend: term, sources: serial list, owner: binding_impl_scheme option,
     parameters: binding_scheme_parameter list, pos: Position.T}
  type binding_generic_scheme
  val register_binding_generic_source_scheme:
    binding_scheme_registration -> local_theory -> local_theory
  val binding_generic_scheme_for_source: Proof.context -> serial -> binding_generic_scheme option
  val binding_scheme_is_canonical: binding_generic_scheme -> bool
  val binding_generic_schemes_for_source: Proof.context -> serial -> binding_generic_scheme list
  val binding_generic_scheme: Proof.context -> term -> binding_generic_scheme option
  val binding_scoped_owner: binding_generic_scheme -> binding_impl_scheme option
  val binding_scoped_parameters: binding_generic_scheme -> binding_scheme_parameter list
  val instantiate_binding_generic_scheme_for_source:
    Proof.context -> serial -> term ->
      {target: Micro_Rust_Names.target_selection option,
       arguments: (typ option * Position.T) list option} -> term option
  val resolve_binding_source_arguments:
    Proof.context -> binding_scheme_parameter list -> URust_AST.rust_generic_argument list ->
      {arguments: (typ option * Position.T) list, identities: string list}
  val resolve_impl_target_selection_with_bindings:
    Proof.context -> URust_AST.rust_type ->
      {self: impl_self, source: source_identity option,
       selection: Micro_Rust_Names.target_selection, scope: binding_scope}
  val prepare_binding_target_selection:
    Proof.context -> serial -> Micro_Rust_Names.target_selection -> Micro_Rust_Names.target_selection
  val register_binding_generic_source_scheme_with_templates:
    binding_scheme_registration ->
      {owner: (generic_declaration_identity * typ) list,
       parameters: (generic_declaration_identity * typ) list} -> local_theory -> local_theory
  val register_binding_generic_source_scheme_with_ambient_templates:
    binding_scheme_registration ->
      {owner: (generic_declaration_identity * typ) list,
       parameters: (generic_declaration_identity * typ) list,
       ambient: generic_declaration_identity list} -> local_theory -> local_theory
  val instantiate_binding_source_arguments_for_source:
    Proof.context -> serial -> term -> typ ->
      {target: Micro_Rust_Names.target_selection option,
       arguments: URust_AST.rust_generic_argument list option} -> term option

end

structure URust_Type_Mappings :> URUST_TYPE_MAPPINGS =
struct
  open URust_AST
  structure Navigation = Micro_Rust_Semantic_Navigation

  val mappingN = "micro_rust_type_mapping"

  datatype backend_role = datatype URust_Model_Parameters.role
  structure Models = URust_Model_Parameters
  val role_name = Models.name
  val role_order = Models.order

  datatype origin =
      Manual
    | Generated of string
    | Alias

  (* Rust identity is independent of HOL equality: i32/u32, pointer
     mutability, references versus raw pointers, and an arbitrary mapping to
     a word remain distinct. Alias
     dependencies are expanded once, when declared. Mapped nodes retain
     the dependency scheme so locale morphisms also reach captured meaning,
     and the exact registry key of the nominal type they denote, so an alias
     expansion names its final target. *)
  datatype meaning =
      Meaning_Parameter of int
    | Meaning_Const_Parameter of int
    | Meaning_Scoped_Parameter of serial * generic_parameter_kind
    | Meaning_Primitive of rust_primitive_type
    | Meaning_Mapped of string * typ * sort list * int list * (backend_role * sort) list * meaning list
    | Meaning_Opaque of (string * meaning list) list
    | Meaning_Numeric of int
    | Meaning_Tuple of meaning list
    | Meaning_Slice of meaning
    | Meaning_Array of meaning * meaning
    | Meaning_Pointer of raw_pointer_mutability * meaning
    | Meaning_Reference of borrow_mode * meaning
    | Meaning_HOL of typ

  type key =
    {base: string,
     segment_arities: int list,
     parameter_kinds: generic_parameter_kind list,
     parameters: string list,
     parameter_positions: Position.T list}

  datatype shared_policy = Shared_Value | Shared_Reference | Shared_Readonly

  fun shared_policy_name Shared_Value = "value"
    | shared_policy_name Shared_Reference = "reference"
    | shared_policy_name Shared_Readonly = "readonly"

  fun read_shared_policy ctxt source =
    let
      val pos = Input.pos_of source
      val policy =
        (case Symbol.trim_blanks (Input.string_of source) of
           "value" => Shared_Value
         | "reference" => Shared_Reference
         | "readonly" => Shared_Readonly
         | _ => error ("urust: shared representation expects value, reference, or readonly" ^
             Position.here pos))
      val _ = Navigation.defer_report ctxt pos Markup.keyword2
    in (policy, pos) end

  type entry =
    {segment_arities: int list,
     template: typ,
     parameter_kinds: generic_parameter_kind list,
     parameter_sorts: sort list,
     erased_parameters: int list,
     backend_roles: backend_role list,
     backend_parameter_sorts: sort list,
     meaning: meaning,
     dependencies: string list,
      shared_policy: (shared_policy * Position.T) option,
     declaration_pos: Position.T,
     origin: origin,
     identity: serial}

  fun entry_template ({template, ...}: entry) = template
  fun entry_arities ({segment_arities, ...}: entry) = segment_arities
  fun entry_parameter_sorts ({parameter_sorts, ...}: entry) =
    parameter_sorts
  fun entry_parameter_kinds ({parameter_kinds, ...}: entry) = parameter_kinds
  fun entry_erased_parameters ({erased_parameters, ...}: entry) = erased_parameters
  fun entry_backend_parameter_sorts
      ({backend_parameter_sorts, ...}: entry) =
    backend_parameter_sorts
  fun entry_backend_roles ({backend_roles, ...}: entry) = backend_roles
  fun entry_declaration_position ({declaration_pos, ...}: entry) =
    declaration_pos
  fun entry_identity ({identity, ...}: entry) = identity
  fun entry_shared_policy ({shared_policy, ...}: entry) = shared_policy

  fun origin_text Manual = "urust_type declaration"
    | origin_text (Generated hol_type_name) =
        "generated datatype " ^ quote hol_type_name
    | origin_text Alias = "urust_type_alias declaration"

  fun alias_origin Alias = true
    | alias_origin _ = false

  fun entry_origin ({origin, ...}: entry) = origin_text origin

  fun same_entry_schema
      (left as {segment_arities = left_arities,
        template = left_template,
        parameter_sorts = left_sorts,
        backend_parameter_sorts = left_backend,
        meaning = left_meaning, origin = left_origin, ...}: entry,
       right as {segment_arities = right_arities,
        template = right_template,
        parameter_sorts = right_sorts,
        backend_parameter_sorts = right_backend,
        meaning = right_meaning, origin = right_origin, ...}: entry) =
    left_arities = right_arities andalso
    left_template = right_template andalso
    #parameter_kinds left = #parameter_kinds right andalso
    left_sorts = right_sorts andalso
    #erased_parameters left = #erased_parameters right andalso
    #backend_roles left = #backend_roles right andalso
    left_backend = right_backend andalso
    alias_origin left_origin = alias_origin right_origin andalso
    (not (alias_origin left_origin) orelse left_meaning = right_meaning)

  fun ordered_entries (left: entry, right: entry) =
    if #identity left <= #identity right then (left, right)
    else (right, left)

  fun conflict base reason (left: entry, right: entry) =
    let
      val (first, second) = ordered_entries (left, right)
    in
      error
        ("urust_type: conflicting active mappings for " ^ quote base ^
          " (" ^ reason ^ ")\n  " ^
          origin_text (#origin first) ^
          Position.here (#declaration_pos first) ^ "\n  " ^
          origin_text (#origin second) ^
          Position.here (#declaration_pos second))
    end

  fun replace_shared_policy shared_policy
      ({segment_arities, template, parameter_kinds, parameter_sorts, erased_parameters,
        backend_roles, backend_parameter_sorts, meaning, dependencies,
        declaration_pos, origin, identity, ...}: entry) =
    {segment_arities = segment_arities, template = template,
     parameter_kinds = parameter_kinds, parameter_sorts = parameter_sorts,
     erased_parameters = erased_parameters, backend_roles = backend_roles,
     backend_parameter_sorts = backend_parameter_sorts, meaning = meaning,
     dependencies = dependencies, shared_policy = shared_policy,
     declaration_pos = declaration_pos, origin = origin, identity = identity}: entry

  fun join_shared_policy base (NONE, selected) = selected
    | join_shared_policy _ (selected, NONE) = selected
    | join_shared_policy base (SOME (left, left_pos), SOME (right, right_pos)) =
        if left = right then
          SOME (left,
            if list_ord (prod_ord fast_string_ord fast_string_ord)
                (Position.properties_of left_pos, Position.properties_of right_pos) <> GREATER
            then left_pos else right_pos)
        else error ("urust_type: conflicting shared representations for " ^ quote base ^
          "\n  " ^ shared_policy_name left ^ Position.here left_pos ^
          "\n  " ^ shared_policy_name right ^ Position.here right_pos)

  fun join_entry base (left: entry, right: entry) =
    if same_entry_schema (left, right)
    then replace_shared_policy
      (join_shared_policy base (#shared_policy left, #shared_policy right))
      (#1 (ordered_entries (left, right)))
    else if alias_origin (#origin left) <> alias_origin (#origin right)
    then conflict base "alias and direct/generated mapping collide" (left, right)
    else if #segment_arities left <> #segment_arities right orelse
        length (#parameter_sorts left) <> length (#parameter_sorts right)
    then conflict base "different generic arity" (left, right)
    else conflict base "different Rust meanings, HOL templates or parameter sorts"
      (left, right)

  structure Data = Generic_Data
  (
    type T = entry Symtab.table
    val empty = Symtab.empty
    fun merge (left, right) =
      Symtab.join join_entry (left, right)
  )

  fun lookup ctxt base =
    Symtab.lookup (Data.get (Context.Proof ctxt)) base

  fun dump ctxt =
    Symtab.dest (Data.get (Context.Proof ctxt))

  (* Alternatives never enter the default mapping table. Their source schema is checked
     against that table, while their own template determines retained witnesses and sorts. *)
  type representation_entry = {entry: entry, name_pos: Position.T}
  structure Representations = Generic_Data
  (
    type T = representation_entry Symtab.table Symtab.table
    val empty = Symtab.empty
    fun merge tables = Symtab.join
      (fn base => fn views => Symtab.join
        (fn name => fn (left: representation_entry, right: representation_entry) =>
          let
            val entry = join_entry (base ^ " representation " ^ quote name)
              (#entry left, #entry right)
            val name_pos = if #identity (#entry left) <= #identity (#entry right)
              then #name_pos left else #name_pos right
          in {entry = entry, name_pos = name_pos} end) views) tables
  )

  fun representation_entry ctxt base name =
    Option.mapPartial (fn views => Symtab.lookup views name)
      (Symtab.lookup (Representations.get (Context.Proof ctxt)) base)

  fun lookup_representation ctxt base name =
    Option.map #entry (representation_entry ctxt base name)

  fun dump_representations ctxt =
    maps (fn (base, views) => map (fn (name, {entry, ...}) =>
      ((base, name), entry)) (Symtab.dest views))
      (Symtab.dest (Representations.get (Context.Proof ctxt)))

  type field_representation =
    {source_head: string, representation: string, declaration_pos: Position.T,
     declaration_identity: serial}

  (* Alias recipes are captured only after the ordinary alias declaration has checked.
     Imports are canonicalized there, and HOL escapes retain checked types through morphisms.
     Selection expands only an alias's outer source type, then uses the ordinary resolver. *)
  type alias_recipe =
    {parameters: string list, rhs: rust_type, escapes: (Input.source * typ) list,
     identity: serial}
  structure Alias_Recipes = Generic_Data
  (
    type T = alias_recipe Symtab.table
    val empty = Symtab.empty
    (* Data.join_entry rejects incompatible alias schemes and retains the smaller identity.
       Keep the corresponding checked recipe, rather than combining its captured evidence. *)
    fun merge tables = Symtab.join
      (fn _ => fn (left: alias_recipe, right: alias_recipe) =>
        if #identity left <= #identity right then left else right) tables
  )

  fun model_parameter_requirements ctxt =
    maps (fn (_, entry: entry) =>
      #backend_roles entry ~~ #backend_parameter_sorts entry)
      (dump ctxt @ map (apfst fst) (dump_representations ctxt))

  fun with_model_parameters renames ctxt =
    Models.with_bindings (model_parameter_requirements ctxt) renames ctxt

  fun model_parameters_declaration ctxt =
    Models.declaration (model_parameter_requirements ctxt) ctxt

  fun inherit_model_parameters ctxt =
    Models.inherit ctxt #> Models.inherit_ambient ctxt
  val without_model_parameters = Models.without_bindings

  val with_ambient_type_parameters = Models.with_ambient

  fun ambient_parameter_sort ctxt rust required =
    (case Models.ambient ctxt rust of
      NONE => required
    | SOME {typ = TFree (_, sort), pos} =>
        (Models.satisfies ctxt ("ambient type parameter " ^ quote rust)
          (TFree ("'ambient", sort)) required pos; sort)
    | SOME _ => raise Fail "checked ambient parameter is not a free type")

  fun add_entry base entry =
    Data.map
      (fn table =>
        (case Symtab.lookup table base of
           NONE => Symtab.update (base, entry) table
         | SOME active =>
             Symtab.update
               (base, join_entry base (active, entry))
               table))

  fun mapping_error message pos =
    error ("urust_type: " ^ message ^ Position.here pos)

  fun ascii_letter character =
    (#"A" <= character andalso character <= #"Z") orelse
    (#"a" <= character andalso character <= #"z")

  fun identifier_start character =
    ascii_letter character orelse character = #"_"

  fun identifier_rest character =
    identifier_start character orelse Char.isDigit character orelse
    character = #"'"

  fun parse_mapping_key (raw, pos) source_symbols =
    let
      val input = raw
      val input_size = size input
      val symbols = Vector.fromList source_symbols
      val offset = Unsynchronized.ref 0

      fun fail detail =
        mapping_error
          ("malformed Rust type key " ^ quote raw ^ " (" ^ detail ^ ")")
          pos

      fun at_end () = !offset >= input_size
      fun current () =
        if at_end () then NONE else SOME (String.sub (input, !offset))
      fun advance () = offset := !offset + 1
      fun skip_blanks () =
        (case current () of
           SOME character =>
             if Char.isSpace character
             then (advance (); skip_blanks ())
             else ()
         | NONE => ())
      fun accept character =
        (skip_blanks ();
         case current () of
           SOME actual =>
             if actual = character
             then (advance (); true)
             else false
         | NONE => false)
      fun require character expected =
        if accept character then ()
        else fail ("expected " ^ expected)
      fun source_position start stop =
        if start < stop andalso stop <= Vector.length symbols
        then
          let
            val (_, start_pos) = Vector.sub (symbols, start)
            val (last_symbol, last_pos) =
              Vector.sub (symbols, stop - 1)
          in
            Position.range_position
              (Position.range
                (start_pos, Position.symbol last_symbol last_pos))
          end
        else Position.none
      fun accept_double_colon () =
        let
          val _ = skip_blanks ()
        in
          if !offset + 1 < input_size andalso
              String.sub (input, !offset) = #":" andalso
              String.sub (input, !offset + 1) = #":"
          then (offset := !offset + 2; true)
          else false
        end

      fun identifier description =
        let
          val _ = skip_blanks ()
          val start = !offset
          val _ =
            (case current () of
               SOME character =>
                 if identifier_start character
                 then advance ()
                 else fail ("expected " ^ description)
             | NONE => fail ("expected " ^ description))
          fun rest () =
            (case current () of
               SOME character =>
                 if identifier_rest character
                 then (advance (); rest ())
                 else ()
             | NONE => ())
          val _ = rest ()
        in String.substring (input, start, !offset - start) end

      fun placeholder () =
        let
          val _ = skip_blanks ()
          val kind =
            if !offset + 5 <= input_size andalso
               String.substring (input, !offset, 5) = "const" then
              (offset := !offset + 5; skip_blanks (); Const_Parameter)
            else Type_Parameter
          val start = !offset
          val _ = require #"'" "a mapping placeholder such as 'a"
          val parameter = "'" ^ identifier "a placeholder name"
        in ((parameter, source_position start (!offset)), kind) end

      fun placeholders () =
        let
          val first = placeholder ()
          fun more parameters =
            if accept #","
            then
              (skip_blanks ();
               if accept #">"
               then (rev parameters, true)
               else more (placeholder () :: parameters))
            else (rev parameters, false)
          val (parameters, closed) = more [first]
          val _ = if closed then () else require #">" "`>`"
        in parameters end

      fun segment () =
        let
          val name = identifier "a Rust path segment"
          val parameters =
            if accept #"<" then placeholders () else []
        in (name, parameters) end

      fun path segments =
        let
          val next = segment ()
          val segments' = next :: segments
        in
          if accept_double_colon ()
          then path segments'
          else rev segments'
        end

      val special =
        if Symbol.trim_blanks input = "()"
        then SOME ("()", [0], [])
        else if Symbol.trim_blanks input = "!"
        then SOME ("!", [0], [])
        else NONE
      val (base, arities, parameters) =
        (case special of
           SOME result => result
         | NONE =>
             let
               val segments = path []
               val _ =
                 (skip_blanks ();
                  if at_end () then ()
                  else fail "unexpected trailing input")
               val names = map fst segments
               val _ =
                 (case
                   Micro_Rust_Names.reserved_key_segment {bare_self = false}
                     (space_implode "::" names) of
                    SOME segment => fail (Micro_Rust_Names.reserved_key_message segment)
                  | NONE => ())
               val parameter_rows = map snd segments
             in
               (space_implode "::" names,
                map length parameter_rows,
                flat parameter_rows)
             end)
      val _ =
        if length parameters =
            length (distinct (op =) (map (fst o fst) parameters))
        then ()
        else fail "mapping placeholders must be distinct"
    in
      {base = base,
       segment_arities = arities,
       parameter_kinds = map snd parameters,
       parameters = map (fst o fst) parameters,
       parameter_positions = map (snd o fst) parameters}: key
    end

  fun parse_mapping_key_source source =
    parse_mapping_key
      (Input.source_content source)
      (Input.source_explode source)

  fun parse_mapping_key_text raw_position =
    parse_mapping_key raw_position []

  fun canonical_parameter index sort =
    TVar (("_urust_type", index), sort)

  fun canonical_backend_parameter role sort =
    TVar (Models.canonical role, sort)

  (* A native locale export may rename schematic indexes and basenames. Transport the
     template and all slot witnesses as one type, then restore canonical identities from
     those transported witnesses. Transforming witnesses separately loses their sharing. *)
  fun morph_scheme phi template parameter_sorts erased_parameters role_sorts =
    let
      val retained = map_index I parameter_sorts
        |> filter_out (fn (index, _) => member (op =) erased_parameters index)
      val parameters = map (fn (index, sort) => canonical_parameter index sort) retained
      val roles = map (fn (role, sort) => canonical_backend_parameter role sort)
        role_sorts
      val transported =
        Morphism.typ phi ((template :: parameters @ roles) ---> propT)
        |> binder_types
      val _ =
        if length transported = 1 + length parameters + length roles then ()
        else raise Fail "uRust type registry: malformed transported scheme"
      val transformed = hd transported
      val witnesses = tl transported
      fun witness_sort (TFree (_, sort)) = sort
        | witness_sort (TVar (_, sort)) = sort
        | witness_sort _ =
            raise Fail "uRust type registry: morphism specialized a scheme parameter"
      val sorts = map witness_sort witnesses
      val (retained_sorts, backend_sorts') = chop (length parameters) sorts
      val transported_sorts = map fst retained ~~ retained_sorts
      val parameter_sorts' = map_index (fn (index, sort) =>
        the_default sort (AList.lookup (op =) transported_sorts index)) parameter_sorts
      val role_sorts' = map fst role_sorts ~~ backend_sorts'
      val restored =
        map (fn (index, sort) => canonical_parameter index sort) transported_sorts @
        map (fn (role, sort) => canonical_backend_parameter role sort) role_sorts'
    in
      (Term.typ_subst_atomic (witnesses ~~ restored) transformed,
       parameter_sorts', role_sorts')
    end

  fun primitive_meaning base =
    get_first
      (fn primitive =>
        if rust_primitive_name primitive = base then SOME primitive else NONE)
      [DPT_U8, DPT_U16, DPT_U32, DPT_U64, DPT_U128, DPT_Usize,
       DPT_I8, DPT_I16, DPT_I32, DPT_I64, DPT_I128, DPT_Isize,
       DPT_Bool, DPT_Char, DPT_Str, DPT_Never, DPT_Unit]

  fun mapped_meaning base template parameter_sorts erased_parameters backend_sorts =
    (case primitive_meaning base of
       SOME primitive => Meaning_Primitive primitive
     | NONE =>
         Meaning_Mapped (base, template, parameter_sorts, erased_parameters, backend_sorts,
           map_index (fn (index, _) => Meaning_Parameter index)
             parameter_sorts))

  fun morph_meaning phi =
    let
      fun morph (Meaning_Parameter index) = Meaning_Parameter index
        | morph (Meaning_Const_Parameter index) = Meaning_Const_Parameter index
        | morph (Meaning_Scoped_Parameter parameter) = Meaning_Scoped_Parameter parameter
        | morph (Meaning_Primitive primitive) = Meaning_Primitive primitive
        | morph (Meaning_Mapped (base, template, sorts, erased, backend_sorts, arguments)) =
            let val (template', sorts', backend_sorts') =
              morph_scheme phi template sorts erased backend_sorts
            in Meaning_Mapped
              (base, template', sorts', erased, backend_sorts', map morph arguments) end
        | morph (Meaning_Opaque rows) = Meaning_Opaque (map (apsnd (map morph)) rows)
        | morph (Meaning_Numeric n) = Meaning_Numeric n
        | morph (Meaning_Tuple types) = Meaning_Tuple (map morph types)
        | morph (Meaning_Slice element) = Meaning_Slice (morph element)
        | morph (Meaning_Array (element, length)) = Meaning_Array (morph element, morph length)
        | morph (Meaning_Pointer (mutability, typ)) =
            Meaning_Pointer (mutability, morph typ)
        | morph (Meaning_Reference (mode, typ)) =
            Meaning_Reference (mode, morph typ)
        | morph (Meaning_HOL typ) = Meaning_HOL (Morphism.typ phi typ)
    in morph end

  fun instantiate_meaning arguments =
    let
      fun instantiate (Meaning_Parameter index) = nth arguments index
        | instantiate (Meaning_Const_Parameter index) = nth arguments index
        | instantiate (Meaning_Scoped_Parameter parameter) = Meaning_Scoped_Parameter parameter
        | instantiate (Meaning_Primitive primitive) =
            Meaning_Primitive primitive
        | instantiate (Meaning_Mapped (base, template, sorts, erased, backend_sorts, types)) =
            Meaning_Mapped
              (base, template, sorts, erased, backend_sorts, map instantiate types)
        | instantiate (Meaning_Opaque rows) = Meaning_Opaque (map (apsnd (map instantiate)) rows)
        | instantiate (Meaning_Numeric n) = Meaning_Numeric n
        | instantiate (Meaning_Tuple types) =
            Meaning_Tuple (map instantiate types)
        | instantiate (Meaning_Slice element) = Meaning_Slice (instantiate element)
        | instantiate (Meaning_Array (element, length)) =
            Meaning_Array (instantiate element, instantiate length)
        | instantiate (Meaning_Pointer (mutability, typ)) =
            Meaning_Pointer (mutability, instantiate typ)
        | instantiate (Meaning_Reference (mode, typ)) =
            Meaning_Reference (mode, instantiate typ)
        | instantiate (Meaning_HOL typ) = Meaning_HOL typ
    in instantiate end

  type source_identity = meaning
  val morph_source_identity = morph_meaning

  structure Source_Resolution_Trace = Proof_Data
  (
    type T = (meaning * typ option * rust_generic_argument) list Unsynchronized.ref option
    fun init _ = NONE
  )

  structure Source_Resolution_Origins = Proof_Data
  (
    type T = (Position.T * (int list * rust_generic_argument) list) list Unsynchronized.ref option
    fun init _ = NONE
  )

  fun argument_origin (Rust_Type_Argument typ) = rust_type_position typ
    | argument_origin (Rust_Numeric_Argument integer) = integer_literal_position integer
    | argument_origin (Rust_Lifetime_Argument (Rust_Lifetime (_, pos))) = pos
    | argument_origin (Rust_Associated_Type_Argument (_, pos, _)) = pos
    | argument_origin (Rust_Const_Expression_Argument source) = Input.pos_of source

  fun same_origin (left, right) = Position.properties_of left = Position.properties_of right

  fun meaning_children (Meaning_Mapped (_, _, _, _, _, arguments)) = arguments
    | meaning_children (Meaning_Opaque rows) = maps snd rows
    | meaning_children (Meaning_Tuple types) = types
    | meaning_children (Meaning_Slice element) = [element]
    | meaning_children (Meaning_Array (element, length)) = [element, length]
    | meaning_children (Meaning_Pointer (_, typ)) = [typ]
    | meaning_children (Meaning_Reference (_, typ)) = [typ]
    | meaning_children _ = []

  (* Use the actual mapping template at the authoritative substitution point. Equal source
     values in distinct slots retain their own origins, even through reordered aliases. *)
  fun note_instantiated_origins ctxt pos template arguments =
    Option.app (fn origins =>
      let
        fun argument index =
          let val source = nth arguments index
              val nested = the_default [] (AList.lookup same_origin (!origins) (argument_origin source))
          in ([], source) :: filter (not o null o fst) nested end
        fun visit path (Meaning_Parameter index) = map (apfst (append path)) (argument index)
          | visit path (Meaning_Const_Parameter index) = map (apfst (append path)) (argument index)
          | visit path meaning = maps (fn (index, child) => visit (path @ [index]) child)
              (map_index I (meaning_children meaning))
      in origins := AList.update same_origin (pos, visit [] template) (!origins) end)
      (Source_Resolution_Origins.get ctxt)

  fun note_source_resolution ctxt meaning evidence argument =
    Option.app (fn trace => trace := (meaning, evidence, argument) :: !trace)
      (Source_Resolution_Trace.get ctxt)

  fun inherit_source_origins ctxt inner outer =
    Option.app (fn origins =>
      case AList.lookup same_origin (!origins) inner of
        NONE => ()
      | SOME associated => origins := AList.update same_origin (outer, associated) (!origins))
      (Source_Resolution_Origins.get ctxt)

  (* The key names expanded source structure, never the HOL representation of an erased slot.
     HOL escapes remain typed identities; the associated owner separately checks its full Self
     type. Length prefixes in XML keep qualified names and nested arguments unambiguous. *)
  fun source_identity_name meaning =
    let
      fun node name attrs children = XML.Elem ((name, attrs), children)
      fun encode (Meaning_Parameter index) = node "parameter" [("index", string_of_int index)] []
        | encode (Meaning_Const_Parameter index) = node "const" [("index", string_of_int index)] []
        | encode (Meaning_Scoped_Parameter (identity, kind)) =
            node "scope" [("identity", string_of_int identity),
              ("kind", if kind = Type_Parameter then "type" else "const")] []
        | encode (Meaning_Primitive primitive) =
            node "primitive" [("name", rust_primitive_name primitive)] []
        | encode (Meaning_Mapped (base, _, _, _, _, arguments)) =
            node "mapped" [("name", base)] (map encode arguments)
        | encode (Meaning_Opaque rows) = node "opaque" []
            (map (fn (name, arguments) => node "segment" [("name", name)] (map encode arguments)) rows)
        | encode (Meaning_Numeric value) = node "numeric" [("value", string_of_int value)] []
        | encode (Meaning_Tuple types) = node "tuple" [] (map encode types)
        | encode (Meaning_Slice element) = node "slice" [] [encode element]
        | encode (Meaning_Array (element, length)) = node "array" [] [encode element, encode length]
        | encode (Meaning_Pointer (mutability, typ)) =
            node "pointer" [("mutable", Bool.toString (mutability = RPM_Mut))] [encode typ]
        | encode (Meaning_Reference (mode, typ)) =
            node "reference" [("mutable", Bool.toString (mode = BM_Mut))] [encode typ]
        | encode (Meaning_HOL typ) = node "hol" [] (Term_XML.Encode.typ typ)
    in XML.string_of (encode meaning) end

  fun identity_sensitive (Meaning_Mapped (_, _, _, erased, _, arguments)) =
        not (null erased) orelse exists identity_sensitive arguments
    | identity_sensitive (Meaning_Opaque _) = true
    | identity_sensitive (Meaning_Tuple types) = exists identity_sensitive types
    | identity_sensitive (Meaning_Slice element) = identity_sensitive element
    | identity_sensitive (Meaning_Array (element, length)) =
        identity_sensitive element orelse identity_sensitive length
    | identity_sensitive (Meaning_Pointer (_, typ)) = identity_sensitive typ
    | identity_sensitive (Meaning_Reference (_, typ)) = identity_sensitive typ
    | identity_sensitive _ = false

  (* Mapped templates have their own canonical scheme variables. Only authored HOL leaves
     belong to the surrounding signature inference state and need its final substitution. *)
  fun finish_meaning finish =
    let
      fun finish_source (Meaning_Mapped (base, template, sorts, erased, roles, arguments)) =
            Meaning_Mapped (base, template, sorts, erased, roles, map finish_source arguments)
        | finish_source (Meaning_Opaque rows) =
            Meaning_Opaque (map (apsnd (map finish_source)) rows)
        | finish_source (Meaning_Tuple types) = Meaning_Tuple (map finish_source types)
        | finish_source (Meaning_Slice element) = Meaning_Slice (finish_source element)
        | finish_source (Meaning_Array (element, length)) =
            Meaning_Array (finish_source element, finish_source length)
        | finish_source (Meaning_Pointer (mode, typ)) = Meaning_Pointer (mode, finish_source typ)
        | finish_source (Meaning_Reference (mode, typ)) = Meaning_Reference (mode, finish_source typ)
        | finish_source (Meaning_HOL typ) = Meaning_HOL (the_single (finish [typ]))
        | finish_source meaning = meaning
    in finish_source end

  fun read_role_variables lthy source role =
    let
      fun read ctxt =
        let
          val keywords = Thy_Header.get_keywords' ctxt
          val tokens =
            Token.tokenize keywords {strict = true} (Input.source_explode source)
            |> filter Token.is_proper
          val _ = Context_Position.reports_text ctxt (maps (Token.reports keywords) tokens)
          val parser =
            Parse.enum ","
              (Parse.position Parse.name --| Parse.$$$ "=" -- Parse.position Parse.type_ident)
              --| Scan.ahead Parse.eof
        in
          (case Scan.read Token.stopper (Parse.!!! parser) tokens of
             SOME bindings => bindings
           | NONE => mapping_error "malformed implicit role bindings" (Input.pos_of source))
        end
      val bindings = URust_Report_Transaction.native lthy read
      val roles = map (fn (name, variable) => (role name, variable, snd name)) bindings
      fun distinct_binding (role, (name, pos), role_pos) (seen_roles, seen_names) =
        if member (op =) seen_roles role then
          mapping_error ("duplicate implicit role " ^ quote (role_name role)) role_pos
        else if member (op =) seen_names name then
          mapping_error ("duplicate implicit template variable " ^ quote name) pos
        else (role :: seen_roles, name :: seen_names)
      val _ = fold distinct_binding roles ([], [])
    in map (fn (role, variable, _) => (role, variable)) roles end

  fun read_implicit_roles lthy source =
    read_role_variables lthy source (fn (name, pos) =>
      case name of "address" => Address | "global" => Global
      | _ => mapping_error ("unknown implicit role " ^ quote name) pos)

  fun read_model_roles lthy source =
    read_role_variables lthy source (fn (name, pos) =>
      if member (op =) ["address", "global"] name then
        mapping_error ("model family " ^ quote name ^ " is a reserved backend role") pos
      else if name <> "" andalso identifier_start (String.sub (name, 0)) andalso
          forall identifier_rest (String.explode name) then Model name
      else mapping_error ("invalid model family " ^ quote name) pos)

  fun read_erased_parameters lthy source =
    let
      fun read ctxt =
        let
          val keywords = Thy_Header.get_keywords' ctxt
          val tokens = Token.tokenize keywords {strict = true} (Input.source_explode source)
            |> filter Token.is_proper
          val _ = Context_Position.reports_text ctxt (maps (Token.reports keywords) tokens)
          val parser = Parse.enum "," (Parse.position Parse.type_ident) --| Scan.ahead Parse.eof
        in
          case Scan.read Token.stopper (Parse.!!! parser) tokens of
            SOME parameters => parameters
          | NONE => mapping_error "malformed erased placeholder list" (Input.pos_of source)
        end
      val parameters = URust_Report_Transaction.native lthy read
      fun distinct_parameter (name, pos) seen =
        if member (op =) seen name then mapping_error ("duplicate erased placeholder " ^ quote name) pos
        else name :: seen
      val _ = fold distinct_parameter parameters []
    in parameters end

  fun checked_template lthy
      ({parameters, ...}: key) roles erased source =
    let
      val pos = Input.pos_of source
      val typ =
        (case Exn.result
            (fn () =>
              URust_Report_Transaction.native lthy
                (fn ctxt => Syntax.read_typ ctxt (Syntax.implode_input source))) () of
           Exn.Res typ => typ
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else error (Runtime.exn_message exn ^ Position.here pos))
      val _ =
        if null (Term.add_tvarsT typ []) then ()
        else mapping_error
          "schematic type variables are not supported in HOL templates"
          pos
      val tfrees = Term.add_tfreesT typ []
      val tfree_names = map fst tfrees
      val role_variables = map (fst o snd) roles
      val _ = fold (fn (_, (name, pos)) => fn seen =>
        if member (op =) seen name then
          mapping_error ("duplicate implicit template variable " ^ quote name) pos
        else name :: seen) roles []
      val erased_names = map (nth parameters) erased
      val retained_names = filter_out (member (op =) erased_names) parameters
      val _ = List.app (fn name =>
        if member (op =) tfree_names name then
          mapping_error ("erased placeholder " ^ quote name ^ " occurs in the HOL template") pos
        else ()) erased_names
      val _ = List.app (fn (_, (name, pos)) =>
        if member (op =) parameters name then
          mapping_error ("implicit variable " ^ quote name ^ " is also a source placeholder") pos
        else if member (op =) tfree_names name then ()
        else mapping_error ("unused implicit variable " ^ quote name) pos) roles
      val declared_variables = retained_names @ role_variables
      val missing =
        filter_out (member (op =) tfree_names) retained_names
      val extra =
        filter_out (member (op =) declared_variables) tfree_names
      val _ =
        if null missing andalso null extra then ()
        else
          mapping_error
            ("mapping placeholders must correspond exactly to the HOL template's free type variables" ^
              (if null missing then ""
               else "; missing " ^ commas_quote missing) ^
              (if null extra then ""
               else "; undeclared " ^ commas_quote extra))
            pos
      fun parameter_sort name =
        (case AList.lookup (op =) tfrees name of
           SOME sort =>
             Sign.minimize_sort (Proof_Context.theory_of lthy) sort
         | NONE =>
             raise Fail
               "uRust type registry: validated template parameter is absent")
      val parameter_sorts = map (fn name => if member (op =) erased_names name then []
        else parameter_sort name) parameters
      val ordered_roles = role_order (map fst roles)
      val role_parameters = map (fn role =>
        let val (name, _) = the (AList.lookup (op =) roles role)
        in (role, (name, parameter_sort name)) end) ordered_roles
      val canonical = map_index I (parameters ~~ parameter_sorts)
        |> filter_out (fn (index, _) => member (op =) erased index)
        |> map (fn (index, (name, sort)) =>
          (TFree (name, sort), canonical_parameter index sort))
      val canonical = canonical @
        map (fn (role, (name, sort)) =>
          (TFree (name, sort), canonical_backend_parameter role sort))
          role_parameters
      val normalized = Term.typ_subst_atomic canonical typ
    in
      (Proof_Context.cert_typ lthy normalized, parameter_sorts,
       map (apsnd snd) role_parameters)
    end

  fun make_entry origin declaration_pos segment_arities template
      parameter_kinds parameter_sorts erased_parameters role_sorts meaning dependencies =
    {segment_arities = segment_arities,
     template = template,
     parameter_kinds = parameter_kinds,
     parameter_sorts = parameter_sorts,
     erased_parameters = erased_parameters,
     backend_roles = map fst role_sorts,
     backend_parameter_sorts = map snd role_sorts,
     meaning = meaning,
     dependencies = dependencies,
      shared_policy = NONE,
     declaration_pos = declaration_pos,
     origin = origin,
     identity = serial ()}: entry

  fun morph_entry phi
      ({segment_arities, template, parameter_kinds, parameter_sorts, erased_parameters,
        backend_roles, backend_parameter_sorts,
        meaning, dependencies, shared_policy, declaration_pos, origin, identity}: entry) =
    let
      val (template', parameter_sorts', role_sorts') =
        morph_scheme phi template parameter_sorts erased_parameters (backend_roles ~~ backend_parameter_sorts)
    in
      {segment_arities = segment_arities,
       template = template',
       parameter_kinds = parameter_kinds,
       parameter_sorts = parameter_sorts',
       erased_parameters = erased_parameters,
       backend_roles = backend_roles,
       backend_parameter_sorts = map snd role_sorts',
       meaning = morph_meaning phi meaning,
       dependencies = dependencies,
       shared_policy = shared_policy,
       declaration_pos = declaration_pos,
       origin = origin,
       identity = identity}: entry
    end

  datatype preflight =
      Existing of entry
    | Refined of entry
    | Fresh of entry

  fun preflight ctxt base (candidate: entry) =
    (case lookup ctxt base of
       NONE => Fresh candidate
     | SOME active =>
          let val joined = join_entry base (active, candidate)
          in
            (* Sequential repetition retains the first author's position; independent theory
               merges still choose their deterministic joined position. *)
            if Option.map #1 (#shared_policy active) = Option.map #1 (#shared_policy joined)
            then Existing active
            else Refined joined
          end)

  fun report_declaration ctxt base pos identity =
    (Navigation.defer_report ctxt pos
       (Position.make_entity_markup {def = true} identity mappingN
         (base, pos));
     Navigation.defer_report ctxt pos Markup.typing)

  fun install_new base (entry: entry) lthy =
    let
      val _ =
        report_declaration lthy base
          (#declaration_pos entry) (#identity entry)
    in
      Local_Theory.declaration
        {pervasive = false, syntax = true,
         pos = #declaration_pos entry}
        (fn phi => add_entry base (morph_entry phi entry))
        lthy
    end

  fun install_prepared base candidate lthy =
    (case preflight lthy base candidate of
       Existing _ => lthy
     | Refined entry =>
         Local_Theory.declaration
           {pervasive = false, syntax = true,
            pos = #2 (the (#shared_policy entry))}
           (fn phi => add_entry base (morph_entry phi entry)) lthy
     | Fresh entry => install_new base entry lthy)

  fun report_parameters ctxt
      ({parameters, parameter_positions, ...}: key) =
    List.app
      (fn (parameter, pos) =>
        Navigation.defer_report ctxt pos Markup.tfree)
      (parameters ~~ parameter_positions)

  fun mapping_candidate origin roles erased_names shared_policy (key_source, source)
      lthy =
    let
      val key as {base, segment_arities, parameter_kinds, ...} =
        parse_mapping_key_source key_source
      val key_pos = Input.pos_of key_source
      val parameters = #parameters key
      val _ = List.app (fn (name, pos) =>
        if member (op =) parameters name then ()
        else mapping_error ("unknown erased placeholder " ^ quote name) pos) erased_names
      val erased = map_index (fn (index, name) =>
        if member (op =) (map fst erased_names) name then SOME index else NONE) parameters
        |> map_filter I
      val (template, parameter_sorts, role_sorts) =
        checked_template lthy key roles erased source
      val _ = report_parameters lthy key
      val candidate =
        make_entry origin key_pos segment_arities template
          parameter_kinds parameter_sorts erased role_sorts
          (mapped_meaning base template parameter_sorts erased role_sorts) []
        |> replace_shared_policy shared_policy
    in (base, key_pos, candidate) end

  fun declare_mapping origin roles erased_names shared_policy payload lthy =
    let val (base, _, candidate) =
      mapping_candidate origin roles erased_names shared_policy payload lthy
    in install_prepared base candidate lthy end

  fun declare_representation name_source roles erased_names shared_policy payload lthy =
    let
      val name = Input.string_of name_source
      val name_pos = Input.pos_of name_source
      val _ =
        if name <> "" andalso identifier_start (String.sub (name, 0)) andalso
            forall identifier_rest (String.explode name)
        then () else mapping_error "representation names must be identifiers" name_pos
      val (base, key_pos, candidate) =
        mapping_candidate Manual roles erased_names shared_policy payload lthy
      val default =
        (case lookup lthy base of
           SOME entry => entry
         | NONE => mapping_error
             ("representation " ^ quote name ^ " requires an existing default mapping for " ^
               quote base) key_pos)
      val _ =
        if alias_origin (#origin default) then
          mapping_error "representation declarations must name a canonical nominal head, not an alias"
            key_pos
        else if #segment_arities default = #segment_arities candidate andalso
            #parameter_kinds default = #parameter_kinds candidate
        then ()
        else mapping_error
          ("representation " ^ quote name ^ " has a different source schema from " ^ quote base)
          key_pos
      val _ = Navigation.defer_report lthy key_pos
        (Position.make_entity_markup {def = false} (#identity default) mappingN
          (base, #declaration_pos default))
      fun add phi context =
        let
          val entry = morph_entry phi candidate
          val selected = {entry = entry, name_pos = name_pos}: representation_entry
          fun update views =
            (case Symtab.lookup views name of
               NONE => Symtab.update (name, selected) views
             | SOME previous =>
                 let val entry = join_entry (base ^ " representation " ^ quote name)
                   (#entry previous, entry)
                 in Symtab.update (name,
                   {entry = entry, name_pos = #name_pos previous}) views end)
        in Representations.map (Symtab.map_default (base, Symtab.empty) update) context end
      val existing = representation_entry lthy base name
      val joined = Option.map (fn previous =>
        join_entry (base ^ " representation " ^ quote name)
          (#entry previous, candidate)) existing
    in
      (case (existing, joined) of
         (SOME previous, SOME entry) =>
           if Option.map #1 (#shared_policy (#entry previous)) =
               Option.map #1 (#shared_policy entry)
           then lthy
           else Local_Theory.declaration
             {pervasive = false, syntax = true, pos = #2 (the (#shared_policy entry))}
             add lthy
       | _ =>
        (Navigation.defer_report lthy name_pos
           (Position.make_entity_markup {def = true} (#identity candidate)
             (mappingN ^ "_representation") (base ^ "::" ^ name, name_pos));
         Local_Theory.declaration
           {pervasive = false, syntax = true, pos = name_pos} add lthy))
    end

  fun generated_candidate
      {rust_name, rust_pos, hol_type_name} =
    let
      val {base, segment_arities, parameters, ...} =
        parse_mapping_key_text (rust_name, rust_pos)
      val _ =
        if null parameters then ()
        else
          mapping_error
            "generated datatypes cannot declare generic mapping placeholders"
            rust_pos
    in
      (base,
       make_entry (Generated hol_type_name) rust_pos
         segment_arities (Type (hol_type_name, [])) [] [] [] []
         (mapped_meaning base (Type (hol_type_name, [])) [] [] []) [])
    end

  fun declaration_role_scheme_candidate
      {rust_name, rust_pos, hol_type_name, hol_type,
       source_parameters, parameter_kinds, backend_parameters} =
    let
      val {base, segment_arities, parameters, ...} =
        parse_mapping_key_text (rust_name, rust_pos)
      val _ = if null parameters then () else
        mapping_error "generated type names cannot contain mapping placeholders" rust_pos
      val all_parameters = source_parameters @ map snd backend_parameters
      val roles = map fst backend_parameters
      val _ =
        if null (Term.add_tvarsT hol_type []) andalso
           length all_parameters = length (distinct (op =) (map fst all_parameters)) andalso
           eq_set (op =) (Term.add_tfreesT hol_type [], all_parameters) andalso
           length source_parameters = length parameter_kinds andalso
           length roles = length (distinct (op =) roles)
        then () else mapping_error "generated type scheme parameters are inconsistent" rust_pos
      val source_sorts = map snd source_parameters
      val role_parameters = map (fn role =>
        (role, the (AList.lookup (op =) backend_parameters role))) (role_order roles)
      val role_sorts = map (apsnd snd) role_parameters
      val substitutions =
        map_index (fn (index, parameter as (_, sort)) =>
          (TFree parameter, canonical_parameter index sort)) source_parameters @
        map (fn (role, parameter as (_, sort)) =>
          (TFree parameter, canonical_backend_parameter role sort)) role_parameters
      val template = Term.typ_subst_atomic substitutions hol_type
      val arities = take (length segment_arities - 1) segment_arities @ [length source_parameters]
    in
      (base, make_entry (Generated hol_type_name) rust_pos arities template
        parameter_kinds source_sorts [] role_sorts
        (mapped_meaning base template source_sorts [] role_sorts) [])
    end

  fun legacy_backend_parameters pos [] = []
    | legacy_backend_parameters _ [address, global] = [(Address, address), (Global, global)]
    | legacy_backend_parameters pos _ =
        mapping_error "positional backend schemes require an address/global pair; use the role-aware API"
          pos

  fun declaration_scheme_candidate
      {rust_name, rust_pos, hol_type_name, hol_type,
       source_parameters, parameter_kinds, backend_parameters} =
    declaration_role_scheme_candidate
      {rust_name = rust_name, rust_pos = rust_pos, hol_type_name = hol_type_name,
       hol_type = hol_type, source_parameters = source_parameters,
       parameter_kinds = parameter_kinds,
       backend_parameters = legacy_backend_parameters rust_pos backend_parameters}

  fun generated_scheme_candidate
      {rust_name, rust_pos, hol_type_name, hol_type, backend_parameters} =
    declaration_scheme_candidate
      {rust_name = rust_name, rust_pos = rust_pos, hol_type_name = hol_type_name,
       hol_type = hol_type, source_parameters = [], parameter_kinds = [],
       backend_parameters = backend_parameters}

  fun preflight_declaration_scheme specification lthy =
    let val (base, candidate) = declaration_scheme_candidate specification
    in ignore (preflight lthy base candidate) end

  fun register_declaration_scheme specification lthy =
    let val (base, candidate) = declaration_scheme_candidate specification
    in install_prepared base candidate lthy end

  fun preflight_declaration_role_scheme specification lthy =
    let val (base, candidate) = declaration_role_scheme_candidate specification
    in ignore (preflight lthy base candidate) end

  fun register_declaration_role_scheme specification lthy =
    let val (base, candidate) = declaration_role_scheme_candidate specification
    in install_prepared base candidate lthy end

  fun preflight_generated specification lthy =
    let
      val (base, candidate) = generated_candidate specification
    in ignore (preflight lthy base candidate) end

  fun register_generated specification lthy =
    let
      val (base, candidate) = generated_candidate specification
    in install_prepared base candidate lthy end

  fun preflight_generated_scheme specification lthy =
    let
      val (base, candidate) = generated_scheme_candidate specification
    in ignore (preflight lthy base candidate) end

  fun register_generated_scheme specification lthy =
    let
      val (base, candidate) = generated_scheme_candidate specification
    in install_prepared base candidate lthy end

  fun report_use ctxt base (entry: entry) positions primitive =
    let
      val _ =
        List.app
          (fn pos =>
            ((if primitive then ()
              else Navigation.defer_report ctxt pos Markup.keyword3);
             Navigation.defer_report ctxt pos Markup.typing))
          positions
      val terminal_pos =
        (case rev positions of
           pos :: _ => pos
         | [] => #declaration_pos entry)
    in
      Navigation.defer_report ctxt terminal_pos
        (Position.make_entity_markup {def = false}
          (#identity entry) mappingN
          (base, #declaration_pos entry))
    end

  fun report_reference ctxt pos base (entry: entry) =
    Navigation.defer_report ctxt pos
      (Position.make_entity_markup {def = false}
        (#identity entry) mappingN (base, #declaration_pos entry))

  datatype resolution_kind =
      Datatype_Fields
    | Function_Signature
    | Impl_Target
    | Alias_Declaration
    | Cast_Target

  fun command_label Datatype_Fields = "urust_datatype"
    | command_label Function_Signature = "urust_fn"
    | command_label Impl_Target = "urust"
    | command_label Alias_Declaration = "urust_type_alias"
    | command_label Cast_Target = "urust_expr"

  fun type_context Datatype_Fields = "datatype fields"
    | type_context Function_Signature = "function signatures"
    | type_context Impl_Target = "impl targets"
    | type_context Alias_Declaration = "type aliases"
    | type_context Cast_Target = "cast targets"

  (* An impl header is resolved like a signature, so its generic arguments accept exactly the
     types that member signatures accept. *)
  fun signature_kind Function_Signature = true
    | signature_kind Impl_Target = true
    | signature_kind _ = false

  (* The Self type of an impl member's elaboration context. Only that context carries it: the
     installed local theory, later members and later commands never see it. *)
  type impl_self =
    {canonical_path: string, self_type: typ, target_pos: Position.T,
     report_reference: Position.T -> unit}

  structure Impl_Self = Proof_Data
  (
    type T = impl_self option
    fun init _ = NONE
  )

  structure Impl_Source_Identity = Proof_Data
  (
    type T = source_identity option
    fun init _ = NONE
  )

  (* An impl header's complete inference frame can establish roles inside retained generic
     arguments or callable recipes, beyond the nominal owner's own scheme. Capture those checked
     slots through the finalizer; never recover them from the resulting HOL type's spellings. *)
  structure Impl_Model_Parameters = Proof_Data
  (
    type T = (backend_role * typ) list
    fun init _ = []
  )
  structure Impl_Model_Parameter_Trace = Proof_Data
  (
    type T = (backend_role * typ) list option Unsynchronized.ref option
    fun init _ = NONE
  )
  fun capture_impl_model_parameters ctxt action =
    let
      val trace = Unsynchronized.ref NONE
      val result = action (Impl_Model_Parameter_Trace.put (SOME trace) ctxt)
      val roles = case !trace of SOME roles => roles
        | NONE => raise Fail "uRust impl model capture: target frame was not finalized"
    in (result, roles) end
  fun with_impl_model_parameters roles ctxt =
    ctxt |> fold (Variable.declare_typ o snd) roles |> Impl_Model_Parameters.put roles
  fun inherit_impl_model_parameters header =
    with_impl_model_parameters (Impl_Model_Parameters.get header)
  fun record_impl_model_parameters kind ctxt finish slots =
    if kind = Impl_Target then Option.app (fn trace =>
      trace := SOME (map fst slots ~~ finish (map snd slots)))
      (Impl_Model_Parameter_Trace.get ctxt)
    else ()

  (* Match declared canonical role slots against the checked Self type. Neither variable names
     nor sort coincidence identify a role, and source placeholders remain separate. *)
  fun impl_backend_parameters ctxt ({canonical_path, self_type, ...}: impl_self) =
    let
      val declared = (case lookup ctxt canonical_path of
         NONE => []
       | SOME entry =>
           if null (#backend_roles entry) then []
           else
             let
               val substitution = Sign.typ_match (Proof_Context.theory_of ctxt)
                 (#template entry, self_type) Vartab.empty
             in map2 (fn role => fn sort =>
               (role, Envir.subst_type substitution (canonical_backend_parameter role sort)))
               (#backend_roles entry) (#backend_parameter_sorts entry) end)
      fun add (role, typ) roles =
        case AList.lookup (op =) roles role of
          NONE => (role, typ) :: roles
        | SOME previous => if previous = typ then roles
            else raise Fail "uRust impl model capture: nominal and frame roles disagree"
    in fold add declared (Impl_Model_Parameters.get ctxt) end

  fun with_impl_self self ctxt =
    ctxt |> fold (Variable.declare_typ o snd) (impl_backend_parameters ctxt self)
      |> Impl_Self.put (SOME self) |> Impl_Source_Identity.put NONE
  fun with_impl_self_identity (self, identity) =
    with_impl_self self #> Impl_Source_Identity.put identity
  val impl_self = Impl_Self.get
  val impl_source_identity = Impl_Source_Identity.get

  type generic_parameter =
    {rust: string, pos: Position.T, kind: generic_parameter_kind,
     hol: string * sort, bounds: string list, report_reference: Position.T -> unit}
  type generic_scope = {parameters: generic_parameter list}

  type callable_origin =
    {path: string, identity: serial, declaration_pos: Position.T, bound_pos: Position.T}
  type callable_recipe =
    {origin: callable_origin, inputs: rust_type list, output: rust_type option}
  type generic_declaration_identity = serial
  type binding_spec =
    {parameter: generic_parameter, declaration: generic_declaration_identity,
     callables: callable_recipe list}
  type computation_channels = {state: typ, abort: typ, input: typ, output: typ}
  type callable_relation =
    {inputs: (typ * source_identity) list,
     result: typ * source_identity, channels: computation_channels}
  datatype generic_binding = Binding of
    {spec: binding_spec, template: typ option, relation: callable_relation option, checked_recipes: int}
  type binding_events =
    {source_uses: generic_binding list, witness_uses: generic_binding list}
  type binding_scope = {bindings: generic_binding list, signature_events: binding_events option}

  fun binding_spec (Binding {spec, ...}) = spec
  fun binding_template (Binding {template, ...}) = template
  fun binding_callable_relation (Binding {relation, ...}) = relation
  fun binding_checked_recipes (Binding {checked_recipes, ...}) = checked_recipes
  fun binding_parameter binding = #parameter (binding_spec binding)
  fun binding_identity binding = #declaration (binding_spec binding)
  fun binding_name binding = fst (#hol (binding_parameter binding))
  fun scope_bindings ({bindings, ...}: binding_scope) = bindings
  fun same_generic_parameter (left: generic_parameter, right: generic_parameter) =
    #rust left = #rust right andalso #kind left = #kind right andalso
    #hol left = #hol right andalso #bounds left = #bounds right andalso
    Position.properties_of (#pos left) = Position.properties_of (#pos right) andalso
    pointer_eq (#report_reference left, #report_reference right)
  fun same_callable_origin (left: callable_origin, right: callable_origin) =
    #path left = #path right andalso #identity left = #identity right andalso
    Position.properties_of (#declaration_pos left) = Position.properties_of (#declaration_pos right) andalso
    Position.properties_of (#bound_pos left) = Position.properties_of (#bound_pos right)
  fun same_recipe (left: callable_recipe, right: callable_recipe) =
    same_callable_origin (#origin left, #origin right) andalso
    pointer_eq (#inputs left, #inputs right) andalso pointer_eq (#output left, #output right)
  fun same_binding (left, right) =
    binding_identity left = binding_identity right andalso
    same_generic_parameter (binding_parameter left, binding_parameter right) andalso
    eq_list same_recipe (#callables (binding_spec left), #callables (binding_spec right)) andalso
    binding_template left = binding_template right andalso
    binding_callable_relation left = binding_callable_relation right andalso
    binding_checked_recipes left = binding_checked_recipes right

  structure Generic_Scope = Proof_Data
  (
    type T = binding_scope option
    fun init _ = NONE
  )
  val binding_scope = Generic_Scope.get
  fun installed_bindings ctxt = maps scope_bindings (the_list (binding_scope ctxt))
  fun scope_parameters ctxt = map binding_parameter (installed_bindings ctxt)
  fun generic_scope ctxt = Option.mapPartial (fn scope =>
    if forall (fn binding => binding_template binding = SOME (TFree (#hol (binding_parameter binding))))
        (scope_bindings scope)
    then SOME {parameters = map binding_parameter (scope_bindings scope)} else NONE) (binding_scope ctxt)

  type generic_use_observer =
    {observe: generic_binding list -> typ list -> bool -> unit,
     bindings: unit -> generic_binding list}
  structure Generic_Uses = Proof_Data
  (
    type T = generic_use_observer option
    fun init _ = NONE
  )
  fun generic_use_observer ctxt = Option.map #observe (Generic_Uses.get ctxt)
  (* An operation-owned provenance collector; never installed in a returned scope. *)
  structure Signature_Origins = Proof_Data
  (
    type T = (generic_binding -> bool -> Position.T -> unit) option
    fun init _ = NONE
  )
  structure Signature_Self_Origins = Proof_Data
  (
    type T = (source_identity -> bool -> Position.T -> unit) option
    fun init _ = NONE
  )
  fun observe_signature_self ctxt witness pos =
    Option.app (fn record => Option.app (fn meaning => record meaning witness pos)
      (impl_source_identity ctxt)) (Signature_Self_Origins.get ctxt)
  structure Source_Only_Parameters = Proof_Data
  (
    type T = generic_binding list
    fun init _ = []
  )
  structure Source_Only_Positions = Proof_Data
  (
    type T = Position.T list Unsynchronized.ref option
    fun init _ = NONE
  )
  structure Declared_Body_Parameters = Proof_Data
  (
    type T = generic_binding list option
    fun init _ = NONE
  )

  val fresh_generic_declaration_identity = serial
  fun generic_scope_identities ctxt = Option.map (map binding_identity o scope_bindings) (binding_scope ctxt)
  fun with_binding_scope scope ctxt = ctxt |> Generic_Scope.put (SOME scope)
    |> Source_Only_Parameters.put [] |> Declared_Body_Parameters.put NONE
  fun prepare_binding_scope specifications ctxt =
    let
      val identities = map #declaration specifications
      val _ = if length identities = length (distinct (op =) identities) then ()
        else raise Fail "uRust generic scope: duplicate declaration identities"
      fun prepare (spec as {parameter, declaration, callables}: binding_spec) =
        let val previous = find_first (fn binding => binding_identity binding = declaration)
              (installed_bindings ctxt)
            val replacements = map_filter (fn binding =>
              case find_first (fn spec => #declaration spec = binding_identity binding) specifications of
                SOME spec => if null (#callables (binding_spec binding)) then
                  SOME (TFree (#hol (binding_parameter binding)), TFree (#hol (#parameter spec))) else NONE
              | NONE => NONE) (installed_bindings ctxt)
            val transport = Term.typ_subst_atomic replacements
            fun relation ({inputs, result, channels}: callable_relation) =
              let fun leaf (typ, source) = (transport typ, finish_meaning (map transport) source)
              in {inputs = map leaf inputs, result = leaf result,
                channels = {state = transport (#state channels), abort = transport (#abort channels),
                  input = transport (#input channels), output = transport (#output channels)}}: callable_relation end
            val relation = Option.map relation (Option.mapPartial binding_callable_relation previous)
            val template = if null callables then SOME (TFree (#hol parameter))
              else Option.map transport (Option.mapPartial binding_template previous)
            val count = case previous of SOME binding => binding_checked_recipes binding | NONE => 0
        in Binding {spec = spec, template = template, relation = relation, checked_recipes = count} end
    in {bindings = map prepare specifications, signature_events = NONE}: binding_scope end
  fun with_identified_generic_scope ({parameters}: generic_scope) identities ctxt =
    if length parameters <> length identities orelse length (distinct (op =) identities) <> length identities
    then raise Fail "uRust generic scope: malformed declaration identities"
    else with_binding_scope
      {bindings = map2 (fn parameter => fn declaration => Binding
        {spec = {parameter = parameter, declaration = declaration, callables = []},
         template = SOME (TFree (#hol parameter)), relation = NONE, checked_recipes = 0}) parameters identities,
       signature_events = NONE} ctxt
  fun with_generic_scope (scope as {parameters}: generic_scope) ctxt =
    let
      fun identity parameter =
        case find_first (fn old => same_generic_parameter
            (parameter, binding_parameter old)) (installed_bindings ctxt) of
          SOME old => binding_identity old
        | NONE => serial ()
    in with_identified_generic_scope scope (map identity parameters) ctxt end

  fun with_source_only_parameters names ctxt = Source_Only_Parameters.put
    (filter (fn binding => member (op =) names (binding_name binding)) (installed_bindings ctxt)) ctxt
  fun with_declared_body_parameters names ctxt = Declared_Body_Parameters.put (SOME
    (filter (fn binding => member (op =) names (binding_name binding)) (installed_bindings ctxt))) ctxt
  fun with_binding_availability {unavailable, source_only, declared_body} ctxt =
    ctxt |> Source_Only_Parameters.put
      (filter (fn binding => member (op =) source_only (binding_identity binding)) (installed_bindings ctxt))
    |> Declared_Body_Parameters.put (if declared_body then SOME
      (filter (fn binding => member (op =) unavailable (binding_identity binding)) (installed_bindings ctxt))
      else NONE)
  fun declared_generic_scope ctxt = is_some (Declared_Body_Parameters.get ctxt)
  fun binding_available ctxt binding = not (exists (fn old => same_binding (binding, old))
    (the_default [] (Declared_Body_Parameters.get ctxt)))
  fun binding_has_witness ctxt binding = is_some (binding_template binding) andalso
    not (exists (fn old => same_binding (binding, old)) (Source_Only_Parameters.get ctxt))
  fun current_binding ctxt parameter = find_first
    (fn binding => same_generic_parameter (parameter, binding_parameter binding)) (installed_bindings ctxt)
  fun parameter_available ctxt parameter = case current_binding ctxt parameter of
      NONE => true | SOME binding => binding_available ctxt binding
  fun parameter_has_witness ctxt parameter = case current_binding ctxt parameter of
      NONE => true | SOME binding => binding_has_witness ctxt binding
  fun require_parameter_available ctxt (parameter: generic_parameter) pos =
    if parameter_available ctxt parameter then () else error
      ("urust: generic parameter " ^ #rust parameter ^ " does not occur in the signature" ^
        Position.here pos ^ "; parameter declared" ^ Position.here (#pos parameter))
  fun scoped_meaning ctxt parameter =
    let val binding = the (current_binding ctxt parameter)
    in Meaning_Scoped_Parameter (binding_identity binding, #kind parameter) end

  type shared_selection = shared_policy * Position.T
  structure Shared_References = Proof_Data
  (
    type T =
      {positions: (Position.T * shared_selection) list,
       generic_names: ((string * Position.T) * shared_selection) list,
       generics: (serial * shared_selection) list}
    fun init _ = {positions = [], generic_names = [], generics = []}
  )
  structure Shared_Reference_Overrides = Proof_Data
  (
    type T = Models.rename list
    fun init _ = []
  )
  val without_shared_references = Shared_References.put
    {positions = [], generic_names = [], generics = []} #>
      Shared_Reference_Overrides.put []
  fun configure_shared_references renames ctxt =
    let val {generics, ...} = Shared_References.get ctxt
    in ctxt |> Shared_References.put
      {positions = [], generic_names = [], generics = generics}
      |> Shared_Reference_Overrides.put renames end

  fun inherit_shared_references header ctxt =
    let val {generics, ...} = Shared_References.get header
    in ctxt |> Shared_References.put
      {positions = [], generic_names = [], generics = generics}
      |> Shared_Reference_Overrides.put [] end

  fun activate_shared_references ctxt =
    let
      val {positions, generic_names, generics} = Shared_References.get ctxt
      fun generic ((name, key_pos), selection) =
        (case find_first (fn binding => #rust (binding_parameter binding) = name)
            (installed_bindings ctxt) of
           NONE => error ("urust: unknown shared-reference generic " ^ quote name ^
             Position.here key_pos)
         | SOME binding =>
             if #kind (binding_parameter binding) <> Type_Parameter then
               error ("urust: shared-reference generic requires a type parameter" ^
                 Position.here key_pos)
             else
               (#report_reference (binding_parameter binding) key_pos;
                Navigation.defer_report ctxt key_pos Markup.tfree;
                (binding_identity binding, selection)))
    in Shared_References.put
      {positions = positions, generic_names = [],
       generics = fold (AList.update (op =)) (map generic generic_names) generics}
      ctxt end

  fun capture_binding_events ctxt action =
    if null (installed_bindings ctxt) then
      (action ctxt, {source_uses = [], witness_uses = []}: binding_events)
    else
      let
        val tracked = installed_bindings ctxt
        val source_uses = Unsynchronized.ref ([]: generic_binding list)
        val witness_uses = Unsynchronized.ref ([]: generic_binding list)
        val active = Unsynchronized.ref true
        val parent = generic_use_observer ctxt
        val ancestors = case Generic_Uses.get ctxt of NONE => K []
          | SOME {bindings, ...} => bindings
        fun note uses binding = if !active then uses := insert same_binding binding (!uses) else ()
        fun observe current types demand =
          let
            val names = maps (map fst o (fn typ => Term.add_tfreesT typ [])) types
            fun selected binding = null types orelse
              (forall (null o #callables o binding_spec) tracked andalso
                member (op =) names (binding_name binding))
            fun record binding = if selected binding andalso
                exists (fn installed => same_binding (binding, installed)) tracked
              then (note source_uses binding; if demand then note witness_uses binding else ()) else ()
            val _ = List.app record current
          in Option.app (fn previous => previous current types demand) parent end
        (* The legacy adapter may restore an exact original record through a foreign child
           scope. Only active capture lineage can supply that record's declaration identity. *)
        fun bindings () = (if !active then tracked else []) @ ancestors ()
        val observed = Generic_Uses.put (SOME {observe = observe, bindings = bindings}) ctxt
      in Thread_Attributes.uninterruptible_body (fn run =>
        let val result = Exn.capture0 (run (fn () => action observed)) ()
            val events = {source_uses = rev (!source_uses), witness_uses = rev (!witness_uses)}
            val _ = active := false
        in (Exn.release result, events) end) end
  fun binding_signature_events ({signature_events, ...}: binding_scope) =
    case signature_events of SOME events => events
      | NONE => error "urust: signature events require a finalized Rust signature or impl target scope"
  fun binding_event_declarations ({source_uses, witness_uses}: binding_events) =
    {source_uses = map binding_identity source_uses, witness_uses = map binding_identity witness_uses}
  val speculative_generic_callbacks = Thread_Data.var (): bool Thread_Data.var
  fun capture_binding_argument_events ctxt action = Thread_Data.setmp speculative_generic_callbacks (SOME true)
    (fn () => capture_binding_events (Generic_Uses.put NONE ctxt) action) ()
  fun replay_binding_argument_events ctxt ({source_uses, witness_uses}: binding_events) =
    let
      fun replay binding = if exists (fn installed => same_binding (binding, installed))
          (installed_bindings ctxt)
        then Option.app (fn observe => observe [binding] []
          (exists (fn witness => same_binding (binding, witness)) witness_uses)) (generic_use_observer ctxt)
        else ()
    in List.app replay source_uses end
  fun event_labels ({source_uses, witness_uses}: binding_events) =
    {source_uses = map binding_name source_uses, witness_uses = map binding_name witness_uses}
  fun capture_generic_use_events ctxt action =
    let val (result, events) = capture_binding_events ctxt action in (result, event_labels events) end
  fun capture_generic_uses ctxt action =
    let val (result, {witness_uses, ...}) = capture_generic_use_events ctxt action
    in (result, witness_uses) end
  fun capture_generic_argument_events ctxt action =
    let val (result, events) = capture_binding_argument_events ctxt action in (result, event_labels events) end
  fun replay_generic_argument_events ctxt {source_uses, witness_uses} =
    replay_binding_argument_events ctxt
      {source_uses = filter (fn binding => member (op =) source_uses (binding_name binding)) (installed_bindings ctxt),
       witness_uses = filter (fn binding => member (op =) witness_uses (binding_name binding)) (installed_bindings ctxt)}
  fun note_generic_types ctxt types = if null types then () else
    Option.app (fn observe => observe (installed_bindings ctxt) types true) (generic_use_observer ctxt)
  fun observe_generic_reference demand ctxt parameter = Option.app
    (fn binding => Option.app (fn observe => observe [binding] [] demand) (generic_use_observer ctxt))
    (current_binding ctxt parameter)

  val generic_reference_demand = Thread_Data.var (): bool Thread_Data.var
  fun generic_reference_requires_witness () =
    the_default true (Thread_Data.get generic_reference_demand)

  fun generic_reference_callback demand parameter pos =
    let
      fun original () = Thread_Data.setmp generic_reference_demand (SOME demand)
        (fn () => #report_reference (parameter: generic_parameter) pos) ()
    in
      if the_default false (Thread_Data.get speculative_generic_callbacks)
      then URust_Report_Transaction.defer_action original
      else original ()
    end

  fun report_generic_reference ctxt parameter pos =
    (require_parameter_available ctxt parameter pos;
     case (Signature_Origins.get ctxt, current_binding ctxt parameter) of
       (SOME record, SOME binding) => record binding true pos
     | (_, NONE) =>
         if exists (not o null o #callables o binding_spec) (installed_bindings ctxt) then ()
         else (observe_generic_reference true ctxt parameter;
           generic_reference_callback true parameter pos)
     | _ => (observe_generic_reference true ctxt parameter;
         generic_reference_callback true parameter pos))

  fun report_generic_source_reference ctxt parameter pos =
    (require_parameter_available ctxt parameter pos;
     case (Signature_Origins.get ctxt, current_binding ctxt parameter) of
       (_, NONE) =>
         if exists (not o null o #callables o binding_spec) (installed_bindings ctxt) then ()
         else (Option.app (fn positions => positions := pos :: !positions) (Source_Only_Positions.get ctxt);
           observe_generic_reference false ctxt parameter;
           generic_reference_callback false parameter pos)
     | (hook, SOME binding) =>
         (Option.app (fn positions => positions := pos :: !positions) (Source_Only_Positions.get ctxt);
          case hook of SOME record => record binding false pos
          | NONE => (observe_generic_reference false ctxt parameter;
              generic_reference_callback false parameter pos)))

  fun report_binding_reference ctxt binding {witness, pos} =
    if not (exists (fn installed => same_binding (binding, installed)) (installed_bindings ctxt)) then ()
    else
      let val parameter = binding_parameter binding
          val _ = require_parameter_available ctxt parameter pos
          val _ = if is_some (Signature_Origins.get ctxt) then ()
            else if witness andalso not (binding_has_witness ctxt binding) then error
              ("urust: generic parameter " ^ #rust parameter ^ " has no available HOL witness" ^ Position.here pos)
            else ()
      in case Signature_Origins.get ctxt of SOME record => record binding witness pos
        | NONE =>
            (observe_generic_reference witness ctxt parameter;
             generic_reference_callback witness parameter pos;
             if witness andalso exists (fn current => not (null (#callables (binding_spec current))))
                 (installed_bindings ctxt) then Option.app (fn template => Navigation.defer_report_text ctxt pos Markup.typing
               (#rust parameter ^ " = " ^ Syntax.string_of_typ (Config.put show_sorts true ctxt) template))
               (binding_template binding) else ()) end

  fun observe_binding_syntax_types ctxt types =
    let
      val occurrences = Unsynchronized.ref ([]: (serial * Properties.T) list)
      fun leaf (TFree (name, sort)) =
            (case find_first (fn binding => binding_name binding = name) (installed_bindings ctxt) of
               NONE => ()
             | SOME binding => List.app (fn {pos, ...} =>
                 let val key = (binding_identity binding, Position.properties_of pos)
                 in if member (op =) (!occurrences) key then () else
                   (occurrences := key :: !occurrences;
                    report_binding_reference ctxt binding {witness = true, pos = pos}) end) (#1 (Term_Position.decode_positionS sort)))
        | leaf _ = ()
    in if forall (null o #callables o binding_spec) (installed_bindings ctxt) then ()
      else List.app (fn typ => Term.fold_atyps (fn atom => fn () => leaf atom) typ ()) types end

  fun with_binding_type_aliases ctxt =
    let
      val aliases = filter (fn binding => not (null (#callables (binding_spec binding))))
        (installed_bindings ctxt)
      fun expand check_ctxt types =
        let
          val environment = Unsynchronized.ref (Vartab.empty,
            fold Term.maxidx_typ (types @ map_filter binding_template aliases) (Variable.maxidx_of check_ctxt))
          fun visit (TFree (name, sort)) =
                (case find_first (fn binding => binding_name binding = name) aliases of
                   NONE => TFree (name, sort)
                 | SOME binding =>
                     let val actual = case binding_template binding of SOME typ => typ
                           | NONE => error ("urust: unresolved callable template " ^ #rust (binding_parameter binding))
                         val next = #2 (!environment) + 1
                         val required = TVar (("_urust_callable_sort", next), sort)
                         val _ = environment := Sign.typ_unify (Proof_Context.theory_of check_ctxt)
                           (actual, required) (#1 (!environment), next)
                           handle Type.TUNIFY => error ("urust: callable template " ^ #rust (binding_parameter binding) ^
                             " does not satisfy " ^ Syntax.string_of_sort check_ctxt sort)
                     in actual end)
            | visit (Type (name, operands)) = Type (name, map visit operands)
            | visit typ = typ
          val rewritten = map visit types
        in map (Envir.norm_type (#1 (!environment))) rewritten end
      fun terms check_ctxt values =
        let val original = maps (fn value => rev (Term.fold_types cons value [])) values
            val replacements = original ~~ expand check_ctxt original
        in map (Term.map_types (fn typ => the (AList.lookup (op =) replacements typ))) values end
    in if null aliases then ctxt else Context.proof_map
      (Syntax_Phases.typ_check ~1 "urust_callable_alias" expand #>
       Syntax_Phases.term_check ~101 "urust_callable_alias" terms) ctxt end

  fun resolve_generic ctxt normalize base arities pos =
    (case find_first (fn binding => #rust (binding_parameter binding) = base) (installed_bindings ctxt) of
       NONE => NONE
     | SOME binding => if is_none (binding_template binding) then NONE else
         let val parameter = binding_parameter binding
             val _ = if arities = [0] then () else error
               ("urust: generic parameter " ^ base ^ " takes no generic arguments" ^ Position.here pos)
             val _ = Navigation.defer_report ctxt pos Markup.tfree
             val _ = if forall (fn current => null (#callables (binding_spec current)))
                 (installed_bindings ctxt) then report_generic_reference ctxt parameter pos
               else report_binding_reference ctxt binding {witness = true, pos = pos}
             val actual = the (binding_template binding)
         in SOME {typ = normalize actual, meaning = scoped_meaning ctxt parameter} end)

  type generic_scheme_parameter =
    {rust: string, kind: generic_parameter_kind, hol: string * sort}
  type generic_source_parameter =
    {rust: string, kind: generic_parameter_kind, hol: (string * sort) option,
     sort: sort, bounds: string list, source_used: bool option}
  type impl_scheme =
    {parameters: generic_source_parameter list, declarations: generic_declaration_identity list,
     target: Micro_Rust_Names.target_template}
  type scoped_scheme_registration =
    {identity: term, backend: term, sources: serial list, owner: impl_scheme option,
     parameters: generic_source_parameter list, pos: Position.T}
  type binding_scheme_parameter =
    {rust: string, kind: generic_parameter_kind, declaration: serial, hol_name: string,
     witness: typ option, sort: sort, bounds: string list, callable_origins: callable_origin list,
     callable_relation: callable_relation option, source_used: bool option}
  type binding_impl_scheme =
    {parameters: binding_scheme_parameter list, declarations: generic_declaration_identity list,
     target: Micro_Rust_Names.target_template}
  type binding_scheme_registration =
    {identity: term, backend: term, sources: serial list, owner: binding_impl_scheme option,
     parameters: binding_scheme_parameter list, pos: Position.T}
  type binding_scheme_metadata =
    {owner: binding_impl_scheme option, parameters: binding_scheme_parameter list,
     source_templates: (generic_declaration_identity * typ option) list,
     ambient_declarations: generic_declaration_identity list}
  type function_scheme =
    {terms: term list, sources: serial list, owner: impl_scheme option,
     parameters: generic_source_parameter list, pos: Position.T,
     bindings: binding_scheme_metadata option}
  type scoped_generic_scheme = function_scheme
  type binding_generic_scheme = function_scheme
  fun scoped_owner (scheme: scoped_generic_scheme) = #owner scheme
  fun scoped_parameters (scheme: scoped_generic_scheme) = #parameters scheme
  fun owner_types NONE = []
    | owner_types (SOME ({target, ...}: impl_scheme)) = Micro_Rust_Names.target_types target
  fun local_witnesses (scheme: function_scheme) =
    case #bindings scheme of SOME {parameters, ...} => map_filter #witness parameters
    | NONE => map Logic.dest_type (drop (2 + length (owner_types (#owner scheme))) (#terms scheme))

  (* Normalize the backend and witnesses together; a witness can name a parameter that
     never occurs in the backend, and independent channel slots must stay independent. *)
  fun normalize_function_scheme terms =
    let
      val instT = TVars.build
        (rev (fold Term.add_tvars terms []) |> fold_index
          (fn (index, variable as (_, sort)) =>
            TVars.add (variable, TVar (("_urust_function_type", index), sort))))
      val typed = map (Term_Subst.instantiate (instT, Vars.empty)) terms
      val inst = Vars.build
        (rev (fold Term.add_vars typed []) |> fold_index
          (fn (index, variable as (_, typ)) =>
            Vars.add (variable, Var (("_urust_function_value", index), typ))))
    in map (Term_Subst.instantiate (TVars.empty, inst)) typed end

  fun parameter_core ({rust, kind, hol, sort, bounds, ...}: generic_source_parameter) =
    (rust, kind, hol, sort, bounds)

  fun binding_slot_usage used
      ({rust, kind, declaration, hol_name, witness, sort, bounds, callable_origins,
        callable_relation, ...}: binding_scheme_parameter) =
    {rust = rust, kind = kind, declaration = declaration, hol_name = hol_name,
     witness = witness, sort = sort, bounds = bounds, callable_origins = callable_origins,
     callable_relation = callable_relation, source_used = used}: binding_scheme_parameter
  fun binding_metadata_core ({owner, parameters, source_templates, ambient_declarations}: binding_scheme_metadata) =
    {parameters = map (binding_slot_usage NONE) parameters,
     owner = Option.map (fn ({parameters, declarations, target}: binding_impl_scheme) =>
       {parameters = map (binding_slot_usage NONE) parameters, declarations = declarations,
        target = target}: binding_impl_scheme) owner,
     source_templates = source_templates, ambient_declarations = ambient_declarations}: binding_scheme_metadata

  (* One deterministic traversal is the codec for all checked relation and witness types. It
     transports the whole bundle through native generalization, morphisms and caller freshening. *)
  fun map_binding_metadata transform
      ({owner, parameters, source_templates, ambient_declarations}: binding_scheme_metadata) =
    let
      fun relation ({inputs, result, channels}: callable_relation) =
        let fun leaf (typ, source) = (transform typ, finish_meaning (map transform) source)
        in {inputs = map leaf inputs, result = leaf result,
          channels = {state = transform (#state channels), abort = transform (#abort channels),
            input = transform (#input channels), output = transform (#output channels)}}: callable_relation end
      fun slot ({rust, kind, declaration, hol_name, witness, sort, bounds, callable_origins,
          callable_relation, source_used}: binding_scheme_parameter) =
        {rust = rust, kind = kind, declaration = declaration, hol_name = hol_name,
         witness = Option.map transform witness, sort = sort, bounds = bounds,
         callable_origins = callable_origins, callable_relation = Option.map relation callable_relation,
         source_used = source_used}: binding_scheme_parameter
      val owner = Option.map (fn ({parameters, declarations, target}: binding_impl_scheme) =>
        let val target = Micro_Rust_Names.map_target_types transform target
        in {parameters = map slot parameters, declarations = declarations, target = target}
          : binding_impl_scheme end) owner
    in {owner = owner, parameters = map slot parameters,
      source_templates = map (apsnd (Option.map transform)) source_templates,
      ambient_declarations = ambient_declarations}: binding_scheme_metadata end

  fun same_function_scheme (left: function_scheme, right: function_scheme) =
    eq_list (op aconv) (#terms left, #terms right) andalso
      map parameter_core (#parameters left) = map parameter_core (#parameters right) andalso
      #sources left = #sources right andalso
      (case (#bindings left, #bindings right) of
         (NONE, NONE) => #owner left = #owner right
       | (SOME first, SOME second) => binding_metadata_core first = binding_metadata_core second
       | _ => false)

  fun merge_usage (NONE, used) = used
    | merge_usage (used, NONE) = used
    | merge_usage (SOME first, SOME second) =
        if first = second then SOME first
        else error "urust_fn: conflicting source-use metadata for one source"
  fun merge_source_usage (left: generic_source_parameter, right: generic_source_parameter) =
    let
      val used = merge_usage (#source_used left, #source_used right)
    in {rust = #rust left, kind = #kind left, hol = #hol left, sort = #sort left,
      bounds = #bounds left, source_used = used}: generic_source_parameter end
  fun merge_binding_usage (left: binding_scheme_metadata, right: binding_scheme_metadata) =
    let
      fun slot (first: binding_scheme_parameter, second: binding_scheme_parameter) =
        binding_slot_usage (merge_usage (#source_used first, #source_used second)) first
      val owner = case (#owner left, #owner right) of
          (SOME first, SOME second) => SOME
            {parameters = map slot (#parameters first ~~ #parameters second),
             declarations = #declarations first, target = #target first}
        | (NONE, NONE) => NONE
        | _ => raise Fail "uRust joint binding scheme: incompatible merged owner"
    in {parameters = map slot (#parameters left ~~ #parameters right),
      owner = owner, source_templates = #source_templates left,
      ambient_declarations = #ambient_declarations left}: binding_scheme_metadata end

  fun add_function_scheme (candidate: function_scheme) entries =
    (case find_first (fn entry => same_function_scheme (entry, candidate)) entries of
       SOME existing =>
         let
           val parameters = map merge_source_usage (#parameters existing ~~ #parameters candidate)
           val bindings = case (#bindings existing, #bindings candidate) of
               (SOME first, SOME second) => SOME (merge_binding_usage (first, second))
             | _ => #bindings existing
           val merged = {terms = #terms existing, sources = #sources existing,
             parameters = parameters, owner = #owner existing, pos = #pos existing,
             bindings = bindings}: function_scheme
         in map (fn entry => if same_function_scheme (entry, existing) then merged else entry) entries end
     | NONE =>
      (case find_first (fn (entry: function_scheme) =>
          hd (#terms entry) aconv hd (#terms candidate) andalso
          nth (#terms entry) 1 aconv nth (#terms candidate) 1 andalso
          (case (#bindings entry, #bindings candidate) of
            (SOME left, SOME right) =>
              map_binding_metadata (K dummyT) left <>
                map_binding_metadata (K dummyT) right orelse
              (#sources entry <> #sources candidate andalso
                not (eq_list (op aconv) (#terms entry, #terms candidate) andalso
                  #parameters entry = #parameters candidate))
          | _ => not (eq_list (op aconv) (#terms entry, #terms candidate) andalso
              #parameters entry = #parameters candidate))) entries of
         NONE => candidate :: entries
       | SOME entry =>
           error ("urust_fn: conflicting generic schemes for one source" ^
             Position.here_list [#pos entry, #pos candidate])))

  structure Function_Schemes = Generic_Data
  (
    type T = function_scheme list
    val empty = []
    fun merge (left, right) = fold add_function_scheme right left
  )

  fun register_function_scheme_full owner {identity, backend, sources, parameters, pos} witnesses lthy =
    if null parameters andalso is_none owner then lthy
    else
      let
        val terms = Variable.polymorphic lthy
          (backend :: identity :: map Logic.mk_type (owner_types owner @ witnesses))
        fun install phi =
          let
            val transformed =
              map (Morphism.term phi) terms |> normalize_function_scheme
            val (transported_owner_types, witnesses) =
              chop (length (owner_types owner)) (map Logic.dest_type (drop 2 transformed))
            val transported_owner = Option.map (fn ({parameters, declarations, target}: impl_scheme) =>
              let val substitution = owner_types owner ~~ transported_owner_types
                val target = Micro_Rust_Names.map_target_types
                  (fn typ => the (AList.lookup (op =) substitution typ)) target
              in {parameters = parameters, declarations = declarations, target = target}: impl_scheme end) owner
            fun transport ({rust, kind, hol = NONE, sort, bounds, source_used}: generic_source_parameter) pending =
                  ({rust = rust, kind = kind, hol = NONE, sort = sort, bounds = bounds,
                    source_used = source_used}, pending)
              | transport {rust, kind, hol = SOME (name, _), sort = _, bounds, source_used} (witness :: pending) =
                  let val sort = Type.sort_of_atyp witness
                  in ({rust = rust, kind = kind, hol = SOME (name, sort), sort = sort,
                    bounds = bounds, source_used = source_used}, pending) end
              | transport _ [] = raise Fail "uRust function scheme: inconsistent witness count"
            val (transported, remaining) = fold_map transport parameters witnesses
            val _ = if null remaining then () else
              raise Fail "uRust function scheme: extra witnesses"
          in Function_Schemes.map (add_function_scheme
            {terms = transformed, sources = sources, owner = transported_owner, parameters = transported, pos = pos, bindings = NONE}) end
      in
        Local_Theory.declaration {pervasive = false, syntax = false, pos = pos} install lthy
      end

  fun register_function_scheme registration witnesses lthy =
    register_function_scheme_full NONE registration witnesses lthy

  fun register_scoped_generic_source_scheme
      ({identity, backend, sources, owner, parameters, pos}: scoped_scheme_registration) lthy =
    register_function_scheme_full owner
      {identity = identity, backend = backend, sources = sources, parameters = parameters, pos = pos}
      (map_filter (Option.map TFree o #hol) parameters) lthy

  fun register_generic_source_scheme (registration as {parameters, ...}) lthy =
    register_function_scheme registration
      (map_filter (Option.map TFree o #hol) parameters) lthy

  fun function_schemes ctxt = Function_Schemes.get (Context.Proof ctxt)

  fun named_identity term =
    (case Term.strip_comb term of (Const (name, _), _) => SOME name | _ => NONE)

  fun matching_function_schemes ctxt backend =
    let
      val thy = Proof_Context.theory_of ctxt
      val named =
        (case named_identity backend of
           NONE => []
         | SOME name => filter (fn (entry: function_scheme) =>
             named_identity (nth (#terms entry) 1) = SOME name) (function_schemes ctxt))
      fun matches (entry: function_scheme) =
        can (Pattern.match thy (hd (#terms entry), backend)) (Vartab.empty, Vartab.empty)
      val entries = if null named then filter matches (function_schemes ctxt) else named
      val identities = map (fn (entry: function_scheme) => nth (#terms entry) 1) entries
      val _ =
        if not (null named) orelse length (distinct (op aconv) identities) <= 1 then ()
        else error "urust_fn: ambiguous generic scheme query for an expanded backend"
    in
      entries
    end

  fun legacy_representable (entry: function_scheme) = case #bindings entry of NONE => true
    | SOME {parameters, owner, ...} => forall (fn slot => null (#callable_origins slot) andalso
        is_none (#callable_relation slot)) (parameters @ maps #parameters (the_list owner))

  fun consistent_parameters [] = NONE
    | consistent_parameters (entry :: entries: function_scheme list) =
        if not (forall legacy_representable (entry :: entries)) then NONE
        else if forall (fn other => #parameters other = #parameters entry) entries
        then SOME (#parameters entry)
        else error ("urust_fn: inconsistent generic metadata for one source" ^
          Position.here_list (map #pos (entry :: entries)))

  fun witnessed_parameters parameters =
    if forall (is_some o #hol) (parameters: generic_source_parameter list) then
      SOME (map (fn {rust, kind, hol, ...} => {rust = rust, kind = kind, hol = the hol}) parameters)
    else NONE

  fun generic_scheme ctxt backend =
    Option.mapPartial witnessed_parameters
      (consistent_parameters (filter (not o null o #parameters) (matching_function_schemes ctxt backend)))

  fun schemes_for_source ctxt source =
    filter (fn (entry: function_scheme) => member (op =) (#sources entry) source)
      (function_schemes ctxt)

  fun generic_source_scheme_for_source ctxt source = consistent_parameters
    (filter (not o null o #parameters) (schemes_for_source ctxt source))
  fun owner_metadata NONE = NONE
    | owner_metadata (SOME ({parameters, declarations, target}: impl_scheme)) = SOME
        (map parameter_core parameters, declarations,
         Option.map (Micro_Rust_Names.map_source_types (K dummyT)) (#source target),
         map (fn ({name, kind, witness}: Micro_Rust_Names.source_variable) =>
           (name, kind, is_some witness)) (#variables target), #requires_source_identity target)
  fun consistent_scoped_schemes [] = NONE
    | consistent_scoped_schemes (entry :: entries: function_scheme list) =
        if not (forall legacy_representable (entry :: entries)) then NONE else if forall (fn other => #parameters entry = #parameters other andalso
            owner_metadata (#owner entry) = owner_metadata (#owner other)) entries then SOME entry
        else error "urust: inconsistent scoped metadata for one source"
  fun scoped_generic_scheme_for_source ctxt source = consistent_scoped_schemes (schemes_for_source ctxt source)
  fun scoped_generic_scheme ctxt backend = consistent_scoped_schemes (matching_function_schemes ctxt backend)
  fun generic_scheme_for_source ctxt source =
    Option.mapPartial witnessed_parameters (generic_source_scheme_for_source ctxt source)

  fun register_generic_scheme {identity, backend, sources, parameters, pos} lthy =
    let
      val legacy = map (fn {rust, kind, hol} =>
        {rust = rust, kind = kind, hol = SOME hol, sort = snd hol, bounds = [],
         source_used = NONE}: generic_source_parameter) parameters
      (* The old record cannot express bounds or observed source use. Preserve authoritative
         metadata when its unique existing native scheme agrees with every supplied old slot.
         Its actual witnesses also need native joint alignment: a supplied backend may already
         be polymorphic, so recreating named TFree witnesses would disconnect used slots. *)
      fun core ({rust, kind, hol, sort, ...}: generic_source_parameter) = (rust, kind, hol, sort)
      val thy = Proof_Context.theory_of lthy
      val schemes = function_schemes lthy
      val caller_max = fold Term.maxidx_term [backend, identity] (Variable.maxidx_of lthy)
      val scheme_max = fold (fold Term.maxidx_term o #terms) schemes ~1
      val shift = Int.max (caller_max, scheme_max) + 1
      fun align (entry: function_scheme) =
        let
          val terms = map (Term.map_types (Logic.incr_tvar shift)) (#terms entry)
          val environment = Pattern.match thy (hd terms, backend) (Vartab.empty, Vartab.empty)
            |> Pattern.match thy (nth terms 1, identity)
          val witnesses = map (Envir.subst_type (#1 environment)) (local_witnesses
            {terms = terms, sources = #sources entry, owner = #owner entry,
             parameters = #parameters entry, pos = #pos entry, bindings = #bindings entry})
        in (entry, witnesses) end
      val entries = map_filter (try align) schemes
      val previous = (case entries of
          (entry, witnesses) :: others =>
            if length (distinct (op aconv)
                  (map (fn (scheme, _) => nth (#terms scheme) 1) entries)) = 1
                andalso forall (fn (other, _) => #parameters other = #parameters entry) others
                andalso map core (#parameters entry) = map core legacy
            then SOME (#parameters entry, witnesses) else NONE
        | [] => NONE)
      val registration = {identity = identity, backend = backend, sources = sources,
        parameters = legacy, pos = pos}
    in
      case previous of SOME (parameters, witnesses) =>
        register_function_scheme {identity = identity, backend = backend, sources = sources,
          parameters = parameters, pos = pos} witnesses lthy
      | NONE => register_generic_source_scheme registration lthy
    end

  fun instantiate_function_schemes ctxt entries candidate arguments =
    let
      val _ = consistent_parameters entries
      val caller_max = fold (fn (typ, _) => fn max => case typ of NONE => max
        | SOME typ => Term.maxidx_typ typ max) arguments (Variable.maxidx_of ctxt)
      val scheme_max = fold (fold Term.maxidx_term o #terms) entries ~1
      val shift = Int.max (caller_max, scheme_max) + 1
      (* Freshen only candidate variables, before caller substitution, and away from unused
         scheme witnesses as well as caller/context indexes. *)
      val fresh_candidate = Term.map_types (Logic.incr_tvar shift) candidate
      fun instantiate (scheme as {terms, parameters, ...}: function_scheme) =
        if not (legacy_representable scheme) then NONE else if length parameters <> length arguments orelse
          not (forall (fn (parameter, (argument, _)) =>
            is_some (#hol parameter) = is_some argument) (parameters ~~ arguments)) then NONE
        else
           let
             val thy = Proof_Context.theory_of ctxt
             val witnesses = local_witnesses scheme
             val supplied = map_filter (fn (parameter, (argument, pos)) =>
               if is_some (#hol parameter) then Option.map (fn typ => (typ, pos)) argument else NONE)
               (parameters ~~ arguments)
             val compatible = length supplied = length witnesses andalso forall
               (fn (witness, (argument, _)) =>
                 Sign.of_sort thy (argument, Type.sort_of_atyp witness))
               (if length supplied = length witnesses then witnesses ~~ supplied else [])
             val aligned =
               try (Pattern.match thy (hd terms, fresh_candidate)) (Vartab.empty, Vartab.empty)
             fun substitute (tyenv, _) =
               let
                 val slots = map (Envir.subst_type tyenv) witnesses
                 val used = Term.add_tvars fresh_candidate []
                 fun inst _ NONE = NONE
                   | inst (slot as TVar variable, (argument, _)) (SOME substitutions) =
                       SOME (if member (op =) used variable
                         then (slot, argument) :: substitutions else substitutions)
                   | inst (slot, (argument, _)) (SOME substitutions) =
                       if slot = argument then SOME substitutions else NONE
               in
                 Option.map
                   (fn substitutions =>
                     Term.map_types (Term.typ_subst_atomic substitutions) fresh_candidate)
                   (fold inst (slots ~~ supplied) (SOME []))
               end
           in if compatible then Option.mapPartial substitute aligned else NONE end
      val results = map_filter instantiate entries |> distinct (op aconv)
    in
      (case results of [] => NONE | [term] => SOME term
       | _ => error "urust_fn: inconsistent generic instantiations for one source candidate")
    end

  fun instantiate_generic_scheme ctxt backend candidate arguments =
    instantiate_function_schemes ctxt
      (filter (not o null o #parameters) (matching_function_schemes ctxt backend)) candidate
      (map (apfst SOME) arguments)

  fun instantiate_generic_scheme_for_source ctxt source candidate arguments =
    instantiate_function_schemes ctxt
      (filter (not o null o #parameters) (schemes_for_source ctxt source)) candidate
      (map (apfst SOME) arguments)

  fun instantiate_generic_source_scheme_for_source ctxt source candidate arguments =
    instantiate_function_schemes ctxt
      (filter (not o null o #parameters) (schemes_for_source ctxt source)) candidate arguments

  fun instantiate_scoped_generic_scheme_for_source ctxt source candidate
      {target = selection, arguments} =
    let
      val entries = schemes_for_source ctxt source
      val _ = consistent_parameters entries
      val caller_types = maps (fn selected => #self_type selected ::
          map snd (#evidence selected) @ maps Micro_Rust_Names.source_types (the_list (#source selected)))
        (the_list selection) @ maps (map_filter (fn (typ, _) => typ)) (the_list arguments)
      val caller_max = fold Term.maxidx_typ caller_types
        (Int.max (Variable.maxidx_of ctxt, Term.maxidx_of_term candidate))
      val scheme_max = fold (fold Term.maxidx_term o #terms) entries ~1
      val shift = Int.max (caller_max, scheme_max) + 1
      val thy = Proof_Context.theory_of ctxt
      fun instantiate (entry: function_scheme) =
        let
          val terms = map (Term.map_types (Logic.incr_tvar shift)) (#terms entry)
          val aligned = Pattern.match thy (hd terms, candidate) (Vartab.empty, Vartab.empty)
          val (types, _) = aligned
          val owner = Option.map (fn ({parameters, declarations, target}: impl_scheme) =>
            let
              val native = owner_types (#owner entry)
              val transported = map Logic.dest_type
                (take (length native) (drop 2 terms))
              val substitution = native ~~ transported
              val target = Micro_Rust_Names.map_target_types
                (fn typ => Envir.subst_type types (the (AList.lookup (op =) substitution typ))) target
              val {self_type, source, variables, requires_source_identity} = target
              fun rename (name, index) = (name, index + shift)
            in {self_type = self_type, source = Option.map
                (Micro_Rust_Names.map_source_variables rename) source,
              variables = map (fn {name, kind, witness} =>
                {name = rename name, kind = kind, witness = witness}) variables,
              requires_source_identity = requires_source_identity}: Micro_Rust_Names.target_template end)
            (#owner entry)
          val native = (Vartab.empty, Int.max (caller_max, scheme_max + shift) + 1)
          val native = case (owner, selection) of
              (SOME template, SOME selected) =>
                (case Micro_Rust_Names.match_target ctxt template selected native of
                   NONE => raise Micro_Rust_Names.SOURCE_MATCH
                 | SOME {types, maxidx, ...} => (types, maxidx))
            | (NONE, SOME _) => raise Micro_Rust_Names.SOURCE_MATCH
            | _ => native
          val witnesses = map (Envir.subst_type types)
            (map (Logic.incr_tvar shift) (local_witnesses entry))
          val native = case arguments of NONE => native
            | SOME supplied =>
                if length supplied <> length (#parameters entry) orelse
                    not (forall (fn (parameter, (argument, _)) =>
                      is_some (#hol parameter) = is_some argument) (#parameters entry ~~ supplied))
                then raise Micro_Rust_Names.SOURCE_MATCH
                else fold (fn (witness, argument) => fn environment =>
                  Sign.typ_unify thy (witness, argument) environment)
                  (witnesses ~~ map_filter (fn (typ, _) => typ) supplied) native
        in SOME (Term.map_types (Envir.norm_type (#1 native)) candidate) end
        handle Pattern.MATCH => NONE | Type.TUNIFY => NONE | Micro_Rust_Names.SOURCE_MATCH => NONE
      val results = map_filter instantiate entries |> distinct (op aconv)
    in case results of [] => NONE | [term] => SOME term
      | _ => error "urust: inconsistent owner/member instantiations for one source" end

  fun legacy_binding_slot ({rust, kind, hol_name, witness, sort, bounds, source_used, ...}
      : binding_scheme_parameter) =
    {rust = rust, kind = kind, hol = Option.map (fn _ => (hol_name, sort)) witness,
     sort = sort, bounds = bounds, source_used = source_used}: generic_source_parameter
  fun legacy_binding_owner ({parameters, declarations, target}: binding_impl_scheme) =
    {parameters = map legacy_binding_slot parameters, declarations = declarations, target = target}: impl_scheme
  fun lift_scheme_slot declaration ({rust, kind, hol, sort, bounds, source_used}: generic_source_parameter)
      witness =
    {rust = rust, kind = kind, declaration = declaration, hol_name = case hol of SOME pair => fst pair
       | NONE => "", witness = witness, sort = sort, bounds = bounds, callable_origins = [],
     callable_relation = NONE, source_used = source_used}: binding_scheme_parameter
  fun binding_metadata (entry: function_scheme) = case #bindings entry of SOME data => data
    | NONE =>
        let val witnesses = Unsynchronized.ref (local_witnesses entry)
            fun local_slot (index, parameter: generic_source_parameter) =
              let val witness = if is_none (#hol parameter) then NONE else
                    (case !witnesses of typ :: rest => (witnesses := rest; SOME typ)
                     | [] => raise Fail "missing legacy scheme witness")
              in lift_scheme_slot (~index - 1) parameter witness end
            val parameters = map_index local_slot (#parameters entry)
            val owner = Option.map (fn ({parameters, declarations, target}: impl_scheme) =>
              {parameters = map2 (fn declaration => fn parameter => lift_scheme_slot declaration parameter
                  (Option.map TFree (#hol parameter))) declarations parameters,
               declarations = declarations, target = target}: binding_impl_scheme) (#owner entry)
            val templates = map (fn slot => (#declaration slot, #witness slot))
              (parameters @ maps #parameters (the_list owner))
        in {parameters = parameters, owner = owner, source_templates = templates,
          ambient_declarations = []}
          : binding_scheme_metadata end
  fun binding_scoped_parameters entry = #parameters (binding_metadata entry)
  fun binding_scoped_owner entry = #owner (binding_metadata entry)
  fun binding_scheme_is_canonical (entry: binding_generic_scheme) = is_some (#bindings entry)

  fun binding_metadata_types metadata =
    let val types = Unsynchronized.ref []
        fun collect typ = (types := typ :: !types; typ)
        val _ = map_binding_metadata collect metadata
    in rev (!types) end
  fun restore_binding_metadata metadata types =
    let val pending = Unsynchronized.ref types
        fun consume _ = case !pending of typ :: rest => (pending := rest; typ)
          | [] => raise Fail "uRust joint binding scheme: missing transported type"
        val restored = map_binding_metadata consume metadata
        val _ = if null (!pending) then () else raise Fail "uRust joint binding scheme: extra type"
    in restored end

  fun register_binding_scheme_full
      ({identity, backend, sources, owner, parameters, pos}: binding_scheme_registration)
      source_templates ambient_declarations lthy =
    if null parameters andalso is_none owner then lthy else
    let
      fun validate (slot: binding_scheme_parameter) =
        let
          val template = the (AList.lookup (op =) source_templates (#declaration slot))
          val _ = if null (#callable_origins slot) = is_none (#callable_relation slot) then ()
            else error "urust: callable scheme metadata lacks its checked relation"
          val _ = case (#witness slot, #callable_relation slot) of
              (SOME witness, SOME {inputs, result, channels}) =>
                if witness = (map #1 inputs ---> Type (\<^type_name>\<open>function_body\<close>,
                    [#state channels, #1 result, #abort channels, #input channels, #output channels]))
                then () else error "urust: callable scheme witness disagrees with its checked relation"
            | _ => ()
          val _ = Option.app (fn witness => if Sign.of_sort (Proof_Context.theory_of lthy)
              (witness, #sort slot) then () else error "urust: callable scheme witness violates its whole sort")
            (#witness slot)
          val _ = case (#witness slot, template) of (SOME witness, SOME actual) =>
                if witness = actual then () else error "urust: source template disagrees with its actual witness"
            | (SOME _, NONE) => error "urust: witnessed source slot lacks its actual template"
            | _ => ()
          val _ = case (#callable_relation slot, template) of
              (SOME {inputs, result, channels}, SOME actual) =>
                if actual = (map #1 inputs ---> Type (\<^type_name>\<open>function_body\<close>,
                    [#state channels, #1 result, #abort channels, #input channels, #output channels]))
                then () else error "urust: source callable template disagrees with its checked relation"
            | (SOME _, NONE) => error "urust: callable source slot lacks its checked template"
            | _ => ()
          val _ = Option.app (fn actual => if Sign.of_sort (Proof_Context.theory_of lthy)
              (actual, #sort slot) then () else error "urust: source template violates its whole sort") template
        in () end
      val slots = parameters @ maps #parameters (the_list owner)
      val _ = if map fst source_templates = map #declaration slots andalso
          length (distinct (op =) (map fst source_templates)) = length slots then ()
        else error "urust: source templates have inconsistent declaration identities or order"
      val _ = if length ambient_declarations = length (distinct (op =) ambient_declarations) andalso
          forall (fn declaration => exists (fn slot: binding_scheme_parameter =>
            #declaration slot = declaration andalso #kind slot = Type_Parameter andalso
            is_some (Option.join (AList.lookup (op =) source_templates declaration))) slots)
            ambient_declarations then ()
        else error "urust: ambient templates do not belong to registered type declarations"
      val _ = List.app validate slots
      val metadata = {owner = owner, parameters = parameters,
        source_templates = source_templates, ambient_declarations = ambient_declarations}: binding_scheme_metadata
      val types = binding_metadata_types metadata
      val terms = Variable.polymorphic lthy (backend :: identity :: map Logic.mk_type types)
      fun install phi =
        let val terms = map (Morphism.term phi) terms |> normalize_function_scheme
            val metadata = restore_binding_metadata metadata (map Logic.dest_type (drop 2 terms))
        in Function_Schemes.map (add_function_scheme
          {terms = terms, sources = sources, owner = Option.map legacy_binding_owner (#owner metadata),
           parameters = map legacy_binding_slot (#parameters metadata), pos = pos,
           bindings = SOME metadata}) end
    in Local_Theory.declaration {pervasive = false, syntax = false, pos = pos} install lthy end
  fun register_binding_generic_source_scheme
      (registration as {parameters, owner, ...}: binding_scheme_registration) lthy =
    let
      fun template (slot: binding_scheme_parameter) =
        (#declaration slot, case #witness slot of SOME typ => SOME typ
          | NONE => Option.map (fn ({inputs, result, channels}: callable_relation) =>
              map #1 inputs ---> Type (\<^type_name>\<open>function_body\<close>,
                [#state channels, #1 result, #abort channels, #input channels, #output channels]))
              (#callable_relation slot))
    in register_binding_scheme_full registration
      (map template (parameters @ maps #parameters (the_list owner))) [] lthy end
  fun register_binding_generic_source_scheme_with_ambient_templates
      (registration as {parameters, owner, ...}: binding_scheme_registration)
      {owner = owner_templates, parameters = local_templates, ambient} lthy =
    let
      val inherited = maps #parameters (the_list owner)
      val _ = if map fst owner_templates = map #declaration inherited andalso
          map fst local_templates = map #declaration parameters andalso
          (case owner of NONE => null owner_templates | SOME data =>
            #declarations data = map #declaration inherited) then ()
        else error "urust: explicit source templates do not belong to the registered owner/local declarations"
    in register_binding_scheme_full registration
      (map (apsnd SOME) (local_templates @ owner_templates)) ambient lthy end
  fun register_binding_generic_source_scheme_with_templates registration {owner, parameters} =
    register_binding_generic_source_scheme_with_ambient_templates registration
      {owner = owner, parameters = parameters, ambient = []}

  fun consistent_binding_schemes [] = NONE
    | consistent_binding_schemes (entry :: entries: function_scheme list) =
        if forall (fn other => binding_metadata other = binding_metadata entry) entries then SOME entry
        else error "urust: inconsistent complete binding metadata for one source"
  fun binding_generic_scheme_for_source ctxt source =
    consistent_binding_schemes (schemes_for_source ctxt source)
  fun binding_generic_scheme ctxt backend =
    consistent_binding_schemes (matching_function_schemes ctxt backend)

  fun neutral_source_kind Type_Parameter = Micro_Rust_Names.Type_Source
    | neutral_source_kind Const_Parameter = Micro_Rust_Names.Const_Source

  fun source_tree_of_meaning ctxt declarations meaning =
    let
      open Micro_Rust_Names
      fun tree expected (Meaning_Scoped_Parameter (identity, kind)) =
            (case find_index (fn declared => declared = identity) declarations of
               ~1 => Source_Rigid (identity, neutral_source_kind kind)
             | index => Source_Variable (("_urust_impl_source", index), neutral_source_kind kind))
        | tree _ (Meaning_Primitive primitive) =
            Source_Node (Primitive_Source (rust_primitive_name primitive), [])
        | tree _ (Meaning_Mapped (base, _, _, _, _, arguments)) =
            let val kinds = case lookup ctxt base of
                SOME entry => map neutral_source_kind (#parameter_kinds entry)
              | NONE => map (K Type_Source) arguments
            in Source_Node (Mapped_Source base, map2 tree kinds arguments) end
        | tree _ (Meaning_Opaque rows) = Source_Node
            (Opaque_Source (map (fn (name, arguments) => (name, length arguments)) rows),
             maps (map (tree Type_Source) o snd) rows)
        | tree _ (Meaning_Numeric value) = Source_Node (Numeric_Source value, [])
        | tree _ (Meaning_Tuple types) = Source_Node (Tuple_Source, map (tree Type_Source) types)
        | tree _ (Meaning_Slice element) = Source_Node (Slice_Source, [tree Type_Source element])
        | tree _ (Meaning_Array (element, length)) = Source_Node (Array_Source, [tree Type_Source element, tree Const_Source length])
        | tree _ (Meaning_Pointer (mode, typ)) = Source_Node (Pointer_Source (mode = RPM_Mut), [tree Type_Source typ])
        | tree _ (Meaning_Reference (mode, typ)) = Source_Node (Reference_Source (mode = BM_Mut), [tree Type_Source typ])
        | tree expected (Meaning_HOL typ) = Source_HOL (expected, typ)
        | tree _ (Meaning_Parameter _) = raise Fail "uninstantiated mapping source parameter"
        | tree _ (Meaning_Const_Parameter _) = raise Fail "uninstantiated mapping const parameter"
    in tree Type_Source meaning end

  (* Locale interpretations retain one source declaration and transport its complete typed
     bundle independently. Preselection may compare declaration invariants, not concrete
     witnesses, callable channels or Self types. Callable input/result source shapes remain
     fixed after erasing only native HOL leaves. Each returned instance still undergoes the
     existing joint candidate alignment and all native/source constraints below. *)
  fun binding_declaration_shape ctxt (entry: function_scheme) =
    let
      val {owner, parameters, source_templates, ambient_declarations} = binding_metadata entry
      fun source meaning = source_tree_of_meaning ctxt [] meaning
        |> Micro_Rust_Names.map_source_types (K dummyT)
      fun relation ({inputs, result, ...}: callable_relation) =
        (map (source o #2) inputs, source (#2 result))
      fun slot ({rust, kind, declaration, hol_name, witness, sort, bounds, callable_origins,
          callable_relation, source_used}: binding_scheme_parameter) =
        (rust, kind, declaration, hol_name, is_some witness, sort, bounds, callable_origins,
          Option.map relation callable_relation,
          source_used)
      fun inherited ({parameters, declarations, target}: binding_impl_scheme) =
        (map slot parameters, declarations,
          Option.map (Micro_Rust_Names.map_source_types (K dummyT)) (#source target),
          map (fn ({name, kind, witness}: Micro_Rust_Names.source_variable) =>
            (name, kind, is_some witness)) (#variables target), #requires_source_identity target)
    in (map slot parameters, Option.map inherited owner, map (apsnd is_some) source_templates,
      ambient_declarations) end

  fun binding_generic_schemes_for_source ctxt source =
    let
      val entries = schemes_for_source ctxt source
      val _ = case entries of [] => ()
        | entry :: others =>
            if forall (fn other => binding_declaration_shape ctxt other = binding_declaration_shape ctxt entry)
                others then ()
            else error "urust: inconsistent binding declaration metadata for one source"
    in entries end

  fun align_binding_candidate ctxt (entries: function_scheme list) candidate caller_types (entry: function_scheme) =
    let
      val caller_max = fold Term.maxidx_typ caller_types
        (Int.max (Variable.maxidx_of ctxt, Term.maxidx_of_term candidate))
      val scheme_max = fold (fold Term.maxidx_term o #terms) entries ~1
      val shift = Int.max (caller_max, scheme_max) + 1
      val thy = Proof_Context.theory_of ctxt
      val terms = map (Term.map_types (Logic.incr_tvar shift)) (#terms entry)
      val metadata = case #bindings entry of
          SOME original => restore_binding_metadata original (map Logic.dest_type (drop 2 terms))
        | NONE => map_binding_metadata (Logic.incr_tvar shift) (binding_metadata entry)
      val aligned = Pattern.match thy (hd terms, candidate) (Vartab.empty, Vartab.empty)
      val metadata = map_binding_metadata (Envir.subst_type (#1 aligned)) metadata
      val owner = Option.map (fn ({target, ...}: binding_impl_scheme) =>
        let val {self_type, source, variables, requires_source_identity} = target
            fun rename (name, index) = (name, index + shift)
        in {self_type = self_type, source = Option.map
            (Micro_Rust_Names.map_source_variables rename) source,
          variables = map (fn {name, kind, witness} =>
            {name = rename name, kind = kind, witness = witness}) variables,
          requires_source_identity = requires_source_identity}: Micro_Rust_Names.target_template end)
        (#owner metadata)
    in {metadata = metadata, owner = owner,
      native = (Vartab.empty, Int.max (caller_max, scheme_max + shift) + 1)} end

  fun instantiate_binding_generic_scheme_for_source ctxt source candidate
      {target = selection, arguments} =
    let
      val entries = binding_generic_schemes_for_source ctxt source
      val caller_types = maps (fn selected => #self_type selected :: map snd (#evidence selected) @
          maps Micro_Rust_Names.source_types (the_list (#source selected))) (the_list selection) @
        maps (map_filter (fn (typ, _) => typ)) (the_list arguments)
      val thy = Proof_Context.theory_of ctxt
      fun instantiate entry =
        let
          val {metadata, owner, native} = align_binding_candidate ctxt entries candidate caller_types entry
          val native = case (owner, selection) of
              (SOME template, SOME selected) =>
                (case Micro_Rust_Names.match_target ctxt template selected native of
                   NONE => raise Micro_Rust_Names.SOURCE_MATCH
                 | SOME {types, maxidx, ...} => (types, maxidx))
            | (NONE, SOME _) => raise Micro_Rust_Names.SOURCE_MATCH | _ => native
          val slots = #parameters metadata
          val native = case arguments of NONE => native | SOME supplied =>
            if length supplied <> length slots orelse
                not (forall (fn (slot, (argument, _)) => is_some (#witness slot) = is_some argument)
                  (slots ~~ supplied)) then raise Micro_Rust_Names.SOURCE_MATCH
            else fold (fn (slot, (argument, _)) => fn environment =>
              case (#witness slot, argument) of (SOME witness, SOME actual) =>
                Sign.typ_unify thy (witness, actual) environment | _ => environment)
              (slots ~~ supplied) native
        in SOME (Term.map_types (Envir.norm_type (#1 native)) candidate) end
        handle Pattern.MATCH => NONE | Type.TUNIFY => NONE | Micro_Rust_Names.SOURCE_MATCH => NONE
      val results = map_filter instantiate entries |> distinct (op aconv)
    in case results of [] => NONE | [term] => SOME term
      | _ => error "urust: inconsistent complete binding instantiations for one source" end

  fun self_outside_impl pos =
    error ("urust: Self is only available inside an impl block" ^ Position.here pos)

  (* Self names the implementing type in every type position of a member: a reference to the
     entity that the target head denotes, with the canonical target in its tooltip. *)
  fun resolve_self ctxt base arities pos =
    if base <> "Self" then NONE
    else
      (case impl_self ctxt of
         NONE => self_outside_impl pos
       | SOME {canonical_path, self_type, report_reference, ...} =>
           let
             val _ =
               if arities = [0] then ()
               else error ("urust: Self cannot take generic arguments" ^ Position.here pos)
             val _ = Navigation.defer_report ctxt pos Markup.keyword3
             val _ =
               (case self_type of
                  Type (name, _) => Navigation.defer_type ctxt pos name
                | _ => ())
             val _ = report_reference pos
             val _ = observe_signature_self ctxt true pos
             val _ =
               Navigation.defer_report_text ctxt pos Markup.typing ("Self = " ^ canonical_path)
           in SOME {typ = self_type,
             meaning = the_default (Meaning_HOL self_type) (impl_source_identity ctxt)} end)

  (* This path-shape rule applies even when a declared HOL signature skips type resolution. *)
  fun check_type_path_start kind segments =
    (case segments of
       _ :: rest =>
         List.app
           (fn Rust_Type_Path_Segment (name, pos, _, _) =>
             if name = "Self" orelse name = "self" then
               error (command_label kind ^ ": `" ^ name ^
                 "` in paths can only be used in start position" ^ Position.here pos)
             else ())
           rest
     | [] => ())

  (* A type-namespace import binds the first segment of a source type path. It is consulted after
     generic parameters and before exact registry keys; the canonical prefix segments carry no
     source position, so they receive no reports, while the alias occurrence keeps its generic
     arguments on the canonical terminal segment. *)
  fun imported_type_path ctxt kind rows =
    (case rows of
       [] => NONE
     | (name, pos, arguments) :: rest =>
         (case URust_Import_Scope.lookup ctxt URust_Import_Scope.Type_Namespace name of
            NONE => NONE
          | SOME binding =>
              let
                val _ = URust_Import_Scope.require_available pos binding
                val _ =
                  if null rest then ()
                  else
                    error
                      (command_label kind ^ ": imported " ^ quote name ^ " (" ^
                        quote (#key binding) ^ ") cannot qualify a Rust type path" ^
                        Position.here pos)
                val _ =
                  if URust_Import_Scope.has_role binding URust_Import_Scope.Mapped_Type then ()
                  else if URust_Import_Scope.has_role binding URust_Import_Scope.Enum_Variant then
                    error
                      (command_label kind ^ ": imported " ^ quote name ^
                        " names the enum variant " ^ quote (#key binding) ^ ", not a type" ^
                        Position.here pos)
                  else
                    error
                      (command_label kind ^ ": imported " ^ quote name ^ " (" ^
                        quote (#key binding) ^ ") is not a usable Rust type" ^
                        Position.here pos)
                val canonical = URust_Import_Scope.key_segments (#key binding)
                val prefix = map (fn segment => (segment, Position.none, [])) (#1 (split_last canonical))
              in SOME (prefix @ [(List.last canonical, pos, arguments)], (pos, binding)) end))

  fun positioned_result kind positions action =
    (case Exn.result action () of
       Exn.Res result => result
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           error
             (command_label kind ^ ": " ^ Runtime.exn_message exn ^
               Position.here_list positions))

  fun no_type_variables what pos typ =
    if null (Term.add_tfreesT typ []) andalso
        null (Term.add_tvarsT typ [])
    then typ
    else
      error
        ("urust_datatype: type variables are not supported in " ^
          what ^ Position.here pos)

  fun read_hol_escape ctxt source =
    let
      val pos = Input.pos_of source
      val typ =
        positioned_result Datatype_Fields [pos]
          (fn () =>
            URust_Report_Transaction.native ctxt
              (fn read_ctxt => Syntax.read_typ read_ctxt (Syntax.implode_input source)))
    in no_type_variables "datatype fields" pos typ end

  fun unknown_type kind base pos =
    if member (op =) ["PhantomData", "core::marker::PhantomData", "std::marker::PhantomData"] base then
      error (command_label kind ^ ": automatic PhantomData field handling is deferred; " ^
        "provide an explicit HOL type and urust_type mapping to store the field, " ^
        "or omit it explicitly from a documented proof-source mirror" ^ Position.here pos)
    else if kind = Impl_Target then
      error ("urust: unknown impl target type " ^ quote base ^
        "; declare it with urust_type, urust_datatype or urust_type_alias" ^ Position.here pos)
    else error
      (command_label kind ^ ": unknown Rust type " ^ quote base ^
        "; declare it with urust_type or use \<tau>\<open>...\<close>" ^
        " (Rust synonyms may also be declared with urust_type_alias)" ^
        Position.here pos)

  fun arity_error kind base expected actual pos =
    let
      fun arities values =
        values |> map string_of_int |> commas |> enclose "[" "]"
    in
      error
        (command_label kind ^ ": Rust type " ^ quote base ^
          " has generic arities " ^ arities actual ^
          ", but the active urust_type mapping expects " ^
          arities expected ^ Position.here pos)
    end

  fun unsupported kind description pos =
    error
      (command_label kind ^ ": " ^ description ^
        " is not supported in " ^ type_context kind ^
        "; use \<tau>\<open>...\<close>" ^
        Position.here pos)

  fun sort_error kind ctxt base argument sort pos =
    error
      (command_label kind ^ ": generic argument type " ^
        quote (Syntax.string_of_typ ctxt argument) ^
        " does not satisfy sort " ^
        quote (Syntax.string_of_sort ctxt sort) ^
        " required by the urust_type mapping for " ^
        quote base ^ Position.here pos)

  fun path_rows segments =
    map
      (fn Rust_Type_Path_Segment (name, pos, arguments, _) =>
        (name, pos, the_default [] arguments))
      segments

  fun row_information rows =
    {base = space_implode "::" (map #1 rows),
     positions = map #2 rows,
     arities = map (length o #3) rows,
     arguments = maps #3 rows}

  fun type_from_rows layout rows =
    Path_Type (map (fn (name, pos, arguments) =>
      Rust_Type_Path_Segment (name, pos,
        if null arguments then NONE else SOME arguments, make_source_layout pos [])) rows, layout)

  fun map_recipe_types path escape =
    let
      fun typ (Path_Type (segments, layout)) =
            path (map (fn Rust_Type_Path_Segment (name, pos, arguments, source) =>
              Rust_Type_Path_Segment (name, pos, Option.map (map argument) arguments, source))
              segments, layout)
        | typ (Tuple_Type (types, layout)) = Tuple_Type (map typ types, layout)
        | typ (Group_Type (T, layout)) = Group_Type (typ T, layout)
        | typ (Reference_Type (mode, lifetime, T, layout)) =
            Reference_Type (mode, lifetime, typ T, layout)
        | typ (Raw_Pointer_Type (mode, T, layout)) = Raw_Pointer_Type (mode, typ T, layout)
        | typ (Slice_Type (T, layout)) = Slice_Type (typ T, layout)
        | typ (Array_Type (T, size, layout)) = Array_Type (typ T, size, layout)
        | typ (Const_Array_Type (T, size, layout)) = Const_Array_Type (typ T, typ size, layout)
        | typ (Function_Type (types, result, layout)) =
            Function_Type (map typ types, Option.map typ result, layout)
        | typ (Impl_Trait_Type (T, layout)) = Impl_Trait_Type (typ T, layout)
        | typ (HOL_Type_Source source) = escape source
        | typ other = other
      and argument (Rust_Type_Argument T) = Rust_Type_Argument (typ T)
        | argument (Rust_Associated_Type_Argument (name, pos, T)) =
            Rust_Associated_Type_Argument (name, pos, typ T)
        | argument other = other
    in typ end

  fun canonical_alias_recipe ctxt parameters =
    map_recipe_types
      (fn (segments, layout) =>
        let
          val rows = path_rows segments
          val parameter = case rows of [(name, _, [])] => member (op =) parameters name
            | _ => false
        in
          if parameter then Path_Type (segments, layout)
          else case imported_type_path ctxt Alias_Declaration rows of
              SOME (canonical, _) => type_from_rows layout canonical
            | NONE => Path_Type (segments, layout)
        end)
      HOL_Type_Source

  fun substitute_alias_recipe parameters arguments rhs =
    let
      val substitutions = parameters ~~ arguments
      fun parameter (Path_Type ([Rust_Type_Path_Segment (name, _, NONE, _)], _)) =
            AList.lookup (op =) substitutions name
        | parameter _ = NONE
      fun typ T =
        (case parameter T of
           SOME (Rust_Type_Argument value) => value
         | SOME value => mapping_error "const argument cannot be used as a type in an alias"
             (argument_origin value)
         | NONE =>
             (case T of
                Path_Type (segments, layout) =>
                  Path_Type (map (fn Rust_Type_Path_Segment (name, pos, args, source) =>
                    Rust_Type_Path_Segment (name, pos, Option.map (map argument) args, source))
                    segments, layout)
              | Tuple_Type (types, layout) => Tuple_Type (map typ types, layout)
              | Group_Type (T, layout) => Group_Type (typ T, layout)
              | Reference_Type (mode, lifetime, T, layout) =>
                  Reference_Type (mode, lifetime, typ T, layout)
              | Raw_Pointer_Type (mode, T, layout) => Raw_Pointer_Type (mode, typ T, layout)
              | Slice_Type (T, layout) => Slice_Type (typ T, layout)
              | Array_Type (T, size, layout) => Array_Type (typ T, size, layout)
              | Const_Array_Type (T, size, layout) =>
                  (case parameter size of
                     SOME (Rust_Numeric_Argument integer) => Array_Type (typ T, integer, layout)
                   | _ => Const_Array_Type (typ T, typ size, layout))
              | Function_Type (types, result, layout) =>
                  Function_Type (map typ types, Option.map typ result, layout)
              | Impl_Trait_Type (T, layout) => Impl_Trait_Type (typ T, layout)
              | other => other))
      and argument (Rust_Type_Argument T) =
            (case parameter T of SOME value => value | NONE => Rust_Type_Argument (typ T))
        | argument (Rust_Associated_Type_Argument (name, pos, T)) =
            Rust_Associated_Type_Argument (name, pos, typ T)
        | argument other = other
    in typ rhs end

  fun expand_field_representation ctxt parameter_names (name, name_pos) original =
    let
      val name = Symbol.trim_blanks name
      val field_pos = rust_type_position original
      fun invalid message = mapping_error message name_pos
      (* A recipe-owned nominal head is reported at the authored alias token. Relocate before
         substitution so a nominal head supplied by an actual argument keeps its own positions. *)
      fun relocate_head pos (Group_Type (T, layout)) = Group_Type (relocate_head pos T, layout)
        | relocate_head pos (Path_Type (segments, layout)) =
            let
              val rows = path_rows segments
              val (prefix, (name, _, arguments)) = split_last rows
              val rows = map (fn (name, _, args) => (name, Position.none, args)) prefix @
                [(name, pos, arguments)]
            in type_from_rows layout rows end
        | relocate_head _ T = T
      fun expand seen validations escapes (Group_Type (T, _)) =
            expand seen validations escapes T
        | expand seen validations escapes (Path_Type (segments, _)) =
            let
              val _ = check_type_path_start Datatype_Fields segments
              val _ = case segments of Rust_Type_Path_Segment (head, _, _, _) :: _ =>
                  if member (op =) parameter_names head then
                    invalid "field representations require an outer nominal type, not a source parameter"
                  else ()
                | _ => ()
              val rows = path_rows segments
              val rows = case imported_type_path ctxt Datatype_Fields rows of
                  SOME (canonical, (alias_pos, binding)) =>
                    (URust_Import_Scope.defer_use_reference ctxt alias_pos binding; canonical)
                | NONE => rows
              val {base, positions, arities, arguments} = row_information rows
              val entry = case lookup ctxt base of SOME entry => entry
                | NONE => unknown_type Datatype_Fields base field_pos
              val _ = if #segment_arities entry = arities then ()
                else arity_error Datatype_Fields base (#segment_arities entry) arities field_pos
            in
              if alias_origin (#origin entry) then
                let
                  val _ = if member (op =) seen base then
                    invalid "recursive alias while selecting a field representation" else ()
                  val recipe = case Symtab.lookup
                      (Alias_Recipes.get (Context.Proof ctxt)) base of
                      SOME recipe => recipe
                    | NONE => invalid ("checked source recipe unavailable for alias " ^ quote base)
                  val _ = List.app (fn position => report_reference ctxt position base entry) positions
                  val rhs = substitute_alias_recipe (#parameters recipe) arguments
                    (relocate_head (List.last positions) (#rhs recipe))
                in expand (base :: seen)
                  ((#parameter_kinds entry, arguments) :: validations)
                  (#escapes recipe @ escapes) rhs end
              else
                let
                  val view = case representation_entry ctxt base name of
                      SOME view => view
                    | NONE => invalid
                        ("unknown representation " ^ quote name ^ " for " ^ quote base)
                  val selected = #entry view
                  (* Direct/imported heads retain exact native token positions. Recipe heads
                     already carry the authored alias occurrence's terminal token above. *)
                  val T = type_from_rows (make_source_layout field_pos []) rows
                  val provenance =
                    {source_head = base, representation = name,
                     declaration_pos = #name_pos view,
                     declaration_identity = #identity selected}: field_representation
                in (T, rev validations, escapes, provenance) end
            end
        | expand _ _ _ _ =
            invalid "field representations require an outer nominal type, optionally through an alias"
    in expand [] [] [] original end

  fun numeric_argument_position
      (Integer_Literal (_, layout, _)) =
    source_span layout

  fun length_literal ctxt integer =
    let
      val raw = integer_literal_lexeme integer
      val pos = integer_literal_position integer
      val _ = if is_none (integer_literal_suffix_position integer) then ()
        else mapping_error "length arguments must be unsuffixed integer literals" pos
      val value =
        (case Parser_Utils.read_unsigned_integer raw of
           SOME n => n
         | NONE => mapping_error "invalid complete unsuffixed length literal" pos)
    in Syntax.read_typ ctxt (string_of_int value) end

  type resolved = {typ: typ, meaning: meaning}
  type argument_specification = {kind: generic_parameter_kind, witness: bool, sort: sort}
  fun argument_specification ({kind, hol, sort, ...}: generic_source_parameter) =
    {kind = kind, witness = is_some hol, sort = sort}: argument_specification

  (* One inference environment and one lazy role table belong to a complete
     signature or field batch. Canonical registry slots are never reused as
     flexible variables by two independent resolutions. *)
  structure Declaration_Parameter_Names = Proof_Data
  (
    type T = string list
    fun init _ = []
  )

  fun inference_state kind ctxt initial_types =
    let
      val instance_name = "_urust_inference_" ^ string_of_int (serial ())
      fun binding_types binding =
        the_list (binding_template binding) @
          (case binding_callable_relation binding of NONE => []
           | SOME {inputs, result, channels} =>
               map #1 inputs @ [#1 result, #state channels, #abort channels,
                 #input channels, #output channels])
      val model_types = map_filter (fn role =>
        Option.map #typ (Models.lookup ctxt role))
        (Models.order (Address :: Global :: map fst (model_parameter_requirements ctxt)))
      val imported_types = initial_types @ model_types @
        map snd (Impl_Model_Parameters.get ctxt) @
        maps binding_types (installed_bindings ctxt) @
        map #self_type (the_list (impl_self ctxt))
      val initial_maxidx =
        fold Term.maxidx_typ imported_types (Variable.maxidx_of ctxt)
      (* Already checked imports use the existing parameter codec before intermediate
         callable validation. Source-variable policy has been checked before this frame. *)
      val imported_variables = fold Term.add_tvarsT imported_types []
      val imported_environment = Vartab.build (fold
        (fn (variable as (name, index), sort) =>
          if Type_Infer.is_param variable then I
          else Vartab.update_new
            (variable, (sort, Type_Infer.param index (name, sort))))
        imported_variables)
      val unification: (Type.tyenv * int) Unsynchronized.ref =
        Unsynchronized.ref
          (imported_environment, initial_maxidx)
      val backend_slots: (backend_role * typ) list Unsynchronized.ref =
        Unsynchronized.ref
          (case impl_self ctxt of NONE => [] | SOME self => impl_backend_parameters ctxt self)
      (* An alias is a transparent source scheme. Capture its declared role variables, then
         instantiate them with the caller's context at use, just like its nominal target. *)
      fun model_binding role =
        if kind = Alias_Declaration then NONE else Models.lookup ctxt role

      fun fresh sort =
        let
          val (environment, index) = !unification
          val next = index + 1
          val _ = unification := (environment, next)
        in Type_Infer.param next (instance_name, sort) end

      fun normalize typ =
        Envir.norm_type (#1 (!unification)) typ

      (* Sort unification can replace our named inference parameters with ordinary
         native TVars. Keep those newly allocated variables in this frame's namespace;
         imported caller variables keep their established parameterization, and
         authored/fixed types remain unchanged. *)
      fun parameterize (typ as TVar ((name, index), sort)) =
            if Type_Infer.is_param (name, index) then typ
            else Type_Infer.param index
              (if index > initial_maxidx then instance_name else name, sort)
        | parameterize typ = typ

      (* Preserve that namespace as soon as native sort unification creates a variable,
         including during intermediate callable validation. Aliases retain the native
         environment's keys and constraints; no authored schematic type is admitted. *)
      fun retain_native_variables (environment, maxidx) =
        let
          val variables = fold (fn (_, (_, typ)) => Term.add_tvarsT typ)
            (Vartab.dest environment) []
          val generated = filter (fn (variable as (name, index), _) =>
            name = Name.aT andalso index > initial_maxidx andalso
              not (Vartab.defined environment variable)) variables
          val environment = fold (fn (variable, sort) =>
            Vartab.update_new (variable, (sort, parameterize (TVar (variable, sort)))))
            generated environment
        in (environment, maxidx) end

      fun commit_environment proposed =
        unification := retain_native_variables proposed

      fun check_sort base argument sort pos =
        let
          val constraint = fresh sort
          val environment =
            Type.unify (Proof_Context.tsig_of ctxt)
              (argument, constraint) (!unification)
            handle Type.TUNIFY =>
              sort_error kind ctxt base (normalize argument) sort pos
        in commit_environment environment end

      fun unify pairs =
        let val proposed = fold (fn pair => fn environment =>
          Sign.typ_unify (Proof_Context.theory_of ctxt) pair environment) pairs (!unification)
        in commit_environment proposed end
      fun native () = !unification
      val accept_native = commit_environment

      fun import_binding pos (typ as Type (name, types)) =
            if typ = dummyT then fresh [] else Type (name, map (import_binding pos) types)
        | import_binding _ (TFree ("'_dummy_", sort)) = fresh sort
        | import_binding pos (typ as TFree (name, _)) =
            if (exists (fn parameter => fst (#hol parameter) = name) (scope_parameters ctxt)
                orelse member (op =) (Declaration_Parameter_Names.get ctxt) name)
                andalso not (Models.ambient_name ctxt name) then
              Models.error_at ("model parameter HOL variable " ^ quote name ^
                " collides with a Rust generic; use an explicit ambient_type_parameters binding") pos
            else typ
        | import_binding _ typ = typ

      (* A checked Self role is already rigid. Defaults may agree with it, but cannot replace it. *)
      val _ = List.app (fn (role, slot) =>
        case model_binding role of NONE => ()
        | SOME {typ, pos} => if typ = dummyT then () else
            (unify [(slot, import_binding pos typ)]
              handle Type.TUNIFY => Models.error_at
                ("model parameter " ^ quote (role_name role) ^ " conflicts with checked Self") pos))
        (!backend_slots)

      fun backend role_sorts pos =
        let
          fun allocated (role, _) =
            (case AList.lookup (op =) (!backend_slots) role of
               SOME slot => slot
             | NONE =>
                 let
                    val slot = (case model_binding role of
                      SOME {typ, pos} =>
                        let
                          val _ = if kind <> Datatype_Fields orelse typ = dummyT orelse
                              (case typ of TFree _ => true | _ =>
                                null (Term.add_tfreesT typ []) andalso
                                not (Term.exists_subtype (fn T => T = dummyT) typ)) then ()
                            else Models.error_at
                              "structured free/hole model bindings are not supported in datatype fields" pos
                        in if typ = dummyT then fresh [] else import_binding pos typ end
                    | NONE => fresh [])
                   val _ = backend_slots := (role, slot) :: !backend_slots
                 in slot end)
          (* Allocate the whole request before adding constraints, retaining the established
             pair's fresh-variable order while allowing a later request to add one role. *)
          val slots = map allocated role_sorts
          val _ = List.app (fn (slot, (role, sort)) =>
            check_sort ("implicit " ^ role_name role ^ " backend") slot sort
              (case model_binding role of SOME {pos, ...} => pos | NONE => pos))
            (slots ~~ role_sorts)
        in map normalize slots end
    in
      {fresh = fresh, normalize = normalize, check_sort = check_sort,
       backend = backend, unify = unify, native = native, accept_native = accept_native,
       parameterize = parameterize,
       backend_slots = fn () =>
         map_filter (fn role =>
            Option.map (pair role) (AList.lookup (op =) (!backend_slots) role))
            (role_order (map fst (!backend_slots)))}
    end

  fun resolve_value_operations kind ctxt read_escape check_sort normalize backend
      parameter dependency =
    let
      val selected_field = Unsynchronized.ref (NONE: (string * Position.T) option)
      val captured_escapes = Unsynchronized.ref ([]: (Input.source * typ) list)
      val source_schema_only = Unsynchronized.ref false
      val ordinary_escape = read_escape
      fun same_escape (left, right) =
        Input.string_of left = Input.string_of right andalso
          same_origin (Input.pos_of left, Input.pos_of right)
      fun read_escape source =
        (case AList.lookup same_escape (!captured_escapes) source of
           SOME typ => Proof_Context.cert_typ ctxt typ
         | NONE => ordinary_escape source)
      (* Raw pointers and mutable references share one reference model and one backend pair. *)
      fun reference_carrier carrier target pos =
        let
          val [address, global] =
            backend [(Address, \<^sort>\<open>type\<close>), (Global, \<^sort>\<open>type\<close>)] pos
        in
          Term.typ_subst_atomic
            [(\<^typ>\<open>'urust_address\<close>, address),
             (\<^typ>\<open>'urust_global\<close>, global),
             (\<^typ>\<open>'urust_value\<close>, target)]
            carrier
          |> Proof_Context.cert_typ ctxt
        end
      val reference_typ = reference_carrier
        \<^typ>\<open>('urust_address, 'urust_global, 'urust_value) Global_Store.ref\<close>
      val readonly_typ = reference_carrier
        \<^typ>\<open>('urust_address, 'urust_global, 'urust_value) Global_Store.ro_ref\<close>

      fun shared_selection target meaning pos =
        let
          val {positions, generics, ...} = Shared_References.get ctxt
          fun same_position (left, right) =
            Position.properties_of left = Position.properties_of right
          fun self_target (Group_Type (typ, _)) = self_target typ
            | self_target (Path_Type ([Rust_Type_Path_Segment ("Self", _, NONE, _)], _)) = true
            | self_target _ = false
          val generic = case meaning of
              Meaning_Scoped_Parameter (declaration, Type_Parameter) =>
                AList.lookup (op =) generics declaration
            | _ => NONE
          val nominal = case meaning of
              Meaning_Mapped (base, _, _, _, _, _) => SOME base
            | Meaning_Primitive primitive => SOME (rust_primitive_name primitive)
            | Meaning_HOL _ => if self_target target then Option.map #canonical_path (impl_self ctxt)
                else NONE
            | _ => NONE
          fun nominal_selection base =
            (case lookup ctxt base of
               SOME entry =>
                 (case #shared_policy entry of
                    SOME selection => (report_reference ctxt pos base entry; SOME selection)
                  | NONE => NONE)
             | NONE => NONE)
          val selected =
            (case AList.lookup same_position positions pos of
               SOME selection => SOME selection
             | NONE => (case generic of SOME selection => SOME selection
                 | NONE => Option.mapPartial nominal_selection nominal))
          (* Aliases have already expanded to structural meaning here. The canonical slice
             borrow does not depend on the spelling of the target or on an expected HOL type. *)
          val selected = (case meaning of
              Meaning_Slice _ =>
                (case selected of
                   SOME (policy, _) =>
                     if policy = Shared_Readonly then selected
                     else error ("urust_fn: shared slice references have the fixed readonly " ^
                       "representation; use a HOL type antiquotation for another carrier" ^
                       Position.here pos)
                 | NONE => SOME (Shared_Readonly, pos))
            | _ => selected)
        in
          (case selected of
             SOME (policy, policy_pos) =>
               (Navigation.defer_report_text ctxt pos Markup.typing
                  ("shared representation = " ^ shared_policy_name policy ^
                    Position.here policy_pos); policy)
           | NONE => error
               ("urust_fn: shared Rust references (&T) require an explicit representation; " ^
                 "declare a shared type policy or shared_references override" ^ Position.here pos))
        end

      fun unsigned_value integer =
        let
          val pos = integer_literal_position integer
          val _ = if is_none (integer_literal_suffix_position integer) then ()
            else mapping_error "const arguments must be unsuffixed integer literals" pos
        in
          case Parser_Utils.read_unsigned_integer (integer_literal_lexeme integer) of
            SOME value => value
          | NONE => mapping_error "invalid complete unsuffixed const argument" pos
        end

      fun source_kind (Meaning_Const_Parameter _) = Const_Parameter
        | source_kind (Meaning_Scoped_Parameter (_, role)) = role
        | source_kind (Meaning_Numeric _) = Const_Parameter
        | source_kind _ = Type_Parameter

      fun source_sort base sort ({meaning, evidence, pos}: {meaning: meaning, evidence: typ option, pos: Position.T}) =
        if !source_schema_only orelse null sort orelse
            Sign.subsort (Proof_Context.theory_of ctxt) (\<^sort>\<open>type\<close>, sort)
        then ()
        else
          (case (meaning, evidence) of
             (Meaning_Numeric value, _) =>
               if Sign.subsort (Proof_Context.theory_of ctxt)
                 (if value = 0 then \<^sort>\<open>len0\<close> else \<^sort>\<open>len\<close>, sort)
               then ()
               else mapping_error ("erased const argument cannot validate sort " ^
                 quote (Syntax.string_of_sort ctxt sort) ^ " required by " ^ quote base) pos
           | (_, SOME typ) =>
               (* Source-only evidence retains its checked sorts. Unifying here would strengthen
                  a discarded canonical backend role instead of validating an existing bound. *)
               if Sign.of_sort (Proof_Context.theory_of ctxt) (typ, sort) then ()
               else sort_error kind ctxt base typ sort pos
           | _ => mapping_error ("erased source argument has no denotation to validate sort " ^
               quote (Syntax.string_of_sort ctxt sort) ^ " required by " ^ quote base) pos)

      fun source_argument expected argument =
        let val value = source_argument_value expected argument
          val _ = if !source_schema_only then ()
            else note_source_resolution ctxt (#meaning value) NONE argument
        in value end
      and source_argument_value expected (Rust_Type_Argument typ) = source_type (SOME expected) typ
        | source_argument_value Const_Parameter (Rust_Numeric_Argument integer) =
            {meaning = Meaning_Numeric (unsigned_value integer), evidence = NONE,
             pos = integer_literal_position integer}
        | source_argument_value Type_Parameter (Rust_Numeric_Argument integer) =
            unsupported kind "numeric generic arguments for type parameters"
              (integer_literal_position integer)
        | source_argument_value _ (Rust_Lifetime_Argument (Rust_Lifetime (_, pos))) =
            unsupported kind "lifetime generic arguments" pos
        | source_argument_value _ (Rust_Associated_Type_Argument (_, pos, _)) =
            unsupported kind "associated type bindings" pos
        | source_argument_value _ (Rust_Const_Expression_Argument source) =
            unsupported kind "const expression generic arguments" (Input.pos_of source)

      and opaque_argument (Rust_Type_Argument typ) = source_type NONE typ
        | opaque_argument (Rust_Numeric_Argument integer) = source_argument Const_Parameter
            (Rust_Numeric_Argument integer)
        | opaque_argument argument = source_argument Type_Parameter argument

      and source_nominal base positions arities arguments pos rows primitive =
        let
          val _ = (case rows of (head, head_pos, _) :: _ :: _ =>
              if head = "Self" orelse
                exists (fn ({rust, ...}: generic_parameter) => rust = head) (scope_parameters ctxt)
                orelse is_some (parameter head [0] head_pos)
              then unsupported kind "associated paths on scoped parameters in erased arguments" head_pos
              else ()
            | _ => ())
          val scoped = find_index (fn ({rust, ...}: generic_parameter) => rust = base)
            (scope_parameters ctxt)
          val value = if scoped >= 0 then
              let
                val parameter = nth (scope_parameters ctxt) scoped
                val _ = if arities = [0] then () else
                  mapping_error "generic parameters cannot take generic arguments" pos
                val _ = report_generic_source_reference ctxt parameter pos
                val _ = Navigation.defer_report ctxt pos Markup.tfree
              in SOME {meaning = scoped_meaning ctxt parameter,
                  evidence = Option.map normalize (binding_template (the (current_binding ctxt parameter))),
                  pos = pos} end
            else if base = "Self" then
              (case impl_self ctxt of NONE => self_outside_impl pos
               | SOME {self_type, report_reference, ...} =>
                   (if arities = [0] then () else mapping_error
                     "Self cannot take generic arguments" pos;
                    report_reference pos;
                    observe_signature_self ctxt false pos;
                    Navigation.defer_report ctxt pos Markup.keyword3;
                    SOME {meaning = the_default (Meaning_HOL self_type)
                      (impl_source_identity ctxt), evidence = SOME self_type, pos = pos}))
            else Option.map (fn ({typ, meaning}: resolved) =>
                {meaning = meaning, evidence = SOME (normalize typ), pos = pos})
              (parameter base arities pos)
        in
          case value of SOME value => value
          | NONE =>
              (case imported_type_path ctxt kind rows of
                 SOME (canonical_rows, (alias_pos, binding)) =>
                   let
                     val {base, positions, arities, arguments} = row_information canonical_rows
                     val value = source_registry base positions arities arguments pos
                       canonical_rows primitive
                     val _ = URust_Import_Scope.defer_use_reference ctxt alias_pos binding
                   in value end
               | NONE => source_registry base positions arities arguments pos rows primitive)
        end

      and source_registry base positions arities arguments pos rows primitive =
        let
          val active = lookup ctxt base
          val _ = dependency base active pos
        in
          case active of
            NONE =>
              let
                val meanings = map (fn (name, _, args) =>
                  (name, map (#meaning o opaque_argument) args)) rows
              in {meaning = (case primitive of SOME p => Meaning_Primitive p
                    | NONE => Meaning_Opaque meanings), evidence = NONE, pos = pos} end
          | SOME entry =>
              let
                val _ = if #segment_arities entry = arities then ()
                  else arity_error kind base (#segment_arities entry) arities pos
                val resolved = map2 source_argument (#parameter_kinds entry) arguments
                val _ = List.app (fn (argument, sort) => source_sort base sort argument)
                  (resolved ~~ #parameter_sorts entry)
                val substitutions = map_index (fn (index, ({evidence, ...}, sort)) =>
                  if member (op =) (#erased_parameters entry) index then SOME NONE
                  else Option.map (fn typ => SOME ((("_urust_type", index), sort), normalize typ)) evidence)
                  (resolved ~~ #parameter_sorts entry)
                val evidence = if forall is_some substitutions then
                    SOME (Term_Subst.instantiateT
                      (TVars.make (map_filter I (map the substitutions))) (#template entry))
                  else NONE
                val _ = if !source_schema_only then
                    (* This validation adds no carrier typing. A canonical entity reference
                       belongs to the terminal authored head, as in ordinary nominal use. *)
                    report_reference ctxt (the_default pos (try List.last positions)) base entry
                  else List.app (fn position => report_reference ctxt position base entry) positions
                val _ = if !source_schema_only then ()
                  else note_instantiated_origins ctxt pos (#meaning entry) arguments
              in {meaning = instantiate_meaning (map #meaning resolved) (#meaning entry),
                evidence = evidence, pos = pos} end
        end

      and source_type expected rust_type =
        let
          val value = (case rust_type of
              Group_Type (typ, _) =>
                let val value = source_type expected typ
                  val _ = if !source_schema_only then ()
                    else inherit_source_origins ctxt
                      (rust_type_position typ) (rust_type_position rust_type)
                in value end
            | Primitive_Type (primitive, pos) => source_nominal
                (rust_primitive_name primitive) [pos] [0] [] pos
                [(rust_primitive_name primitive, pos, [])] (SOME primitive)
            | Path_Type (segments, layout) =>
                let
                  val _ = check_type_path_start kind segments
                  val _ = (case segments of
                    Rust_Type_Path_Segment ("self", pos, _, _) :: _ =>
                      mapping_error "`self` cannot be used as a type" pos
                  | _ => ())
                  val rows = path_rows segments
                  val {base, positions, arities, arguments} = row_information rows
                in source_nominal base positions arities arguments (source_span layout) rows NONE end
            | Slice_Type (element, layout) =>
                let
                  val value = source_type (SOME Type_Parameter) element
                in {meaning = Meaning_Slice (#meaning value),
                  evidence = Option.map HOLogic.listT (#evidence value),
                  pos = source_span layout} end
            | Tuple_Type (types, layout) =>
                if !source_schema_only then
                  {meaning = Meaning_Tuple
                     (map (#meaning o source_type (SOME Type_Parameter)) types),
                   evidence = NONE, pos = source_span layout}
                else unsupported kind "this source type form in an erased argument"
                  (source_span layout)
            | Reference_Type (mode, _, element, layout) =>
                if !source_schema_only then
                  {meaning = Meaning_Reference
                     (mode, #meaning (source_type (SOME Type_Parameter) element)),
                   evidence = NONE, pos = source_span layout}
                else unsupported kind "this source type form in an erased argument"
                  (source_span layout)
            | Raw_Pointer_Type (mode, element, layout) =>
                if !source_schema_only then
                  {meaning = Meaning_Pointer
                     (mode, #meaning (source_type (SOME Type_Parameter) element)),
                   evidence = NONE, pos = source_span layout}
                else unsupported kind "this source type form in an erased argument"
                  (source_span layout)
            | Array_Type (element, length, layout) =>
                if !source_schema_only then
                  {meaning = Meaning_Array
                     (#meaning (source_type (SOME Type_Parameter) element),
                      #meaning (source_argument Const_Parameter (Rust_Numeric_Argument length))),
                   evidence = NONE, pos = source_span layout}
                else unsupported kind "this source type form in an erased argument"
                  (source_span layout)
            | Const_Array_Type (element, length, layout) =>
                if !source_schema_only then
                  {meaning = Meaning_Array
                     (#meaning (source_type (SOME Type_Parameter) element),
                      #meaning (source_type (SOME Const_Parameter) length)),
                   evidence = NONE, pos = source_span layout}
                else unsupported kind "this source type form in an erased argument"
                  (source_span layout)
            | HOL_Type_Source source =>
                if !source_schema_only then
                  (* A type escape is a type-role argument. Its checked HOL evidence is read
                     or replayed by the final retained field resolution, in the same frame. *)
                  {meaning = Meaning_Opaque [], evidence = NONE, pos = Input.pos_of source}
                else unsupported kind "this source type form in an erased argument"
                  (Input.pos_of source)
            | _ => unsupported kind "this source type form in an erased argument"
                (rust_type_position rust_type))
          val _ = case expected of NONE => () | SOME role =>
            if source_kind (#meaning value) = role then ()
            else unsupported kind (if role = Const_Parameter then "type parameters used as const arguments"
              else "const parameters used as type arguments") (#pos value)
          val _ = if !source_schema_only then ()
            else note_source_resolution ctxt (#meaning value) NONE (Rust_Type_Argument rust_type)
        in value end

      fun resolve_nominal base positions arities arguments pos primitive =
        (case (case resolve_generic ctxt normalize base arities pos of
            NONE => parameter base arities pos | value => value) of
           SOME value => value
         | NONE => registry_nominal base positions arities arguments pos primitive)

      and registry_nominal base positions arities arguments pos primitive =
             let
               val active = lookup ctxt base
               val _ = dependency base active pos
               val entry =
                 (case !selected_field of
                    NONE =>
                      (case active of SOME entry => entry
                       | NONE => unknown_type kind base pos)
                  | SOME (name, name_pos) =>
                      let
                        val view = case representation_entry ctxt base name of
                            SOME view => view
                          | NONE => mapping_error
                              ("unknown representation " ^ quote name ^ " for " ^ quote base)
                              name_pos
                        val entry = #entry view
                        (* Consume selection before entering retained argument resolution. *)
                        val _ = selected_field := NONE
                        val _ = Navigation.defer_report ctxt name_pos
                          (Position.make_entity_markup {def = false} (#identity entry)
                            (mappingN ^ "_representation")
                            (base ^ "::" ^ name, #name_pos view))
                      in entry end)
               val expected_arities = #segment_arities entry
               val _ =
                 if expected_arities = arities then ()
                 else arity_error kind base expected_arities arities pos
               fun resolve_argument (index, (argument, parameter_kind)) =
                 if member (op =) (#erased_parameters entry) index then
                   let val value = source_argument parameter_kind argument
                       val _ = source_sort base (nth (#parameter_sorts entry) index) value
                   in (#meaning value, NONE) end
                 else
                   let
                     val (value, argument_pos) =
                       (case (argument, parameter_kind) of
                          (Rust_Type_Argument argument, parameter_kind) =>
                            let
                              val value = resolve_type (SOME parameter_kind) argument
                              val pos = rust_type_position argument
                              val _ = if parameter_kind = Const_Parameter then
                                check_sort "const argument" (#typ value) \<^sort>\<open>len0\<close> pos else ()
                            in (value, pos) end
                        | (Rust_Numeric_Argument integer, Const_Parameter) =>
                            ({typ = length_literal ctxt integer,
                              meaning = Meaning_Numeric (unsigned_value integer)},
                              numeric_argument_position integer)
                        | (Rust_Numeric_Argument integer, Type_Parameter) =>
                            unsupported kind "numeric generic arguments for type parameters"
                              (numeric_argument_position integer)
                        | (Rust_Lifetime_Argument (Rust_Lifetime (_, pos)), _) =>
                            unsupported kind "lifetime generic arguments" pos
                        | (Rust_Associated_Type_Argument (_, pos, _), _) =>
                            unsupported kind "associated type bindings" pos
                        | (Rust_Const_Expression_Argument source, _) =>
                            unsupported kind "const expression generic arguments" (Input.pos_of source))
                     val sort = nth (#parameter_sorts entry) index
                     val _ = check_sort base (#typ value) sort argument_pos
                     val _ = note_source_resolution ctxt (#meaning value) (SOME (#typ value)) argument
                   in (#meaning value, SOME (index, sort, normalize (#typ value))) end
               val resolved_arguments = map_index resolve_argument (arguments ~~ #parameter_kinds entry)
               val parameter_sorts = #parameter_sorts entry
               val backend_sorts = #backend_parameter_sorts entry
               val roles = #backend_roles entry
               val retained = map_filter snd resolved_arguments
               val backend_types = backend (roles ~~ backend_sorts) pos
               val substitutions =
                 map (fn (index, sort, argument) =>
                     ((("_urust_type", index), sort), argument)) retained @
                 map
                   (fn (role, (sort, argument)) =>
                     ((Models.canonical role, sort), argument))
                   (roles ~~ (backend_sorts ~~ backend_types))
               val result =
                 Term_Subst.instantiateT
                   (TVars.make substitutions) (#template entry)
                 |> normalize
                 |> Proof_Context.cert_typ ctxt
               val terminal_pos =
                 (case rev positions of
                    terminal :: _ => terminal
                  | [] => pos)
               val _ =
                 (case result of
                    Type (name, _) =>
                      Navigation.defer_type ctxt terminal_pos name
                  | _ => ())
               (* Source-head navigation remains attached to its canonical declaration.
                  The option occurrence separately references the selected alternative. *)
               val _ = report_use ctxt base (the_default entry active) positions primitive
               val _ = note_instantiated_origins ctxt pos (#meaning entry) arguments
             in
               {typ = result,
                meaning = instantiate_meaning
                  (map fst resolved_arguments) (#meaning entry)}
             end

      (* Validate each source role before a wrapper can erase or wrap its meaning. Grouping
         retains the role, so a rejection points to the parameter rather than its parentheses. *)
      and resolve_type role rust_type =
        let
          val value = resolve_type_value role rust_type
          val _ =
            (case (#meaning value, role) of
               (Meaning_Parameter _, SOME Const_Parameter) =>
                 unsupported kind "type parameters used as const arguments"
                   (rust_type_position rust_type)
             | (Meaning_Const_Parameter _, SOME Type_Parameter) =>
                 unsupported kind "const parameters used as type arguments"
                   (rust_type_position rust_type)
             | (Meaning_Const_Parameter _, NONE) =>
                 unsupported kind "const parameters used as field types"
                   (rust_type_position rust_type)
             | (Meaning_Scoped_Parameter (_, actual), expected) =>
                 if actual = the_default Type_Parameter expected then ()
                 else unsupported kind
                   (if actual = Type_Parameter then "type parameters used as const arguments"
                    else if is_some expected then "const parameters used as type arguments"
                    else "const parameters used as field types")
                   (rust_type_position rust_type)
             | _ => ())
          val _ = note_source_resolution ctxt (#meaning value) (SOME (#typ value))
            (Rust_Type_Argument rust_type)
        in value end

      and resolve_type_value _
          (Primitive_Type (primitive, pos)) =
            resolve_nominal
              (rust_primitive_name primitive) [pos] [0] [] pos true
        | resolve_type_value _ (Path_Type (segments, layout)) =
            let
              val _ = check_type_path_start kind segments
              val rows = path_rows segments
              val {base, positions, arities, arguments} = row_information rows
              val pos = source_span layout
              val _ = List.app
                (fn Rust_Lifetime_Argument (Rust_Lifetime (_, pos)) =>
                      unsupported kind "lifetime generic arguments" pos
                  | Rust_Associated_Type_Argument (_, pos, _) =>
                      unsupported kind "associated type bindings" pos
                  | Rust_Const_Expression_Argument source =>
                      unsupported kind "const expression generic arguments" (Input.pos_of source)
                  | _ => ()) arguments
            in
              (case
                 (case resolve_self ctxt base arities pos of
                     NONE =>
                       (case resolve_generic ctxt normalize base arities pos of
                          NONE => parameter base arities pos | value => value)
                  | self => self) of
                 SOME value => value
               | NONE =>
                   (case imported_type_path ctxt kind rows of
                      SOME (canonical_rows, (alias_pos, binding)) =>
                        let
                          val {base, positions, arities, arguments} =
                            row_information canonical_rows
                          val value =
                            registry_nominal base positions arities arguments pos false
                          val _ = URust_Import_Scope.defer_use_reference ctxt alias_pos binding
                        in value end
                    | NONE =>
                        registry_nominal base positions arities arguments pos false))
            end
        | resolve_type_value _ (Tuple_Type (types, layout)) =
            if length types < 2
            then unsupported kind "singleton tuple types" (source_span layout)
            else
              let val resolved = map (resolve_type NONE) types in
                {typ =
                   fold_rev
                     (fn typ => fn rest => HOLogic.mk_prodT (typ, rest))
                     (map #typ resolved) \<^typ>\<open>tnil\<close>,
                 meaning = Meaning_Tuple (map #meaning resolved)}
              end
        | resolve_type_value role (group as Group_Type (typ, _)) =
            let val value = resolve_type role typ
              val _ = inherit_source_origins ctxt
                (rust_type_position typ) (rust_type_position group)
            in value end
        (* Function_Signature also resolves constructor turbofish arguments, but the generic lexer
           has no reference syntax, so only function signatures reach the mutable case. *)
        | resolve_type_value _ (Reference_Type (BM_Mut, _, target, layout)) =
            if signature_kind kind then
              let val target_type = resolve_type NONE target in
                {typ = reference_typ (#typ target_type) (source_span layout),
                 meaning = Meaning_Reference (BM_Mut, #meaning target_type)}
              end
            else unsupported kind "Rust reference types" (source_span layout)
        | resolve_type_value _ (Reference_Type (BM_Imm, _, target, layout)) =
            if signature_kind kind then
              let
                val target_type = resolve_type NONE target
                val pos = source_span layout
                val typ = (case shared_selection target (#meaning target_type) pos of
                    Shared_Value => #typ target_type
                  | Shared_Reference => reference_typ (#typ target_type) pos
                  | Shared_Readonly => readonly_typ (#typ target_type) pos)
              in {typ = typ, meaning = Meaning_Reference (BM_Imm, #meaning target_type)} end
            else unsupported kind "Rust reference types" (source_span layout)
        | resolve_type_value _ (Raw_Pointer_Type (mutability, target, layout)) =
            let val target_type = resolve_type NONE target in
              {typ = reference_typ (#typ target_type) (source_span layout),
               meaning = Meaning_Pointer (mutability, #meaning target_type)}
            end
        | resolve_type_value _ (Slice_Type (element, _)) =
            let val resolved = resolve_type (SOME Type_Parameter) element
            in {typ = HOLogic.listT (#typ resolved), meaning = Meaning_Slice (#meaning resolved)} end
        | resolve_type_value _ (Array_Type (element, integer, layout)) =
            let val length = length_literal ctxt integer in
              resolve_array (resolve_type NONE element)
                {typ = length, meaning = Meaning_Numeric (unsigned_value integer)} (source_span layout)
            end
        | resolve_type_value _ (Const_Array_Type (element, length, layout)) =
            let
              val resolved = resolve_type NONE element
              val resolved_length = resolve_type (SOME Const_Parameter) length
            in resolve_array resolved resolved_length (source_span layout) end
        | resolve_type_value _ (Function_Type (_, _, layout)) =
            unsupported kind "Rust function pointer types" (source_span layout)
        | resolve_type_value _ (Impl_Trait_Type (_, layout)) =
            unsupported kind "Rust impl Trait types" (source_span layout)
        | resolve_type_value _ (Macro_Type (_, pos)) =
            unsupported kind "unexpanded Rust macro types" pos
        | resolve_type_value _ (HOL_Type_Source source) =
            let val typ = read_escape source in
              {typ = typ, meaning = Meaning_HOL typ}
            end
      and resolve_array ({typ = element_type, meaning = element}: resolved)
          ({typ = length_type, meaning = length}: resolved) pos =
        let
          val _ = check_sort "fixed array length" length_type \<^sort>\<open>len\<close> pos
          val typ = Type (\<^type_name>\<open>array\<close>, [element_type, normalize length_type])
        in {typ = typ, meaning = Meaning_Array (element, length)} end
      fun call_argument ({kind = expected, witness, sort}: argument_specification) argument =
        (if not witness then
             let
               val value = source_argument expected argument
               val _ = source_sort "function argument" sort value
             in {typ = NONE, evidence = #evidence value, meaning = #meaning value, pos = #pos value} end
         else
             let
               val (value, pos) = case argument of
                   Rust_Type_Argument typ => (resolve_type (SOME expected) typ, rust_type_position typ)
                 | Rust_Numeric_Argument integer =>
                     if expected = Const_Parameter then
                       ({typ = length_literal ctxt integer,
                         meaning = Meaning_Numeric (unsigned_value integer)},
                        integer_literal_position integer)
                     else unsupported kind "numeric generic arguments for type parameters"
                       (integer_literal_position integer)
                 | _ => (ignore (source_argument expected argument);
                     raise Fail "unsupported source argument survived validation")
             in {typ = SOME (#typ value), evidence = SOME (#typ value), meaning = #meaning value, pos = pos} end)
      fun field (selection, escapes, rust_type) =
        let
          val _ = selected_field := selection
          val _ = captured_escapes := escapes
          val result = resolve_type NONE rust_type
          val _ = if is_none (!selected_field) then ()
            else mapping_error "field representation did not reach an outer nominal mapping"
              (snd (the (!selected_field)))
          val _ = captured_escapes := []
        in result end
    in {types = map (resolve_type NONE), fields = map field,
      schema_arguments = fn kinds => fn arguments =>
        Unsynchronized.setmp source_schema_only true
          (fn () => ignore (map2 source_argument kinds arguments)) (),
      arguments = fn specifications => fn arguments => map2 call_argument specifications arguments} end

  fun resolve_values kind ctxt read_escape check_sort normalize backend parameter dependency rust_types =
    #types (resolve_value_operations kind ctxt read_escape check_sort normalize backend
      parameter dependency) rust_types

  fun no_parameter _ _ _ = NONE
  fun no_dependency _ _ _ = ()

  fun finish_backend ctxt normalize slots types =
    let
      val roles = role_order (map fst slots)
      val all_roles = role_order ([Address, Global] @ roles)
      val names =
        Name.variants (Variable.names_of ctxt)
          (map (fn Address => "'urust_address" | Global => "'urust_global"
            | Model family => "'urust_model_" ^ family) all_roles)
      fun parameter (typ as TVar (_, sort)) =
            (typ, sort)
        | parameter (typ as TFree (_, sort)) = (typ, sort)
        | parameter _ =
            raise Fail
              "uRust type registry: backend parameter became a concrete type"
      val normalized = map (apsnd normalize) slots
        |> filter (fn (_, TVar _) => true | (_, TFree _) => true | _ => false)
        |> map (apsnd parameter)
      val parameters = map (fn (role, (TFree parameter, _)) => (role, parameter)
        | (role, (_, sort)) => (role,
            (the (AList.lookup (op =) (all_roles ~~ names) role), sort))) normalized
      val substitutions =
        map2 (fn (_, (typ, _)) => fn (_, parameter) => (typ, TFree parameter))
          normalized parameters
      val result =
        map
          (normalize #>
            Term.typ_subst_atomic substitutions #>
            Proof_Context.cert_typ ctxt)
          types
    in
      {types = result, backend_parameters = parameters}
    end

  (* An impl target needs names for every role-owned hole, including holes nested inside an
     explicitly selected representation. Its source/escape holes remain untouched and rigid
     context types retain their identity. Datatype schemes use the atomic-role codec above. *)
  fun finish_impl_backend ctxt normalize slots types =
    let
      val normalized = map (apsnd normalize) slots
      val nested = exists (fn (_, Type (_, children)) =>
            not (null (fold Term.add_tvarsT children [])) | _ => false) normalized
    in
      if not nested then #types (finish_backend ctxt normalize slots types)
      else
        let
          val roles = role_order ([Address, Global] @ map fst normalized)
          val names = Name.variants (Variable.names_of ctxt)
            (map (fn Address => "'urust_address" | Global => "'urust_global"
              | Model family => "'urust_model_" ^ family) roles)
          val reserved = fold Name.declare names (Variable.names_of ctxt)
          fun role (role, typ) (substitutions, used) =
            let
              val primary = the (AList.lookup (op =) (roles ~~ names) role)
              fun variable (index, variable as (_, sort)) (substitutions, used) =
                if exists (fn (T, _) => T = TVar variable) substitutions
                then (substitutions, used)
                else
                  let val (name, used) = if index = 0 then (primary, used)
                        else Name.variant (primary ^ string_of_int index) used
                  in ((TVar variable, TFree (name, sort)) :: substitutions, used) end
            in fold variable (map_index I (rev (Term.add_tvarsT typ [])))
              (substitutions, used) end
          val (substitutions, _) = fold role normalized ([], reserved)
        in map (normalize #> Term.typ_subst_atomic substitutions #>
          Proof_Context.cert_typ ctxt) types end
    end

  (* Datatypes and functions share the positioned override reader and name checks. Sort
     inference remains with each declaration's existing resolution environment. *)
  fun read_parameter_names_with checked ctxt parameters overrides =
    let
      fun descriptor (Generic_Parameter (name, pos, kind)) = (name, pos, kind)
      val descriptors = map descriptor parameters
      val _ = case duplicates (op =) (map #1 descriptors) of [] => ()
        | name :: _ => mapping_error ("duplicate parameter " ^ quote name)
            (#2 (the (find_first (fn (n, _, _) => n = name) descriptors)))
      val _ = fold (fn ((name, pos), _) => fn seen =>
        (case AList.lookup (op =) seen name of
           NONE => (name, pos) :: seen
         | SOME previous => error ("urust_type: duplicate parameter override " ^ quote name ^
             Position.here_list [previous, pos]))) overrides []
      val _ = List.app (fn ((name, pos), _) =>
        if exists (fn (n, _, _) => n = name) descriptors then ()
        else mapping_error ("unknown parameter override " ^ quote name) pos) overrides
      fun parameter_name (name, pos, kind) =
        let
          val minimum = case kind of Type_Parameter => \<^sort>\<open>type\<close>
            | Const_Parameter => \<^sort>\<open>len0\<close>
          val explicit = AList.lookup (op =) (map (apfst fst) overrides) name
          val declared = case explicit of NONE => checked name | SOME (raw, override_pos) =>
            SOME (Syntax.read_typ ctxt raw handle ERROR message => mapping_error message override_pos)
          val (hol_name, sort) = case declared of NONE =>
              ("'" ^ String.map Char.toLower name, minimum)
            | SOME (TFree parameter) => parameter
            | SOME _ => mapping_error "parameter overrides require a HOL type variable and sort" pos
        in {hol = (hol_name, sort), declared = declared, pos = pos} end
      val names = map parameter_name descriptors
      val _ = if length names = length (distinct (op =) (map (fst o #hol) names)) then ()
        else mapping_error "HOL parameter names must be distinct"
          (#pos (hd names))
    in names end

  fun read_parameter_names ctxt parameters overrides =
    read_parameter_names_with (K NONE) ctxt parameters overrides

  fun parameter_names ctxt parameters overrides =
    map #hol (read_parameter_names ctxt parameters overrides)

  fun ambient_parameter_names ctxt parameters overrides =
    let
      val _ = List.app (fn ((rust, pos), _) =>
        if is_some (Models.ambient ctxt rust) then
          Models.error_at ("ambient and HOL-name overrides both bind " ^ quote rust) pos else ()) overrides
      (* Ambient connections already contain checked rigid types. Keep their identity directly;
         pretty-printed types contain markup and are neither source nor an inference seam. *)
      fun checked rust = Option.map #typ (Models.ambient ctxt rust)
    in map #hol (read_parameter_names_with checked ctxt parameters overrides) end

  fun resolve_declaration_roles_with_representations ctxt parameters overrides fields =
    let
      fun prepare (NONE, T) = (NONE, [], T, [], NONE)
        | prepare (SOME selection, T) =
            let val (expanded, validations, escapes, provenance) =
              expand_field_representation ctxt
                (map (fn Generic_Parameter (name, _, _) => name) parameters) selection T
            in (SOME (#representation provenance, snd selection), escapes, expanded,
              validations, SOME provenance) end
      val prepared = map prepare fields
      fun descriptor (Generic_Parameter (name, pos, kind)) = (name, pos, kind)
      val descriptors = map descriptor parameters
      val names = map (fn {hol = (name, _), declared, pos} => (name, declared, pos))
        (read_parameter_names ctxt parameters overrides)
      val {fresh, normalize, check_sort, backend, backend_slots, ...} =
        inference_state Datatype_Fields (Declaration_Parameter_Names.put (map #1 names) ctxt) []
      fun parameter_type ((name, pos, kind), (_, declared, _)) =
        let
          val minimum = case kind of Type_Parameter => \<^sort>\<open>type\<close>
            | Const_Parameter => \<^sort>\<open>len0\<close>
          val sort = case declared of SOME (TFree (_, sort)) => sort | _ => minimum
          val slot = fresh sort
          val _ = check_sort name slot minimum pos
        in (name, slot) end
      val slots = map parameter_type (descriptors ~~ names)
      val _ = if length names = length (distinct (op =) (map #1 names)) then ()
        else mapping_error "HOL parameter names must be distinct" Position.none
      fun parameter name arities pos =
        Option.map (fn typ =>
          (if arities = [0] then () else mapping_error "parameters cannot take generic arguments" pos;
           Navigation.defer_report ctxt pos Markup.tfree;
           let
             val index = find_index (fn (n, _) => n = name) slots
             val kind = #3 (nth descriptors index)
           in {typ = typ, meaning = (case kind of Type_Parameter => Meaning_Parameter index
             | Const_Parameter => Meaning_Const_Parameter index)} end))
          (AList.lookup (op =) slots name)
      fun escape source =
        let
          val typ =
            URust_Report_Transaction.native ctxt
              (fn read_ctxt => Syntax.read_typ read_ctxt (Syntax.implode_input source))
          val variables = Term.add_tfreesT typ []
          val _ = if null (Term.add_tvarsT typ []) then () else
            mapping_error "schematic variables are not declaration parameters" (Input.pos_of source)
          fun substitute (variable as (name, sort)) =
            case find_index (fn (n, _, _) => n = name) names of
              ~1 => mapping_error "unrelated HOL variable in datatype field" (Input.pos_of source)
            | index => let val slot = snd (nth slots index)
                  val _ = check_sort name slot sort (Input.pos_of source)
                in (TFree variable, slot) end
        in Term.typ_subst_atomic (map substitute variables) typ end
      val operations = resolve_value_operations Datatype_Fields ctxt escape check_sort normalize backend
        parameter no_dependency
      (* Every alias source slot is checked even if expansion drops it. Its old carrier's
         sorts are deliberately absent; the selected template checks retained witnesses. *)
      val _ = List.app (fn (_, _, _, validations, _) =>
        List.app (fn (kinds, arguments) =>
          #schema_arguments operations kinds arguments)
          validations) prepared
      val resolved = #fields operations
        (map (fn (selection, escapes, T, _, _) => (selection, escapes, T)) prepared)
      fun finish_parameter ((_, slot), (name, declared, pos)) =
        case normalize slot of TVar (_, sort) =>
          let
            val sort = Sign.minimize_sort (Proof_Context.theory_of ctxt) sort
            val _ = case declared of NONE => () | SOME typ =>
              if Sign.of_sort (Proof_Context.theory_of ctxt) (typ, sort) then ()
              else mapping_error "parameter override does not satisfy inferred sort" pos
          in (normalize slot, (name, sort)) end
        | _ => mapping_error "parameter inference produced a concrete type" pos
      val inferred = map finish_parameter (slots ~~ names)
      val substitutions = map (fn (slot, parameter) => (slot, TFree parameter)) inferred
      val normalized_types = map (Term.typ_subst_atomic substitutions o normalize o #typ) resolved
      val backend_context = fold (Variable.declare_typ o TFree o snd) inferred ctxt
      val {types, backend_parameters} = finish_backend backend_context normalize (backend_slots ()) normalized_types
    in {types = types, source_parameters = map snd inferred, backend_parameters = backend_parameters,
      representations = map #5 prepared} end

  fun resolve_declaration_roles ctxt parameters overrides rust_types =
    let val {types, source_parameters, backend_parameters, ...} =
      resolve_declaration_roles_with_representations ctxt parameters overrides
        (map (pair NONE) rust_types)
    in {types = types, source_parameters = source_parameters,
      backend_parameters = backend_parameters} end

  fun resolve_fields ctxt rust_types =
    let
      val {normalize, check_sort, backend, backend_slots, ...} =
        inference_state Datatype_Fields ctxt []
      val resolved =
        resolve_values Datatype_Fields ctxt (read_hol_escape ctxt)
          check_sort normalize backend no_parameter no_dependency rust_types
      val {types, backend_parameters} =
        finish_backend ctxt normalize (backend_slots ()) (map #typ resolved)
    in {types = types, backend_parameters = map snd backend_parameters} end

  fun resolve_declaration ctxt parameters overrides rust_types =
    let val {types, source_parameters, backend_parameters} =
      resolve_declaration_roles ctxt parameters overrides rust_types
    in {types = types, source_parameters = source_parameters,
      backend_parameters = map snd backend_parameters} end

  fun resolve ctxt rust_type =
    the_single (#types (resolve_fields ctxt [rust_type]))

  (* Immediate type operands in source order, for the source-ordered signature walks below. *)
  fun rust_type_operands (Path_Type (segments, _)) =
        let
          fun argument (Rust_Type_Argument typ) = SOME typ
            | argument (Rust_Numeric_Argument _) = NONE
            | argument (Rust_Lifetime_Argument _) = NONE
            | argument (Rust_Associated_Type_Argument (_, _, typ)) = SOME typ
            | argument (Rust_Const_Expression_Argument _) = NONE
          fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
            map_filter argument (the_default [] arguments)
        in maps segment segments end
    | rust_type_operands (Tuple_Type (types, _)) = types
    | rust_type_operands (Group_Type (typ, _)) = [typ]
    | rust_type_operands (Reference_Type (_, _, typ, _)) = [typ]
    | rust_type_operands (Raw_Pointer_Type (_, typ, _)) = [typ]
    | rust_type_operands (Slice_Type (typ, _)) = [typ]
    | rust_type_operands (Array_Type (typ, _, _)) = [typ]
    | rust_type_operands (Const_Array_Type (typ, length, _)) = [typ, length]
    | rust_type_operands (Function_Type (parameters, result, _)) =
        parameters @ the_list result
    | rust_type_operands (Impl_Trait_Type (typ, _)) = [typ]
    | rust_type_operands (Macro_Type _) = []
    | rust_type_operands (Primitive_Type _) = []
    | rust_type_operands (HOL_Type_Source _) = []

  fun with_shared_references renames parameters result ctxt =
    let
      val _ = Models.distinct_keys "shared-reference override" renames
      fun error_at message pos = error ("urust: " ^ message ^ Position.here pos)
      fun borrow_positions typ =
        (case typ of
           Reference_Type (BM_Imm, _, _, layout) =>
             let
               val pos = source_span layout
               val _ = if is_some (Position.offset_of pos) then ()
                 else error_at "shared-reference slot requires located borrow syntax" pos
             in [pos] end
         | _ => []) @ maps borrow_positions (rust_type_operands typ)
      fun slot key pos =
        if key = "result" then SOME result
        else if String.isPrefix "arg:" key then
          let
            val digits = String.extract (key, 4, NONE)
            val index = (case Int.fromString digits of
                SOME index => if index >= 0 andalso string_of_int index = digits then index
                  else ~1
              | NONE => ~1)
          in
            if index >= 0 andalso index < length parameters then SOME (nth parameters index)
            else error_at ("unknown shared-reference slot " ^ quote key) pos
          end
        else NONE
      fun read ((key, key_pos), source) (positions, generics) =
        let val selection = read_shared_policy ctxt source
        in
          (case slot key key_pos of
             SOME typ => (map (fn pos => (pos, selection)) (borrow_positions typ) @ positions, generics)
           | NONE =>
               if String.isPrefix "type:" key andalso size key > 5 then
                 (positions, ((String.extract (key, 5, NONE), key_pos), selection) :: generics)
               else error_at ("unknown shared-reference key " ^ quote key) key_pos)
        end
      val (positions, generic_names) = fold read renames ([], [])
    in
      Shared_References.put
        {positions = positions, generic_names = rev generic_names,
         generics = #generics (Shared_References.get ctxt)} ctxt
    end

  fun prepare_shared_references parameters result ctxt =
    ctxt |> with_shared_references (Shared_Reference_Overrides.get ctxt) parameters result
      |> activate_shared_references

  fun prepare_impl_shared_references ctxt =
    let
      val _ = List.app (fn ((key, pos), _) =>
        if String.isPrefix "type:" key andalso size key > 5 then ()
        else error ("urust: impl shared_references accepts only type:NAME keys" ^
          Position.here pos)) (Shared_Reference_Overrides.get ctxt)
    in prepare_shared_references [] (Primitive_Type (DPT_Unit, Position.none)) ctxt end

  (* Check lexical Rust restrictions without interpreting any retained type. The operand walk
     includes function-pointer types, impl Trait and associated-type binding values. Const-expression
     and HOL source escapes retain their own syntax and are not Rust type paths. *)
  fun check_signature_syntax_with_self lexical_self ctxt rust_types =
    let
      fun key name pos =
        (case Micro_Rust_Names.reserved_key_segment {bare_self = false} name of
           SOME segment =>
             error ("urust_fn: " ^ Micro_Rust_Names.reserved_key_message segment ^ Position.here pos)
         | NONE => ())
      fun binding (Rust_Associated_Type_Argument (name, pos, _)) = key name pos
        | binding _ = ()
      fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
        List.app binding (the_default [] arguments)
      fun check (typ as Path_Type (segments, _)) =
            let
              val _ = check_type_path_start Function_Signature segments
              val _ =
                (case segments of
                   Rust_Type_Path_Segment ("Self", pos, arguments, _) :: _ =>
                     (case impl_self ctxt of
                        NONE => if lexical_self then
                          if null (the_default [] arguments) then ()
                          else error ("urust: Self cannot take generic arguments" ^ Position.here pos)
                        else self_outside_impl pos
                      | SOME _ =>
                          if null (the_default [] arguments) then ()
                          else error ("urust: Self cannot take generic arguments" ^ Position.here pos))
                 | Rust_Type_Path_Segment (name, pos, _, _) :: _ => key name pos
                 | [] => ())
              val _ = List.app segment segments
            in List.app check (rust_type_operands typ) end
        | check typ = List.app check (rust_type_operands typ)
    in List.app check rust_types end

  val check_signature_syntax = check_signature_syntax_with_self false

  fun hol_sources (HOL_Type_Source source) = [source]
    | hol_sources typ = maps hol_sources (rust_type_operands typ)

  fun lifetime_uses (Reference_Type (_, SOME lifetime, typ, _)) = lifetime :: lifetime_uses typ
    | lifetime_uses (Path_Type (segments, _)) =
        let
          fun argument (Rust_Lifetime_Argument lifetime) = [lifetime]
            | argument (Rust_Type_Argument typ) = lifetime_uses typ
            | argument (Rust_Associated_Type_Argument (_, _, typ)) = lifetime_uses typ
            | argument _ = []
          fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
            maps argument (the_default [] arguments)
        in maps segment segments end
    | lifetime_uses typ = maps lifetime_uses (rust_type_operands typ)

  fun reserved_lifetime name = name = "'static" orelse name = "'_"

  (* Rust scope rules for lifetime parameters, checked before the erased types are resolved:
     reserved names cannot be declared, declarations are distinct and every named use is declared. *)
  fun check_lifetimes declared rust_types =
    let
      fun declare (Rust_Lifetime (name, pos)) scope =
        if reserved_lifetime name then
          error
            ("urust_fn: " ^ quote name ^ " cannot be declared as a lifetime parameter" ^
              Position.here pos)
        else
          (case Symtab.lookup scope name of
             SOME first =>
               error
                 ("urust_fn: duplicate lifetime parameter " ^ quote name ^
                   Position.here_list [first, pos])
           | NONE => Symtab.update (name, pos) scope)
      val scope = fold declare declared Symtab.empty
      fun check (Rust_Lifetime (name, pos)) =
        if reserved_lifetime name orelse Symtab.defined scope name then ()
        else error ("urust_fn: undeclared lifetime " ^ quote name ^ Position.here pos)
    in List.app check (maps lifetime_uses rust_types) end

  structure Header_Lifetimes = Proof_Data
  (
    type T = (Position.T * serial) Symtab.table
    fun init _ = Symtab.empty
  )

  fun declare_header_lifetime ctxt (Rust_Lifetime (name, pos)) scope =
    if reserved_lifetime name then
      error ("urust_fn: " ^ quote name ^ " cannot be declared as a lifetime parameter" ^
        Position.here pos)
    else
      (case Symtab.lookup scope name of
         SOME (first, _) => error ("urust_fn: duplicate lifetime parameter " ^ quote name ^
           Position.here_list [first, pos])
       | NONE =>
           let val identity = serial ()
             val _ = Navigation.defer_report ctxt pos
               (Position.make_entity_markup {def = true} identity "urust_lifetime" (name, pos))
           in Symtab.update (name, (pos, identity)) scope end)

  fun with_header_lifetimes lifetimes ctxt = Header_Lifetimes.put
    (fold (declare_header_lifetime ctxt) lifetimes (Header_Lifetimes.get ctxt)) ctxt

  fun inherit_header_lifetimes source = Header_Lifetimes.put (Header_Lifetimes.get source)

  (* Definite type/const positions are shared by ignored headers and erased outlives heads.
     Bare nominal arguments stay kind-neutral: the HOL registry is not Rust name resolution. *)
  fun check_type_kinds kind_of (purpose as (type_position, _)) (Path_Type (segments, _)) =
        let
          val _ =
            (case segments of
               Rust_Type_Path_Segment (name, pos, _, _) :: _ =>
                 if kind_of name = SOME Const_Parameter then
                   error ("urust_fn: const parameters cannot be used as " ^ type_position ^
                     Position.here pos)
                 else ()
             | _ => ())
        in check_generic_kinds kind_of purpose segments end
    | check_type_kinds kind_of (purpose as (_, const_position)) (Const_Array_Type (element, length, _)) =
        (check_type_kinds kind_of purpose element;
         case length of
           Path_Type ([Rust_Type_Path_Segment (name, pos, NONE, _)], _) =>
             if kind_of name = SOME Type_Parameter then
               error ("urust_fn: type parameters cannot be used as const " ^ const_position ^
                 Position.here pos)
             else ()
         | _ => ())
    | check_type_kinds kind_of purpose typ =
        List.app (check_type_kinds kind_of purpose) (rust_type_operands typ)
  and check_generic_kinds kind_of purpose segments =
        let
          fun argument (Rust_Associated_Type_Argument (_, _, typ)) = check_type_kinds kind_of purpose typ
            | argument (Rust_Type_Argument (Path_Type (nested, _))) = check_generic_kinds kind_of purpose nested
            | argument (Rust_Type_Argument typ) = check_type_kinds kind_of purpose typ
            | argument _ = ()
          fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
            List.app argument (the_default [] arguments)
        in List.app segment segments end

  fun scope_parameter_kind ctxt name =
    Option.map #kind (find_first (fn ({rust, ...}: generic_parameter) => rust = name)
      (scope_parameters ctxt))

  (* No type/source resolution, reports, observers or inference belong to this syntax-only
     context. Opaque model/macro/const payloads cannot establish Rust expansion or body bindings. *)
  fun check_outlives_head ctxt head =
    let
      fun unsupported description pos = error
        ("urust_fn: " ^ description ^ " is not supported in authoritative outlives heads" ^
          Position.here pos)
      fun argument (Rust_Type_Argument typ) = visit typ
        | argument (Rust_Associated_Type_Argument (_, pos, _)) =
            unsupported "associated type bindings" pos
        | argument _ = ()
      and visit (Path_Type (segments, _)) =
            let
              val _ = List.app (fn Rust_Type_Path_Segment (name, pos, _, _) =>
                if name = "_" then unsupported "Rust inference holes" pos else ()) segments
              val _ = (case segments of Rust_Type_Path_Segment (name, pos, arguments, _) :: rest =>
                  if name = "Self" orelse is_some (scope_parameter_kind ctxt name) then
                    (if null rest then () else unsupported "associated paths on scoped parameters" pos;
                     if null (the_default [] arguments) then ()
                     else error ("urust: generic parameter " ^ name ^
                       " takes no generic arguments" ^ Position.here pos))
                  else ()
                | [] => ())
            in List.app (fn Rust_Type_Path_Segment (_, _, arguments, _) =>
              List.app argument (the_default [] arguments)) segments end
        | visit (Impl_Trait_Type (_, layout)) =
            unsupported "impl Trait" (source_span layout)
        | visit typ = List.app visit (rust_type_operands typ)
      val _ = check_signature_syntax ctxt [head]
      val _ = check_type_kinds (scope_parameter_kind ctxt) ("type where heads", "where operands") head
    in visit head end

  (* Header validation extends the immutable inherited lifetime context. Bound-local binders
     still have their own isolated environment and do not escape. Impl predicate Self has
     lexical scope before the single target resolution; no checked Self is manufactured. *)
  fun check_header impl_header ctxt function =
    let
      fun declare (lifetime as Rust_Lifetime (name, pos)) scope =
        (case Symtab.lookup (Header_Lifetimes.get ctxt) name of
           SOME (old, _) => if Position.properties_of old = Position.properties_of pos then scope
             else declare_header_lifetime ctxt lifetime scope
         | NONE => declare_header_lifetime ctxt lifetime scope)
      val scope = fold declare (function_lifetime_parameters function) (Header_Lifetimes.get ctxt)
      val descriptors = function_type_parameters function
      fun local_kind name =
        (case get_first (fn Generic_Parameter (rust, _, kind) =>
          if rust = name then SOME kind else NONE) descriptors of
           SOME kind => SOME kind | NONE => scope_parameter_kind ctxt name)
      val type_kind = check_type_kinds local_kind
      val generic_kinds = check_generic_kinds local_kind
      fun use outlives scope (Rust_Lifetime (name, pos)) =
        if outlives andalso name = "'_" then
          error ("urust_fn: placeholder lifetime " ^ quote name ^ " is not allowed in bounds" ^
            Position.here pos)
        else if reserved_lifetime name then ()
        else
          (case Symtab.lookup scope name of
             NONE => error ("urust_fn: undeclared lifetime " ^ quote name ^ Position.here pos)
           | SOME (declaration, identity) =>
               Navigation.defer_report ctxt pos
                 (Position.make_entity_markup {def = false} identity "urust_lifetime"
                   (name, declaration)))
      fun binder scope lifetimes =
        let
          val local_scope = fold declare lifetimes Symtab.empty
          val _ = List.app (fn (Rust_Lifetime (name, pos)) =>
            case Symtab.lookup scope name of
              NONE => ()
            | SOME (first, _) =>
                error ("urust_fn: bound lifetime " ^ quote name ^
                  " shadows an enclosing lifetime" ^ Position.here_list [first, pos])) lifetimes
        in Symtab.fold Symtab.update local_scope scope end
      fun typ check_syntax strict scope rust_type =
        let
          fun visit _ (Function_Type (inputs, output, _)) =
                List.app (visit NONE) (inputs @ the_list output)
            | visit context (Reference_Type (_, lifetime, nested, layout)) =
                (case (context, lifetime) of
                   (SOME purpose, NONE) =>
                     error ("urust_fn: reference lifetime must be explicit in a " ^ purpose ^
                       Position.here (the_default (source_span layout)
                         (try hd (source_token_positions layout Operator_Token))))
                 | (_, SOME lifetime) => (use (is_some context) scope lifetime; visit context nested)
                 | _ => visit context nested)
            | visit context (Path_Type (segments, _)) =
                let
                  fun argument (Rust_Lifetime_Argument lifetime) = use (is_some context) scope lifetime
                    | argument (Rust_Type_Argument typ) = visit context typ
                    | argument (Rust_Associated_Type_Argument (_, _, typ)) = visit context typ
                    | argument _ = ()
                  fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
                    List.app argument (the_default [] arguments)
                in List.app segment segments end
            | visit context typ = List.app (visit context) (rust_type_operands typ)
          val _ = if check_syntax then
            check_signature_syntax_with_self (impl_header andalso is_some strict) ctxt [rust_type]
            else ()
        in visit strict rust_type end
      (* Callable elision uses only source-visible input lifetime occurrences. Function pointers
         introduce their own binder boundary; external nominal/alias lifetime inference is not
         performed for ignored header types. *)
      fun callable_lifetimes (Function_Type _) = []
        | callable_lifetimes (Reference_Type (_, lifetime, nested, layout)) =
            (case lifetime of
               SOME (Rust_Lifetime (_, pos)) => [pos]
             | NONE => [the_default (source_span layout)
                 (try hd (source_token_positions layout Operator_Token))]) @
            callable_lifetimes nested
        | callable_lifetimes (Path_Type (segments, _)) =
            let
              fun argument (Rust_Lifetime_Argument (Rust_Lifetime (_, pos))) = [pos]
                | argument (Rust_Type_Argument typ) = callable_lifetimes typ
                | argument (Rust_Associated_Type_Argument (_, _, typ)) = callable_lifetimes typ
                | argument _ = []
              fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
                maps argument (the_default [] arguments)
            in maps segment segments end
        | callable_lifetimes typ = maps callable_lifetimes (rust_type_operands typ)
      fun elided_result (Function_Type _) = []
        | elided_result (Reference_Type (_, NONE, nested, layout)) =
            the_default (source_span layout)
              (try hd (source_token_positions layout Operator_Token)) :: elided_result nested
        | elided_result (Reference_Type (_, SOME (Rust_Lifetime ("'_", pos)), nested, _)) =
            pos :: elided_result nested
        | elided_result (Path_Type (segments, _)) =
            let
              fun argument (Rust_Lifetime_Argument (Rust_Lifetime ("'_", pos))) = [pos]
                | argument (Rust_Type_Argument typ) = elided_result typ
                | argument (Rust_Associated_Type_Argument (_, _, typ)) = elided_result typ
                | argument _ = []
              fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
                maps argument (the_default [] arguments)
            in maps segment segments end
        | elided_result typ = maps elided_result (rust_type_operands typ)
      fun callable_result inputs output =
        (case maps elided_result (the_list output) of
           pos :: _ =>
             if length (maps callable_lifetimes inputs) = 1 then ()
             else error ("urust_fn: callable result lifetime must be explicit when its inputs " ^
               "do not contain exactly one source lifetime" ^ Position.here pos)
         | [] => ())
      fun path scope segments layout =
        typ true NONE scope (Path_Type (map (fn (name, pos) =>
          Rust_Type_Path_Segment (name, pos, NONE, make_source_layout pos [])) segments, layout))
      fun bound scope (Rust_Trait_Bound (segments, layout)) = path scope segments layout
        | bound scope (Rust_Generic_Trait_Bound (rust_type, _)) =
            (case rust_type of
               Path_Type (segments, _) =>
                 generic_kinds ("generic trait type operands", "generic trait operands") segments
             | _ => ();
             typ true (SOME "generic trait bound") scope rust_type)
        | bound scope (Rust_Callable_Bound (segments, inputs, output, layout)) =
            (path scope segments layout;
             List.app (type_kind ("callable type operands", "callable operands"))
               (inputs @ the_list output);
             List.app (typ true NONE scope) (inputs @ the_list output);
             callable_result inputs output)
        | bound scope (Rust_Outlives_Bound lifetime) = use true scope lifetime
        | bound scope (Rust_Const_Bound (nested, _)) = bound scope nested
        | bound scope (Rust_For_Bound (lifetimes, nested, _)) = bound (binder scope lifetimes) nested
      fun predicate scope (Rust_Type_Predicate (head, bounds, _)) =
            (type_kind ("type where heads", "where operands") head;
             typ true (SOME "where predicate") scope head; List.app (bound scope) bounds)
        | predicate scope (Rust_Lifetime_Predicate (head, bounds, _)) =
            (use true scope head; List.app (bound scope) bounds)
        | predicate scope (Rust_For_Predicate (lifetimes, nested, _)) =
            predicate (binder scope lifetimes) nested
      fun parameter (Generic_Lifetime_Bounds (_, bounds, _)) = List.app (bound scope) bounds
        | parameter (Generic_Type (_, _, bounds)) = List.app (bound scope) bounds
        | parameter (Generic_Const (_, _, rust_type)) =
            (type_kind ("const declaration types", "const declaration operands") rust_type;
             typ true NONE scope rust_type)
        | parameter _ = ()
      (* Parameter/receiver preparation keeps its established smallest-token diagnostics; common
         header traversal checks their lifetime scope without preempting that syntax owner. *)
      fun formal (Function_Parameter (_, _, rust_type, _)) = typ false NONE scope rust_type
        | formal (Receiver_Parameter (Receiver_Ref {lifetime, ...}, _, _)) =
            Option.app (use false scope) lifetime
        | formal _ = ()
      val {parameters, where_clause, ...} = function_generics function
    in
      List.app parameter parameters;
      List.app (predicate scope) where_clause;
      List.app formal (function_parameters function);
      Option.app (typ false NONE scope) (function_return_type function)
    end

  val check_function_header = check_header false
  val check_impl_header = check_header true

  datatype channel_source =
      Authored_Channel of Input.source
    | Inherited_Channel of {label: string, source: Input.source, use_pos: Position.T}

  type function_channels =
    {state: channel_source option, abort: channel_source option,
     input: channel_source option, output: channel_source option}

  type signature_read = {source: Input.source, cited: Position.T list, label: string option}

  fun authored_read source : signature_read =
    {source = source, cited = [Input.pos_of source], label = NONE}

  (* An inherited source belongs to the earlier command that declared the scoped default. It is
     read without positions, so neither its parse nor the repeated read reports into that command;
     failures cite the declaration and the inheriting function instead. *)
  fun channel_read (Authored_Channel source) = authored_read source
    | channel_read (Inherited_Channel {label, source, use_pos}) =
        {source = Input.reset_pos source, cited = [Input.pos_of source, use_pos],
         label = SOME label}

  fun labelled NONE message = message
    | labelled (SOME label) message = label ^ ": " ^ message

  (* assemble receives the resolved leading HOL sources and the resolved Rust types, and returns
     the types to finish. *)
  (* The callable branch belongs to the same signature/target inference owner. *)
  fun resolve_binding_operations kind original_ctxt channel_sources lifetimes rust_types assemble =
    let
      val active = Unsynchronized.ref true
      fun run () =
      let
      val frame = serial ()
      val metadata = Unsynchronized.ref true
      val origins = Unsynchronized.ref
        ([]: (serial * bool * generic_binding * bool * Position.T * bool) list)
      val original_bindings = installed_bindings original_ctxt
      fun collect emit_reference binding witness pos =
        if not (!active) then () else
        if not (exists (fn installed => same_generic_parameter
            (binding_parameter binding, binding_parameter installed) andalso
            binding_identity binding = binding_identity installed) original_bindings)
        then raise Fail "uRust signature origin: foreign declaration/callback"
        else
          let val key = (!metadata, binding_identity binding, witness,
                Position.properties_of pos, emit_reference)
              fun same (owner, purpose, previous, demand, position, emit) =
                owner = frame andalso
                (purpose, binding_identity previous, demand, Position.properties_of position, emit) = key
          in if exists same (!origins) then () else
            origins := (frame, !metadata, binding, witness, pos, emit_reference) :: !origins end
      fun collect_self meaning witness pos =
        let
          fun visit demand (Meaning_Scoped_Parameter (declaration, kind)) =
                (case find_first (fn binding => binding_identity binding = declaration)
                    original_bindings of
                   SOME binding =>
                     if #kind (binding_parameter binding) = kind
                     then collect false binding demand pos
                     else raise Fail "uRust Self signature origin: changed declaration kind"
                 | NONE => raise Fail "uRust Self signature origin: foreign declaration")
            | visit demand (Meaning_Mapped (_, _, _, erased, _, arguments)) =
                List.app (fn (index, argument) =>
                  visit (demand andalso not (member (op =) erased index)) argument)
                  (map_index I arguments)
            | visit _ (Meaning_Opaque rows) = List.app (visit false) (maps snd rows)
            | visit demand (Meaning_Tuple types) = List.app (visit demand) types
            | visit demand (Meaning_Slice element) = visit demand element
            | visit demand (Meaning_Array (element, length)) =
                (visit demand element; visit demand length)
            | visit demand (Meaning_Pointer (_, typ)) = visit demand typ
            | visit demand (Meaning_Reference (_, typ)) = visit demand typ
            | visit _ _ = ()
        in if !active then visit witness meaning else () end
      val ctxt = original_ctxt |> Generic_Uses.put NONE
        |> Signature_Origins.put (SOME (collect true))
        |> Signature_Self_Origins.put (SOME collect_self)
      val _ = check_lifetimes lifetimes rust_types
      val recipe_types = maps (fn binding => maps (fn {inputs, output, ...}: callable_recipe =>
        inputs @ the_list output) (#callables (binding_spec binding))) original_bindings
      val leading = map channel_read (map_filter I channel_sources)
      val reads = leading @ map authored_read (maps hol_sources (recipe_types @ rust_types))
      fun parse read_ctxt ({source, cited, label}: signature_read) =
        positioned_result kind cited (fn () => Syntax.parse_typ read_ctxt (Syntax.implode_input source)
          handle ERROR message => error (labelled label message))
      val raw = URust_Report_Transaction.native ctxt (fn read_ctxt => map (parse read_ctxt) reads)
      (* Inspect authored variable identities before native synonym expansion can erase an
         abbreviation operand. Raw sorts still contain syntax markers and default-sort
         placeholders; native certification below checks their actual constraints. *)
      val _ = List.app (fn (read: signature_read, typ) =>
        ignore (positioned_result kind (#cited read) (fn () =>
          Proof_Context.standard_typ_check ctxt
            (map (fn (name, _) => TVar (name, []))
              (Term.add_tvarsT typ [])))))
        (reads ~~ raw)
      val _ = List.app (observe_binding_syntax_types ctxt o single)
        (take (length (maps hol_sources recipe_types)) (drop (length leading) raw))
      val ordinary = filter (fn binding => null (#callables (binding_spec binding))) original_bindings
      (* Preserve raw syntax for positioned origins, but expand native synonyms before any
         channel, recipe or outer escape reaches inference or a callable argument sort check. *)
      val prepared = URust_Report_Transaction.native ctxt (fn read_ctxt =>
        positioned_result kind (maps #cited reads) (fn () => Syntax.check_typs read_ctxt
          (map (TFree o #hol o binding_parameter) ordinary @ raw)))
      val (seeds, parsed) = chop (length ordinary) prepared
      (* Check the authored schematic-variable policy before internal sort inference
         can replace a source variable. Use the native context policy on variable
         leaves; ordinary source holes and callable aliases still follow their
         established preparation phases. *)
      val _ = List.app (fn (read: signature_read, typ) =>
        ignore (positioned_result kind (#cited read) (fn () =>
          Proof_Context.standard_typ_check ctxt (map TVar (Term.add_tvarsT typ [])))))
        (reads ~~ parsed)
       (* Expand native HOL type abbreviations before callable sort constraints and
          the signature codec inspect their structure. Keep the authored-variable
          gate above: an abbreviation may erase an explicitly schematic operand. *)
       val parsed = map (fn (read: signature_read, typ) =>
         positioned_result kind (#cited read) (fn () =>
           the_single (Proof_Context.standard_typ_check ctxt [typ]))) (reads ~~ parsed)
      val {fresh, normalize, check_sort, backend, backend_slots, unify, native, accept_native,
        parameterize} =
         inference_state kind ctxt (seeds @ parsed)
      val named = Unsynchronized.ref (Symtab.make (map2 (fn binding => fn typ =>
        (binding_name binding,
          if Models.ambient_name ctxt (binding_name binding) then typ
          else fresh (Type.sort_of_atyp typ))) ordinary seeds))
      val templates = Unsynchronized.ref ([]: (serial * (typ * callable_relation)) list)
      val visiting = Unsynchronized.ref ([]: serial list)
      val channel_types = Unsynchronized.ref (NONE: computation_channels option)
      fun source_key source = (Input.string_of source, Position.properties_of (Input.pos_of source))
      val source_types = maps (fn (read, typ) => [(source_key (#source read), typ)]) (reads ~~ parsed)
      fun lookup_source source = case AList.lookup (op =) source_types (source_key source) of
          SOME typ => typ | NONE => raise Fail "uRust callable frame: missing parsed HOL source"
      fun local_binding name = find_first (fn binding => #rust (binding_parameter binding) = name)
        original_bindings
      fun terminal ({state, abort, input, output}: computation_channels) result =
        Type (\<^type_name>\<open>function_body\<close>, [state, result, abort, input, output])
      fun actual relation = map #1 (#inputs (relation: callable_relation)) --->
        terminal (#channels relation) (#1 (#result relation))
      fun channels () = case !channel_types of SOME tuple => tuple
        | NONE => error "urust: recursive callable/channel alias dependency"
      fun existing_type typ = typ |> Term.map_atyps
        (fn TFree (name, sort) => (case Symtab.lookup (!named) name of
            SOME slot => (check_sort name slot sort Position.none; slot)
          | NONE => TFree (name, sort)) | other => other) |> normalize
      fun import_type (typ as Type (name, operands)) =
            if typ = dummyT then fresh [] else Type (name, map import_type operands)
        | import_type (TFree ("'_dummy_", sort)) = fresh sort
        | import_type (typ as TFree (name, sort)) =
            (case find_first (fn binding => binding_name binding = name andalso
                not (null (#callables (binding_spec binding)))) original_bindings of
               SOME binding => let val (typ, _) = callable binding
                 val _ = check_sort (#rust (binding_parameter binding)) typ sort
                   (#pos (binding_parameter binding)) in typ end
             | NONE => (case Symtab.lookup (!named) name of
                 SOME slot => (check_sort name slot sort Position.none; slot)
               | NONE => if is_some (Variable.def_sort ctxt (name, ~1)) then typ
                 else let val slot = fresh sort
                   val _ = named := Symtab.update (name, slot) (!named) in slot end))
        | import_type typ = typ
      and callable binding =
        let val declaration = binding_identity binding
        in case AList.lookup (op =) (!templates) declaration of SOME resolved => resolved
         | NONE =>
          let
            val parameter = binding_parameter binding
            val _ = if member (op =) (!visiting) declaration then error
              ("urust: recursive callable dependency involving " ^ #rust parameter ^
                Position.here (#pos parameter)) else ()
            val _ = visiting := declaration :: !visiting
            val prior_metadata = !metadata
            val _ = metadata := true
            fun parameter_hook name arities pos = Option.map (fn dependency =>
              let val _ = if arities = [0] then () else mapping_error "generic parameters take no arguments" pos
                  val (typ, _) = callable dependency
                  val _ = collect true dependency true pos
              in {typ = typ, meaning = Meaning_Scoped_Parameter
                (binding_identity dependency, #kind (binding_parameter dependency))} end) (local_binding name)
            fun read_escape source = import_type (lookup_source source)
            val operations = resolve_value_operations kind ctxt read_escape check_sort existing_type
              backend parameter_hook no_dependency
            fun recipe ({origin, inputs, output}: callable_recipe) =
              let val output = the_default (Primitive_Type (DPT_Unit, #bound_pos origin)) output
                  val resolved = #types operations (inputs @ [output])
                  val (inputs, result) = split_last resolved
              in {inputs = map (fn {typ, meaning} => (typ, meaning)) inputs,
                result = (#typ result, #meaning result), channels = channels ()}: callable_relation end
            fun inherited_relation ({inputs, result, channels = previous}: callable_relation) =
              let fun leaf (typ, source) = (existing_type typ, finish_meaning (map existing_type) source)
                  val current = channels ()
                  val _ = unify (map2 (fn T => fn U => (existing_type T, U))
                    [#state previous, #abort previous, #input previous, #output previous]
                    [#state current, #abort current, #input current, #output current])
              in {inputs = map leaf inputs, result = leaf result, channels = current}: callable_relation end
            val inherited = Option.map inherited_relation (binding_callable_relation binding)
            val pending_recipes = drop (binding_checked_recipes binding) (#callables (binding_spec binding))
            val relations = the_list inherited @ map recipe pending_recipes
            val relation = case relations of first :: _ => first
              | [] => raise Fail "uRust callable frame: ordinary dependency entered callable builder"
            fun compare other =
              let
                val left = Meaning_Tuple (map #2 (#inputs relation) @ [#2 (#result relation)])
                val right = Meaning_Tuple (map #2 (#inputs other) @ [#2 (#result other)])
                val rigid = map (fn binding =>
                  let val slot = the (Symtab.lookup (!named) (binding_name binding))
                  in (normalize slot, TFree (#hol (binding_parameter binding))) end) ordinary
                fun freeze typ = Term.typ_subst_atomic rigid (normalize typ)
                val left = finish_meaning (map freeze) left
                val right = finish_meaning (map freeze) right
                val compared = Micro_Rust_Names.unify_source_trees
                  (Sign.typ_unify (Proof_Context.theory_of ctxt)) [] (K (K NONE))
                  (source_tree_of_meaning ctxt [] left) (source_tree_of_meaning ctxt [] right) (native ())
                  handle Micro_Rust_Names.SOURCE_MATCH => error
                    ("urust: incompatible callable bounds with distinct declared types" ^
                     Position.here_list (map (#bound_pos o #origin) (#callables (binding_spec binding))))
                    | Type.TUNIFY => error
                        ("urust: incompatible callable bounds with different checked native types" ^
                         Position.here_list (map (#bound_pos o #origin) (#callables (binding_spec binding))))
                (* Rigid declaration variables were only a comparison view. Retain permitted native
                   hole/channel constraints, restoring the actual frame slots before committing. *)
                val {types = compared_types, maxidx = compared_max, ...} = compared
                val unfreeze = Term.typ_subst_atomic (map swap rigid)
                val compared_types = Vartab.map (K (apsnd unfreeze)) compared_types
                val _ = accept_native (compared_types, compared_max)
                val _ = unify [(actual relation, actual other)]
                  handle Type.TUNIFY => error
                    ("urust: incompatible callable bounds with different checked native types" ^
                     Position.here_list (map (#bound_pos o #origin) (#callables (binding_spec binding))))
              in () end
            val _ = List.app compare (tl relations)
            val _ = check_sort (#rust parameter) (actual relation) (snd (#hol parameter)) (#pos parameter)
            val _ = Option.app (fn inherited =>
              let val previous = #channels (inherited: callable_relation)
                  val current = channels ()
              in unify (map2 (fn T => fn U => (existing_type T, U))
                [#state previous, #abort previous, #input previous, #output previous]
                [#state current, #abort current, #input current, #output current]) end)
              (binding_callable_relation binding)
            val resolved = (actual relation, relation)
            val _ = templates := (declaration, resolved) :: !templates
            val _ = visiting := tl (!visiting)
            val _ = metadata := prior_metadata
          in resolved end
        end
      val (supplied, _) = chop (length leading) parsed
      fun channel NONE pending = (fresh [], pending)
        | channel (SOME _) (typ :: pending) = (import_type typ, pending)
        | channel _ [] = raise Fail "uRust callable frame: missing channel"
      val (tuple, _) = fold_map channel channel_sources supplied
      val [state, abort, input, output] = tuple
      val _ = channel_types := SOME {state = state, abort = abort, input = input, output = output}
      val _ = List.app (fn binding => if null (#callables (binding_spec binding)) then ()
        else ignore (callable binding)) original_bindings
      fun checked_binding binding =
        let val template = if null (#callables (binding_spec binding)) then
                existing_type (the (binding_template binding)) else #1 (callable binding)
            val relation = if null (#callables (binding_spec binding)) then NONE
              else SOME (#2 (callable binding))
        in Binding {spec = binding_spec binding, template = SOME template, relation = relation,
          checked_recipes = length (#callables (binding_spec binding))} end
      val intermediate = {bindings = map checked_binding original_bindings, signature_events = NONE}: binding_scope
      val checking = ctxt |> with_binding_scope intermediate |> with_binding_type_aliases
      val _ = metadata := false
      val leading_raw_count = length leading
      val raw_sources = drop leading_raw_count raw
      (* Only actual outer escapes supply authored HOL origins; recipe reads remain metadata. *)
      val outer_hol = maps hol_sources rust_types
      val _ = List.app (fn source => observe_binding_syntax_types checking
        [the (AList.lookup (op =) (map2 (fn read => fn typ => (source_key (#source read), typ)) reads raw)
          (source_key source))]) outer_hol
      val _ = List.app (fn (source, raw) => case source of
          Authored_Channel _ => observe_binding_syntax_types checking [raw] | _ => ())
        (map_filter I channel_sources ~~ take leading_raw_count raw)
      val imported = map import_type parsed
      val complete = map normalize
        (map_filter binding_template (scope_bindings intermediate) @ imported)
      (* This complete native frame already contains generated inference TVars; authored
         syntax was checked above in the original strict context. *)
      val checked = Syntax.check_typs
        (Proof_Context.set_mode Proof_Context.mode_schematic checking) complete
      val _ = unify (complete ~~ checked)
      fun read_escape source = import_type (lookup_source source)
      val operations = resolve_value_operations kind checking read_escape check_sort existing_type
        backend no_parameter no_dependency
      val resolved = #types operations rust_types
      val outer = assemble (channels ()) resolved
      fun restore types =
        let
          fun named_slot (name, slot) = case normalize slot of TVar (variable, sort) =>
                SOME ((variable, sort), TFree (name, sort)) | _ => NONE
          val names = TVars.make (map_filter named_slot (Symtab.dest (!named)))
          val types = map (normalize #> Term_Subst.instantiateT names) types
          val types = if kind = Impl_Target then
            let
              val generated = map_filter (fn (index, typ) => case normalize typ of TVar (_, sort) =>
                    SOME (normalize typ, TFree (nth (Name.variants (Variable.names_of ctxt)
                      ["'urust_state", "'urust_abort", "'urust_input", "'urust_output"]) index, sort))
                | _ => NONE) (map_index I tuple)
            in map (Term.typ_subst_atomic generated) types end else types
        in if kind = Impl_Target then
          let val named_context = fold (fn (name, slot) => Variable.declare_typ
                (TFree (name, Type.sort_of_atyp slot))) (Symtab.dest (!named)) ctxt
          in finish_impl_backend named_context normalize (backend_slots ()) types end
          else
          map (Term.map_atyps parameterize #> Proof_Context.cert_typ ctxt) types end
      fun finish_relation ({inputs, result, channels}: callable_relation) =
        let fun leaf (typ, source) = (the_single (restore [typ]), finish_meaning restore source)
            val [state, abort, input, output] = restore
              [#state channels, #abort channels, #input channels, #output channels]
        in {inputs = map leaf inputs, result = leaf result,
          channels = {state = state, abort = abort, input = input, output = output}}: callable_relation end
      fun finish_binding binding =
        let val spec = binding_spec binding
            val parameter = #parameter spec
            val template = the_single (restore [the (binding_template binding)])
            val hol = case template of TFree pair => pair | _ => #hol parameter
            val parameter = {rust = #rust parameter, pos = #pos parameter, kind = #kind parameter,
              hol = hol, bounds = #bounds parameter, report_reference = #report_reference parameter}
        in Binding {spec = {parameter = parameter, declaration = #declaration spec,
          callables = #callables spec}, template = SOME template,
          relation = Option.map finish_relation (binding_callable_relation binding),
          checked_recipes = length (#callables spec)} end
      val final_bindings = map finish_binding (scope_bindings intermediate)
      val final_scope = {bindings = final_bindings, signature_events = NONE}: binding_scope
      val final_ctxt = original_ctxt |> with_binding_scope final_scope
        |> Signature_Origins.put NONE |> Signature_Self_Origins.put NONE
      val finished = restore outer
      fun final_origin (owner, _, previous, witness, pos, emit_reference) =
        let val _ = if owner = frame then () else raise Fail "uRust signature origin: foreign frame"
            val binding = the (find_first (fn binding => binding_identity binding = binding_identity previous)
              final_bindings)
            val original = the (find_first (fn binding => binding_identity binding = binding_identity previous)
              original_bindings)
            val _ = if same_generic_parameter (binding_parameter previous, binding_parameter original)
                andalso pointer_eq (#report_reference (binding_parameter previous),
                  #report_reference (binding_parameter binding)) then ()
              else raise Fail "uRust signature origin: changed source/callback provenance"
        in (binding, witness, pos, emit_reference) end
      val metadata_origins = map final_origin (rev (filter #2 (!origins)))
      val actual_origins = map final_origin (rev (filter_out #2 (!origins)))
      val _ = List.app (fn (binding, witness, pos, emit_reference) =>
        if emit_reference then
          (generic_reference_callback witness (binding_parameter binding) pos;
           if witness then Navigation.defer_report_text final_ctxt pos Markup.typing
             (#rust (binding_parameter binding) ^ " = " ^
              Syntax.string_of_typ (Config.put show_sorts true final_ctxt) (the (binding_template binding)))
           else ()) else ()) metadata_origins
      val (_, events) = capture_binding_events final_ctxt (fn observed => List.app
        (fn (binding, witness, pos, emit_reference) =>
          if emit_reference then report_binding_reference observed binding
            {witness = witness, pos = pos}
          else if exists (fn installed => same_binding (binding, installed))
              (installed_bindings observed) then
            Option.app (fn observe => observe [binding] [] witness) (generic_use_observer observed)
          else raise Fail "uRust Self signature origin: stale finalized binding") actual_origins)
      val scope = {bindings = final_bindings, signature_events = SOME events}: binding_scope
      val resolved = map (fn {typ, meaning} => {typ = the_single (restore [typ]),
        meaning = finish_meaning restore meaning}: resolved) resolved
      val _ = Option.app (fn trace => trace := map (fn (source, evidence, argument) =>
        (finish_meaning restore source, Option.map (the_single o restore o single) evidence, argument))
        (!trace)) (Source_Resolution_Trace.get ctxt)
      val _ = record_impl_model_parameters kind ctxt restore (backend_slots ())
    in {types = finished, scope = scope, resolved = resolved, channels = #channels
      (finish_relation {inputs = [], result = (HOLogic.unitT, Meaning_Primitive DPT_Unit),
        channels = channels ()})} end
      val outcome = Exn.capture0 run ()
      val _ = active := false
    in Exn.release outcome end

  fun resolve_signature_operations kind original_ctxt leading lifetimes rust_types
      specifications arguments assemble =
    let
      val source_positions = Unsynchronized.ref ([]: Position.T list)
      val ctxt = Source_Only_Positions.put (SOME source_positions) original_ctxt
      val _ = check_lifetimes lifetimes rust_types
      val parameters = filter (fn parameter => case current_binding ctxt parameter of
        SOME binding => null (#callables (binding_spec binding)) | NONE => true) (scope_parameters ctxt)
      val witnessed_types = map_filter (fn ({hol, ...}: generic_source_parameter, argument) =>
        if is_some hol then (case argument of Rust_Type_Argument typ => SOME typ | _ => NONE)
        else NONE) (specifications ~~ arguments)
      val reads = leading @ map authored_read (maps hol_sources (rust_types @ witnessed_types))
      fun parse read_ctxt ({source, cited, label}: signature_read) =
        positioned_result kind cited
          (fn () =>
            Syntax.parse_typ read_ctxt (Syntax.implode_input source)
              handle ERROR message => error (labelled label message))
      (* One deterministic parse-and-check of every channel and signature escape keeps sort
         inference shared and lets the report transaction repeat the read for its markup. *)
      val checked_all =
        URust_Report_Transaction.native ctxt (fn read_ctxt =>
          let val read_ctxt = with_binding_type_aliases read_ctxt
              val parsed = map (parse read_ctxt) reads
              val _ = List.app (fn raw => observe_binding_syntax_types read_ctxt [raw]) parsed
            in positioned_result kind (maps #cited reads)
              (fn () => Syntax.check_typs read_ctxt
                (map (TFree o #hol) parameters @ parsed))
          end)
      val (parameter_types, checked) = chop (length parameters) checked_all
       val _ = note_generic_types ctxt checked

      (* Keep sort inference shared across the whole signature. Only fresh
         signature variables are flexible; ambient variables remain rigid. *)
      val {fresh, normalize, check_sort, backend, backend_slots, parameterize, ...} =
        inference_state kind ctxt checked_all
      val named_parameters: typ Symtab.table Unsynchronized.ref =
        Unsynchronized.ref (Symtab.make (map2
          (fn {hol = (name, _), ...}: generic_parameter => fn typ =>
            (name, if Models.ambient_name ctxt name then typ
              else fresh (Type.sort_of_atyp typ))) parameters parameter_types))

      fun import_typ (typ as Type (name, types)) =
            if typ = dummyT then fresh []
            else Type (name, map import_typ types)
        | import_typ (TFree ("'_dummy_", sort)) = fresh sort
        | import_typ (typ as TFree (name, sort)) =
              (case Symtab.lookup (!named_parameters) name of
                 SOME parameter =>
                   (check_sort name parameter sort Position.none; parameter)
               | NONE =>
                   if is_some (Variable.def_sort ctxt (name, ~1)) then typ
                   else
                     let
                       val parameter = fresh sort
                       val _ =
                         named_parameters :=
                           Symtab.update (name, parameter) (!named_parameters)
                     in parameter end)
        | import_typ (typ as TVar _) = typ

      val (leading_types, escapes) = chop (length leading) (map import_typ checked)
      val pending = Unsynchronized.ref escapes

      fun read_escape _ =
        (case !pending of
           typ :: rest => (pending := rest; typ)
         | [] =>
             raise Fail
               "uRust type registry: signature HOL escape is absent")

      fun finish_authored types =
        let
          fun named (name, parameter) =
            (case normalize parameter of
               TVar (variable, sort) =>
                 SOME ((variable, sort), TFree (name, sort))
             | _ => NONE)
          (* Several authored names may unify; restore one name per resulting variable.
             A name specialized to a concrete type needs no restoration. *)
          val names =
            TVars.make (map_filter named (Symtab.dest (!named_parameters)))
        in
          map
            (normalize #>
              Term_Subst.instantiateT names #>
              Term.map_atyps parameterize #>
              Proof_Context.cert_typ ctxt)
            types
        end

      (* Only an impl target fixes its explicitly allocated semantic roles. Its ordinary
         source/escape holes remain schematic and are rejected by the target's existing guard.
         One naming context serves both the Self type and every actual meaning leaf. *)
      fun finish types =
        let val finished = finish_authored types in
          if kind = Impl_Target then
            let
              val named_context = fold (fn (name, slot) =>
                Variable.declare_typ (TFree (name, Type.sort_of_atyp slot)))
                (Symtab.dest (!named_parameters)) ctxt
              (* Authored restoration also turns native unification variables into inference
                 parameters. Apply that same codec to role slots before matching their holes. *)
              val finished_slots = map
                (apsnd (the_single o finish_authored o single)) (backend_slots ())
            in finish_impl_backend named_context normalize finished_slots finished end
          else finished
        end

      fun scoped_normalize typ =
        typ |> Term.map_atyps
          (fn typ as TFree (name, _) =>
                (case Symtab.lookup (!named_parameters) name of
                   SOME parameter => parameter
                 | NONE => typ)
            | typ => typ) |> normalize
      val operations = resolve_value_operations kind ctxt read_escape check_sort scoped_normalize
        backend no_parameter no_dependency
      val resolved = #types operations rust_types
      val resolved_arguments = #arguments operations (map argument_specification specifications) arguments
      val _ =
        if null (!pending) then ()
        else
          raise Fail
            "uRust type registry: unconsumed signature HOL escape"
      fun report_generic name pos =
        if exists (fn source_pos => Position.properties_of source_pos = Position.properties_of pos)
          (!source_positions) then () else
        (case find_first (fn ({rust, ...}: generic_parameter) => rust = name) parameters of
           NONE => ()
         | SOME {hol = (hol_name, sort), ...} =>
             let
               val final_sort =
                 (case Option.map normalize (Symtab.lookup (!named_parameters) hol_name) of
                    SOME (TVar (_, inferred)) => inferred
                  | SOME (TFree (_, inferred)) => inferred
                  | _ => sort)
             in Navigation.defer_report_text ctxt pos Markup.typing
               (name ^ " = " ^ Syntax.string_of_typ (Config.put show_sorts true ctxt)
                 (TFree (hol_name, final_sort))) end)
      fun report_type (Primitive_Type (primitive, pos)) =
            report_generic (rust_primitive_name primitive) pos
        | report_type (typ as Path_Type ([Rust_Type_Path_Segment (name, pos, _, _)], _)) =
            (report_generic name pos; List.app report_type (rust_type_operands typ))
        | report_type typ = List.app report_type (rust_type_operands typ)
      val _ = List.app report_type rust_types
      val supplied_types = map_filter #typ resolved_arguments
      val finished_types = finish supplied_types
      fun finish_argument {typ = NONE, evidence, meaning, pos} pending =
            ((NONE, pos), pending)
        | finish_argument {typ = SOME _, evidence, meaning, pos} (typ :: pending) =
            ((SOME typ, pos), pending)
        | finish_argument _ [] = raise Fail "missing finished function argument"
      val (actual_arguments, unused) = fold_map finish_argument resolved_arguments finished_types
      val _ = if null unused then () else raise Fail "extra finished function arguments"
      val _ = Option.app (fn trace => trace := map (fn (meaning, evidence, argument) =>
        (finish_meaning finish meaning, Option.map (the_single o finish o single) evidence, argument))
        (!trace)) (Source_Resolution_Trace.get ctxt)
      val finished_resolved = map (fn {typ, meaning} =>
        {typ = typ, meaning = finish_meaning finish meaning}) resolved
      val _ = record_impl_model_parameters kind ctxt finish (backend_slots ())
    in (finish (assemble leading_types finished_resolved),
      {arguments = actual_arguments, identities =
        map (source_identity_name o finish_meaning finish o #meaning) resolved_arguments,
       meanings = map (finish_meaning finish o #meaning) resolved_arguments,
       evidence = map (fn {evidence, pos, ...} =>
         (Option.map (the_single o finish o single) evidence, pos)) resolved_arguments}) end

  fun resolve_signature_with kind ctxt leading lifetimes rust_types assemble =
    #1 (resolve_signature_operations kind ctxt leading lifetimes rust_types [] [] assemble)

  fun resolve_source_arguments_complete ctxt specifications arguments =
    let
      val result = #2 (resolve_signature_operations Function_Signature ctxt [] [] []
        specifications arguments (K (K [])))
      fun validate ((SOME argument, pos), {sort, ...}: generic_source_parameter) =
            if Sign.of_sort (Proof_Context.theory_of ctxt) (argument, sort) then ()
            else sort_error Function_Signature ctxt "function argument" argument sort pos
        | validate ((NONE, _), _) = ()
      val _ = List.app validate (#arguments result ~~ specifications)
    in result end
  type complete_source_arguments =
    {arguments: (typ option * Position.T) list, identities: string list,
     meanings: source_identity list, evidence: (typ option * Position.T) list}
  fun source_argument_view ({arguments, identities, ...}: complete_source_arguments) =
    {arguments = arguments, identities = identities}
  fun resolve_source_arguments ctxt specifications arguments =
    source_argument_view (resolve_source_arguments_complete ctxt specifications arguments)

  fun resolve_binding_source_arguments ctxt specifications arguments =
    if forall (null o #callable_origins) (specifications: binding_scheme_parameter list) then
      resolve_source_arguments ctxt (map legacy_binding_slot specifications) arguments
    else
      let
        val _ = if length specifications = length arguments then () else
          error "urust: wrong number of complete generic source arguments"
        val result = resolve_source_arguments_complete ctxt (map legacy_binding_slot specifications) arguments
        val evidence = #evidence result
        val _ = if length evidence = length specifications then () else
          raise Fail "uRust callable source argument evidence: wrong slot count"
        fun actual_template slot = case #witness slot of SOME typ => SOME typ
          | NONE => Option.map (fn ({inputs, result, channels}: callable_relation) =>
              map #1 inputs ---> Type (\<^type_name>\<open>function_body\<close>,
                [#state channels, #1 result, #abort channels, #input channels, #output channels]))
              (#callable_relation slot)
        val expected = map actual_template specifications
        val expected_terms = Variable.polymorphic ctxt (map Logic.mk_type (map_filter I expected))
        val caller_max = fold Term.maxidx_typ (map_filter fst evidence) (Variable.maxidx_of ctxt)
        val expected_max = fold Term.maxidx_term expected_terms ~1
        val shift = Int.max (caller_max, expected_max) + 1
        val pending = Unsynchronized.ref (map (Logic.dest_type o Term.map_types (Logic.incr_tvar shift)) expected_terms)
        fun slot NONE = NONE | slot (SOME _) = case !pending of typ :: rest =>
            (pending := rest; SOME typ) | [] => raise Fail "missing expected callable template"
        val templates = map slot expected
        (* An erased actual witness is evidence of its existing checked denotation. Freeze
           its schematic leaves in this private comparison so a bound cannot strengthen it. *)
        fun rigid typ = Term.map_atyps (fn TVar ((name, index), sort) =>
            TFree (Name.internal ("urust_source_evidence_" ^ name ^ string_of_int index), sort)
          | leaf => leaf) typ
        fun constrain ((parameter: binding_scheme_parameter, expected), (actual, pos)) environment =
          case (expected, actual) of
            (SOME template, SOME typ) => Sign.typ_unify (Proof_Context.theory_of ctxt)
              (template, if is_none (#witness parameter) then rigid typ else typ) environment
          | (_, NONE) => if null (#callable_origins parameter) then environment else error
              ("urust: erased callable argument has no checked denotation" ^ Position.here pos)
          | _ => environment
        val _ = fold constrain ((specifications ~~ templates) ~~ evidence)
          (Vartab.empty, Int.max (caller_max, expected_max + shift) + 1)
          handle Type.TUNIFY => error "urust: generic argument does not satisfy the complete callable template"
      in source_argument_view result end

  fun resolve_signature ctxt rust_types =
    resolve_signature_with Function_Signature ctxt [] [] rust_types (K (map #typ))

  (* Supplied channels, authored or inherited from a scoped default, and Rust escapes share native
     type/sort checking and import. Rust alone supplies parameter/result types, including the
     default unit result. *)
  fun resolve_function_signature ctxt
      ({state, abort, input, output}: function_channels) lifetimes parameters result =
    let
      val channels = [state, abort, input, output]
      val leading = map channel_read (map_filter I channels)
      fun assemble supplied resolved =
        let
          val (parameter_types, result_types) =
            chop (length parameters) (map #typ resolved)
          fun channel NONE types = (dummyT, types)
            | channel (SOME _) (typ :: types) = (typ, types)
            | channel (SOME _) [] =
                raise Fail "uRust type registry: missing function channel"
          val (channel_types, unused) = fold_map channel channels supplied
          val _ =
            if null unused then ()
            else raise Fail "uRust type registry: unconsumed function channel"
          val [state_type, abort_type, input_type, output_type] = channel_types
        in
          [parameter_types --->
            Type (\<^type_name>\<open>function_body\<close>,
              [state_type, the_single result_types, abort_type, input_type, output_type])]
        end
    in
      the_single
        (resolve_signature_with Function_Signature ctxt leading lifetimes (parameters @ [result])
          assemble)
    end

  fun resolve_function_signature_with_bindings ctxt
      (channels as {state, abort, input, output}: function_channels) lifetimes parameters result =
    if forall (fn binding => null (#callables (binding_spec binding))) (installed_bindings ctxt) then
      let val (typ, events) = capture_binding_events ctxt (fn observed =>
            resolve_function_signature observed channels lifetimes parameters result)
          val bindings = installed_bindings ctxt
      in {typ = typ, scope = {bindings = bindings, signature_events = SOME events}: binding_scope} end
    else
      let
        fun assemble (tuple: computation_channels) (resolved: resolved list) =
          let val (parameters, result) = split_last (map #typ resolved)
          in [parameters ---> Type (\<^type_name>\<open>function_body\<close>,
            [#state tuple, result, #abort tuple, #input tuple, #output tuple])] end
        val resolved = resolve_binding_operations Function_Signature ctxt [state, abort, input, output]
          lifetimes (parameters @ [result]) assemble
      in {typ = the_single (#types resolved), scope = #scope resolved} end

  (* Impl targets. The written head may name a type through a chunk import or a type alias; the
     alias expansion decides the canonical path and the Self type, and every rejection applies to
     the expansion. *)
  fun non_path_description (Tuple_Type _) = "a tuple type"
    | non_path_description (Group_Type _) = "a parenthesized type"
    | non_path_description (Reference_Type (BM_Imm, _, _, _)) = "a shared reference type"
    | non_path_description (Reference_Type (BM_Mut, _, _, _)) = "a mutable reference type"
    | non_path_description (Raw_Pointer_Type _) = "a raw pointer type"
    | non_path_description (Slice_Type _) = "a slice type"
    | non_path_description (Array_Type _) = "an array type"
    | non_path_description (Const_Array_Type _) = "an array type"
    | non_path_description _ = "a type without a Rust path"

  fun meaning_description _ _ (Meaning_Tuple _) = "a tuple type"
    | meaning_description _ _ (Meaning_Slice _) = "a slice type"
    | meaning_description _ _ (Meaning_Pointer _) = "a raw pointer type"
    | meaning_description _ _ (Meaning_Reference _) = "a reference type"
    | meaning_description ctxt typ (Meaning_Array _) =
        "the HOL type " ^ quote (Syntax.string_of_typ ctxt typ)
    | meaning_description ctxt _ (Meaning_HOL typ) =
        "the HOL type " ^ quote (Syntax.string_of_typ ctxt typ)
    | meaning_description _ _ _ = "a type without a Rust path"

  fun primitive_target_error name via pos =
    error
      ("urust: cannot define an inherent impl for the primitive type " ^ quote name ^ via ^
        Position.here pos)

  (* The exact registry key that a written target head denotes, without reports: a type import
     on the only segment denotes its target key, as in type resolution. *)
  fun written_target_key ctxt rows =
    (case rows of
       [(name, _, _)] =>
         (case URust_Import_Scope.lookup ctxt URust_Import_Scope.Type_Namespace name of
            SOME binding => #key binding
          | NONE => name)
     | _ => #base (row_information rows))

  fun target_rows (Path_Type (segments, _)) = SOME (path_rows segments)
    | target_rows _ = NONE

  fun resolve_impl_target_meaning_with resolver ctxt target =
    let
      val pos = rust_type_position target
      val rows =
        (case (target_rows target, target) of
           (SOME rows, _) => rows
         | (NONE, Primitive_Type (primitive, primitive_pos)) =>
             primitive_target_error (rust_primitive_name primitive) "" primitive_pos
         | (NONE, HOL_Type_Source source) =>
             error
               ("urust: a \<tau>\<open>...\<close> HOL type cannot be an impl target; " ^
                 "impl targets must be Rust type paths" ^ Position.here (Input.pos_of source))
         | (NONE, _) =>
             error
               ("urust: impl targets must be Rust type paths, not " ^
                 non_path_description target ^ Position.here pos))
      val written_key = written_target_key ctxt rows
      val written_entry = lookup ctxt written_key
      val via =
        (case written_entry of
           SOME entry =>
             if alias_origin (#origin entry)
             then " (through the type alias " ^ quote written_key ^ ")"
             else ""
         | NONE => "")
      val meaning = Unsynchronized.ref NONE
      fun assemble _ resolved =
        (case resolved of
           [{typ, meaning = resolved_meaning}] => (meaning := SOME resolved_meaning; [typ])
         | _ => raise Fail "uRust type registry: impl target resolution is not one type")
      val self_type =
        the_single (resolver ctxt
          (map (fn (name, (pos, _)) => Rust_Lifetime (name, pos))
            (Symtab.dest (Header_Lifetimes.get ctxt))) [target] assemble)
      val canonical_path =
        (case the (!meaning) of
           Meaning_Mapped (base, _, _, _, _, _) => base
         | Meaning_Primitive primitive =>
             primitive_target_error (rust_primitive_name primitive) via pos
         | other =>
             error
               ("urust: impl target " ^ quote written_key ^ " is a type alias of " ^
                 meaning_description ctxt self_type other ^ "; impl targets must be Rust type paths" ^
                 Position.here pos))
      val _ =
        if null (Term.add_tvarsT self_type []) then ()
        else
          error
            ("urust: an impl target must not contain inference holes; " ^
              "write every type argument explicitly" ^ Position.here pos)
      fun report_target_reference use_pos =
        Option.app (report_reference ctxt use_pos written_key) written_entry
    in
      ({canonical_path = canonical_path, self_type = self_type, target_pos = pos,
        report_reference = report_target_reference},
       the (!meaning))
    end

  fun resolve_impl_target_meaning ctxt target =
    resolve_impl_target_meaning_with
      (fn ctxt => resolve_signature_with Impl_Target ctxt []) ctxt target

  fun source_target_template ctxt {self_type, source, declarations, witnesses} =
    let
      val parameters = scope_parameters ctxt
      val identities = the_default [] (generic_scope_identities ctxt)
      val _ = if length declarations = length witnesses then () else
        raise Fail "uRust impl source template: inconsistent witnesses"
      fun variable (index, (declaration, witness)) =
        let val position = find_index (fn identity => identity = declaration) identities
          val _ = if position >= 0 then () else raise Fail "foreign impl declaration identity"
        in {name = ("_urust_impl_source", index),
          kind = neutral_source_kind (#kind (nth parameters position)), witness = witness} end
    in {self_type = self_type, source = SOME (source_tree_of_meaning ctxt declarations source),
      variables = map_index variable (declarations ~~ witnesses),
      requires_source_identity = identity_sensitive source}: Micro_Rust_Names.target_template end

  val synthetic_input_prefix = "urust_synthetic_target_input:"

  (* Position accepts only native properties. Carry fallback provenance in its native label,
     retaining the original label for diagnostics; no synthetic read receives authored ranges. *)
  fun synthetic_input_position pos =
    Position.label (synthetic_input_prefix ^ the_default "" (Position.label_of pos)) pos

  fun synthetic_input_origin pos =
    case Position.label_of pos of
      SOME label => if String.isPrefix synthetic_input_prefix label then
        SOME (Position.label (String.extract (label, size synthetic_input_prefix, NONE)) pos)
        else NONE
    | NONE => NONE

  fun authored_argument_input inputs argument =
    let
      val origin = argument_origin argument
      val exact = AList.lookup same_origin inputs origin
      fun nested (_, source) =
        (case (Position.offset_of origin, Position.end_offset_of origin,
            Position.offset_of (Input.pos_of source), Position.end_offset_of (Input.pos_of source)) of
           (SOME start, SOME stop, SOME outer_start, SOME outer_stop) =>
             if start >= outer_start andalso stop <= outer_stop andalso stop > start andalso
                 Position.file_of origin = Position.file_of (Input.pos_of source) andalso
                 Position.id_of origin = Position.id_of (Input.pos_of source) then
               let val symbols = filter (fn (_, pos) => case Position.offset_of pos of
                   SOME offset => start <= offset andalso offset < stop | NONE => false)
                     (Input.source_explode source)
               in case symbols of [] => NONE | (_, pos) :: _ =>
                 SOME (implode (map fst symbols), pos) end
             else NONE
         | _ => NONE)
    in case exact of SOME source => SOME (Input.string_of source, Input.pos_of source)
      | NONE => get_first nested inputs end

  fun source_argument_input inputs argument =
    case authored_argument_input inputs argument of SOME source => source
    | NONE => (case argument of
        Rust_Type_Argument (HOL_Type_Source source) => (Input.string_of source, Input.pos_of source)
      | Rust_Type_Argument typ =>
          (URust_Printer.string_of_rust_type URust_Printer.serialized_options typ,
            synthetic_input_position (rust_type_position typ))
      | Rust_Numeric_Argument integer =>
          (integer_literal_lexeme integer,
            synthetic_input_position (integer_literal_position integer))
      | _ => raise Fail "unsupported target source argument input")

  fun selection_of_meaning ctxt authored typ meaning trace origins pos =
    let
      val associated = the_default [] (AList.lookup same_origin origins pos)
      fun visit path meaning (evidence, inputs) =
        let
          val origin = AList.lookup (op =) associated path
          val records = filter (fn (other, _, argument) => other = meaning andalso
            (case origin of NONE => true | SOME source =>
              same_origin (argument_origin source, argument_origin argument))) trace
          val actual = get_first (fn (_, typ, _) => typ) records
          val actual = case (actual, meaning) of (NONE, Meaning_Scoped_Parameter (identity, _)) =>
              (case find_first (fn binding => binding_identity binding = identity) (installed_bindings ctxt) of
                 SOME binding => if binding_has_witness ctxt binding andalso binding_available ctxt binding
                   then binding_template binding else NONE
               | NONE => NONE)
            | _ => actual
          val source = case origin of SOME argument => SOME argument
            | NONE => Option.map #3 (try hd records)
          val input = Option.map (source_argument_input authored) source
          val evidence = case actual of NONE => evidence | SOME T => (path, T) :: evidence
          val inputs = case input of NONE => inputs | SOME source => (path, source) :: inputs
        in fold_index (fn (index, child) => visit (path @ [index]) child)
          (meaning_children meaning) (evidence, inputs) end
      val (evidence, inputs) = visit [] meaning ([], [])
    in {self_type = typ, source = SOME (source_tree_of_meaning ctxt [] meaning),
      source_identity = if identity_sensitive meaning then SOME (source_identity_name meaning) else NONE,
      evidence = rev evidence, inputs = rev inputs, pos = pos}: Micro_Rust_Names.target_selection end

  fun resolve_impl_target_selection ctxt target =
    let
      val trace = Unsynchronized.ref []
      val origins = Unsynchronized.ref []
      val observed = ctxt |> Source_Resolution_Trace.put (SOME trace)
        |> Source_Resolution_Origins.put (SOME origins)
      val (self, meaning) = resolve_impl_target_meaning observed target
      val selection = selection_of_meaning ctxt [] (#self_type self) meaning (!trace) (!origins) (rust_type_position target)
    in (self, if identity_sensitive meaning then SOME meaning else NONE, selection) end

  fun resolve_impl_target_selection_with_bindings ctxt target =
    if forall (null o #callables o binding_spec) (installed_bindings ctxt) then
      let val ((self, source, selection), events) = capture_binding_events ctxt
            (fn observed => resolve_impl_target_selection observed target)
          val scope = {bindings = installed_bindings ctxt, signature_events = SOME events}: binding_scope
      in {self = self, source = source, selection = selection, scope = scope} end
    else
      let
        val trace = Unsynchronized.ref []
        val origins = Unsynchronized.ref []
        val final_scope = Unsynchronized.ref NONE
        val observed = ctxt |> Source_Resolution_Trace.put (SOME trace)
          |> Source_Resolution_Origins.put (SOME origins)
        fun resolver ctxt lifetimes types assemble =
          let fun assemble_binding (_: computation_channels) resolved = assemble [] resolved
              val resolved = resolve_binding_operations Impl_Target ctxt [NONE, NONE, NONE, NONE]
                lifetimes types assemble_binding
              val _ = assemble [] (#resolved resolved)
              val _ = final_scope := SOME (#scope resolved)
          in #types resolved end
        val (self, meaning) = resolve_impl_target_meaning_with resolver observed target
        val scope = the (!final_scope)
        val selection = selection_of_meaning (with_binding_scope scope ctxt) [] (#self_type self)
          meaning (!trace) (!origins) (rust_type_position target)
      in {self = self, source = if identity_sensitive meaning then SOME meaning else NONE,
        selection = selection, scope = scope} end

  fun resolve_impl_target_identity ctxt target =
    let val (self, identity, _) = resolve_impl_target_selection ctxt target
    in (self, identity) end

  fun resolve_target_selection_with_inputs ctxt inputs target =
    let
      val trace = Unsynchronized.ref []
      val origins = Unsynchronized.ref []
      val observed = ctxt |> Source_Resolution_Trace.put (SOME trace)
        |> Source_Resolution_Origins.put (SOME origins)
      val meaning = Unsynchronized.ref NONE
      fun assemble _ [{typ, meaning = source}] = (meaning := SOME source; [typ])
        | assemble _ _ = raise Fail "target selection expected one type"
      val typ = the_single (resolve_signature_with Function_Signature observed []
        (map (fn (name, (pos, _)) => Rust_Lifetime (name, pos))
          (Symtab.dest (Header_Lifetimes.get ctxt))) [target] assemble)
    in selection_of_meaning ctxt inputs typ (the (!meaning)) (!trace) (!origins) (rust_type_position target) end

  fun resolve_target_selection ctxt target = resolve_target_selection_with_inputs ctxt [] target

  fun prepare_scoped_target_selection ctxt source (selection: Micro_Rust_Names.target_selection) =
    let
      val entries = schemes_for_source ctxt source
      val _ = consistent_scoped_schemes entries
      fun enrich (scheme: function_scheme) (selection: Micro_Rust_Names.target_selection) =
        case scoped_owner scheme of NONE => selection
       | SOME {target, parameters, ...} =>
           let
             val target = Micro_Rust_Names.fresh_target
               (fold Term.maxidx_typ (#self_type selection :: map snd (#evidence selection))
                 (Variable.maxidx_of ctxt) + 1) target
             val matched = Micro_Rust_Names.match_target ctxt target selection
               (Vartab.empty, Variable.maxidx_of ctxt)
             fun demand ({variable, path, evidence, ...}: Micro_Rust_Names.source_binding) acc =
               let val index = find_index (fn ({name, ...}: Micro_Rust_Names.source_variable) =>
                   name = variable) (#variables target)
               in if index < 0 orelse is_none (#hol (nth parameters index)) orelse is_some evidence
                 then acc else
                 (case AList.lookup (op =) (#inputs selection) path of
                    NONE => error ("urust: selected impl argument has no available HOL witness" ^
                      Position.here (#pos selection))
                  | SOME (text, origin) =>
                      let
                        val authored_origin = synthetic_input_origin origin
                        val synthetic = is_some authored_origin
                        val origin = the_default origin authored_origin
                        val pos = if synthetic then Position.none else origin
                        val input = Parser_Lex_Util.positioned_content_source text pos
                        val argument = URust_Parser.parse_generic_argument_source ctxt input
                        val parameter = nth parameters index
                        val resolved = resolve_source_arguments ctxt [parameter] [argument]
                          handle ERROR message => error (message ^
                            (if synthetic then "; source argument" ^ Position.here origin else ""))
                        val typ = case #arguments resolved of [(SOME T, _)] => T
                          | _ => error ("urust: selected impl argument has no available HOL witness" ^
                              Position.here origin)
                      in (path, typ) :: acc end)
               end
             val evidence = case matched of NONE => #evidence selection
               | SOME {bindings, ...} => fold demand bindings (#evidence selection)
           in {self_type = #self_type selection, source = #source selection,
             source_identity = #source_identity selection, inputs = #inputs selection,
             evidence = evidence, pos = #pos selection}: Micro_Rust_Names.target_selection end
    in fold enrich entries selection end

  fun prepare_binding_target_selection ctxt source (selection: Micro_Rust_Names.target_selection) =
    let
      val entries = binding_generic_schemes_for_source ctxt source
      fun enrich (scheme: function_scheme) (selection: Micro_Rust_Names.target_selection) =
        case binding_scoped_owner scheme of NONE => selection
       | SOME {target, parameters, ...} =>
           let
             val target = Micro_Rust_Names.fresh_target
               (fold Term.maxidx_typ (#self_type selection :: map snd (#evidence selection))
                 (Variable.maxidx_of ctxt) + 1) target
             val matched = Micro_Rust_Names.match_target ctxt target selection
               (Vartab.empty, Variable.maxidx_of ctxt)
             fun demand ({variable, path, evidence, ...}: Micro_Rust_Names.source_binding) acc =
               let val index = find_index (fn ({name, ...}: Micro_Rust_Names.source_variable) =>
                   name = variable) (#variables target)
               in if index < 0 orelse is_none (#witness (nth parameters index)) orelse is_some evidence
                 then acc else
                 (case AList.lookup (op =) (#inputs selection) path of
                    NONE => error ("urust: selected impl argument has no available HOL witness" ^
                      Position.here (#pos selection))
                  | SOME (text, origin) =>
                      let
                        val authored_origin = synthetic_input_origin origin
                        val synthetic = is_some authored_origin
                        val origin = the_default origin authored_origin
                        val pos = if synthetic then Position.none else origin
                        val input = Parser_Lex_Util.positioned_content_source text pos
                        val argument = URust_Parser.parse_generic_argument_source ctxt input
                        val parameter = nth parameters index
                        val resolved = resolve_binding_source_arguments ctxt [parameter] [argument]
                          handle ERROR message => error (message ^
                            (if synthetic then "; source argument" ^ Position.here origin else ""))
                        val typ = case #arguments resolved of [(SOME T, _)] => T
                          | _ => error ("urust: selected impl argument has no available HOL witness" ^
                              Position.here origin)
                      in (path, typ) :: acc end)
               end
             val evidence = case matched of NONE => #evidence selection
               | SOME {bindings, ...} => fold demand bindings (#evidence selection)
           in {self_type = #self_type selection, source = #source selection,
             source_identity = #source_identity selection, inputs = #inputs selection,
             evidence = evidence, pos = #pos selection}: Micro_Rust_Names.target_selection end
    in fold enrich entries selection end


  (* Source proof evidence stays on this candidate's stack and in its one native environment.
     It never changes an execution availability mask or adds a lowering argument. *)
  fun instantiate_binding_source_arguments_for_source ctxt source candidate occurrence_type
      {target = selection, arguments} =
    let
      val entries = binding_generic_schemes_for_source ctxt source
      val thy = Proof_Context.theory_of ctxt
      fun instantiate ctxt (entry: function_scheme) =
        let
          val original = binding_metadata entry
          val parameters = #parameters original
          val supplied = Option.map (fn arguments =>
            if length parameters = length arguments then
              resolve_source_arguments_complete ctxt (map legacy_binding_slot parameters) arguments
            else error "urust: wrong number of complete generic source arguments") arguments
          val _ = if is_none arguments andalso exists (is_none o #witness) parameters then
              error "urust: erased generic arguments require explicit source arguments" else ()
          val caller_types = occurrence_type ::
            maps (fn selected => #self_type selected :: map snd (#evidence selected) @
              maps Micro_Rust_Names.source_types (the_list (#source selected))) (the_list selection) @
            maps (map_filter fst o #evidence) (the_list supplied)
          val {metadata, owner, native} = align_binding_candidate ctxt entries candidate caller_types entry
          val native = Sign.typ_unify thy (fastype_of candidate, occurrence_type) native
          val relations = map_filter #callable_relation
            (#parameters original @ maps #parameters (the_list (#owner original)))
          fun declared (Meaning_Scoped_Parameter (identity, _)) = [identity]
            | declared meaning = maps declared (meaning_children meaning)
          val relation_declarations = maps (fn {inputs, result, ...}: callable_relation =>
            maps (declared o #2) inputs @ declared (#2 result)) relations
          val relation_variables = maps (fn {inputs, result, channels}: callable_relation =>
            maps (fn typ => Term.add_tvarsT typ [])
              (map #1 inputs @ [#1 result, #state channels, #abort channels, #input channels, #output channels])) relations
          fun required (slot: binding_scheme_parameter) =
            is_some (#witness slot) orelse not (null (#callable_origins slot)) orelse
            member (op =) (#ambient_declarations original) (#declaration slot) orelse
            member (op =) relation_declarations (#declaration slot) orelse
            (case Option.join (AList.lookup (op =) (#source_templates original) (#declaration slot)) of
               NONE => false
             | SOME typ => exists (member (op =) relation_variables) (Term.add_tvarsT typ []))
          fun unavailable_role (Meaning_Mapped (_, _, _, erased, roles, children)) =
                not (null roles) orelse exists (fn (index, child) =>
                  not (member (op =) erased index) andalso unavailable_role child) (map_index I children)
            | unavailable_role (Meaning_Opaque _) = false
            | unavailable_role meaning = exists unavailable_role (meaning_children meaning)
          val rigid = Unsynchronized.ref ([]: (typ * typ) list)
          val rigid_prefix = Name.internal ("urust_source_evidence_" ^ string_of_int (serial ()))
          fun freeze typ =
            let val atoms = Term.add_tvarsT typ []
                val _ = List.app (fn variable as ((_, index), sort) =>
                  let val actual = TVar variable
                  in if is_some (AList.lookup (op =) (!rigid) actual) then () else
                    rigid := (actual, TFree (rigid_prefix ^ string_of_int index ^ "_" ^
                      string_of_int (length (!rigid)), sort)) :: !rigid end) atoms
            in Term.typ_subst_atomic (!rigid) typ end
          fun constrain (slot: binding_scheme_parameter) argument actual meaning pos environment =
            if not (required slot) then environment else
              let
                val expected = case Option.join
                    (AList.lookup (op =) (#source_templates metadata) (#declaration slot)) of
                    SOME typ => typ
                  | NONE => error ("urust: needed source template is absent from legacy registration" ^ Position.here pos)
                val actual = case actual of SOME typ => typ | NONE =>
                  (case argument of SOME (Rust_Numeric_Argument integer) => length_literal ctxt integer
                   | _ => error ("urust: source argument has no checked denotation required by the callable relation" ^
                       Position.here pos))
                val _ = if is_none (#witness slot) andalso unavailable_role meaning then
                    error ("urust: erased source evidence has an unavailable implicit backend role" ^ Position.here pos)
                  else ()
                val _ = if is_none (#witness slot) andalso not (Sign.of_sort thy (actual, #sort slot)) then
                    sort_error Function_Signature ctxt "erased callable dependency" actual (#sort slot) pos else ()
                val actual = Envir.norm_type (#1 environment) actual
                val actual = if is_none (#witness slot) then freeze actual else actual
                val environment = (#1 environment, Int.max (#2 environment, Term.maxidx_of_typ actual))
              in Sign.typ_unify thy (expected, actual) environment end
          fun checked_argument (slot: binding_scheme_parameter) argument =
            let val resolved = resolve_source_arguments_complete ctxt [legacy_binding_slot slot] [argument]
            in (fst (hd (#evidence resolved)), hd (#meanings resolved), snd (hd (#evidence resolved))) end
          fun owner_constraints (template: Micro_Rust_Names.target_template)
              (selected: Micro_Rust_Names.target_selection) (matched: Micro_Rust_Names.target_match) environment =
            let
              val inherited = #parameters (the (#owner metadata))
              fun binding ({variable, kind, value, path, evidence, ...}: Micro_Rust_Names.source_binding) environment =
                let val index = find_index (fn ({name, ...}: Micro_Rust_Names.source_variable) => name = variable)
                      (#variables template)
                    val _ = if index >= 0 then () else raise Fail "uRust source evidence: foreign owner variable"
                    val slot = nth inherited index
                    val _ = if neutral_source_kind (#kind slot) = kind then () else
                      raise Fail "uRust source evidence: changed owner declaration kind"
                in if not (required slot) then environment else
                  case AList.lookup (op =) (#inputs selected) path of
                    SOME (text, position) =>
                      let val authored = synthetic_input_origin position
                          val origin = the_default position authored
                          val pos = if is_some authored then Position.none else origin
                          val argument = URust_Parser.parse_generic_argument_source ctxt
                            (Parser_Lex_Util.positioned_content_source text pos)
                          val (actual, meaning, actual_pos) = checked_argument slot argument
                      in constrain slot (SOME argument) actual meaning actual_pos environment end
                  | NONE =>
                      (case value of
                         Micro_Rust_Names.Source_Rigid (identity, actual_kind) =>
                           (case find_first (fn binding => binding_identity binding = identity) (installed_bindings ctxt) of
                              SOME binding => if neutral_source_kind (#kind (binding_parameter binding)) = actual_kind then
                                constrain slot NONE (binding_template binding)
                                  (Meaning_Scoped_Parameter (identity, #kind (binding_parameter binding)))
                                  (#pos selected) environment
                                else raise Fail "uRust source evidence: changed checked Self declaration kind"
                            | NONE => error "urust: selected source declaration is outside the actual caller scope")
                       | _ => constrain slot NONE evidence (Meaning_HOL (#self_type selected))
                           (#pos selected) environment)
                end
            in fold binding (#bindings matched) environment end
          val native = case (owner, selection) of
              (SOME template, SOME selected) =>
                (case Micro_Rust_Names.match_target ctxt template selected native of
                   NONE => raise Micro_Rust_Names.SOURCE_MATCH
                 | SOME (matched as {types, maxidx, ...}) =>
                     owner_constraints template selected matched (types, maxidx))
            | (NONE, SOME _) => raise Micro_Rust_Names.SOURCE_MATCH
            | _ => native
          val native = case (arguments, supplied) of
              (SOME arguments, SOME resolved) =>
                fold (fn (((slot, argument), (actual, pos)), meaning) =>
                    constrain slot (SOME argument) actual meaning pos)
                  (((#parameters metadata ~~ arguments) ~~ #evidence resolved) ~~ #meanings resolved) native
            | _ => native
          val unfreeze = Term.typ_subst_atomic (map swap (!rigid))
        in SOME (Term.map_types (unfreeze o Envir.norm_type (#1 native)) candidate) end
        handle Pattern.MATCH => NONE | Type.TUNIFY => NONE | Micro_Rust_Names.SOURCE_MATCH => NONE
      (* Distinct locale instances may fail after reading source arguments. Keep their reports
         and use observations isolated until one complete checked result survives. *)
      fun attempt entry =
        let
          val ((result, events), reports) = URust_Report_Transaction.capture_isolated
            (fn () => capture_binding_argument_events ctxt (fn observed => instantiate observed entry))
        in Option.map (fn term => (term, events, reports)) result end
      val results = map_filter attempt entries |> distinct
        (fn ((left, _, _), (right, _, _)) => left aconv right)
    in case results of [] => NONE
      | [(term, events, reports)] =>
          (replay_binding_argument_events ctxt events;
           (* An enclosing candidate is still speculative. Defer callbacks with its existing
              report transaction instead of executing a nested replay before final selection. *)
           URust_Report_Transaction.defer_action
             (fn () => URust_Report_Transaction.replay ctxt reports);
           SOME term)
      | _ => error "urust: inconsistent candidate-owned source evidence for one source" end


  fun resolve_impl_target ctxt target = #1 (resolve_impl_target_identity ctxt target)

  fun resolve_type_identity ctxt target =
    let
      val meaning = Unsynchronized.ref NONE
      fun assemble _ resolved =
        (case resolved of [{typ, meaning = source}] => (meaning := SOME source; [typ])
         | _ => raise Fail "source identity resolution expected one type")
      val typ = the_single (resolve_signature_with Function_Signature ctxt [] [] [target] assemble)
    in (typ, if identity_sensitive (the (!meaning)) then !meaning else NONE) end

  (* The canonical path of an impl target, without reports or errors: the expansion of an alias
     or import when the head is registered, the written path when it is not (yet), and NONE for a
     head that cannot be an impl target. *)
  fun impl_target_key ctxt target =
    (case target_rows target of
       NONE => NONE
     | SOME rows =>
         let val key = written_target_key ctxt rows in
           (case lookup ctxt key of
              NONE => SOME key
            | SOME entry =>
                (case #meaning entry of
                   Meaning_Mapped (base, _, _, _, _, _) => SOME base
                 | _ => NONE))
         end)

  fun instantiate_constructor ctxt rust_name arguments constructor =
    let
      val entry = the (lookup ctxt rust_name)
      val _ = if length arguments = length (#parameter_sorts entry) then () else
        mapping_error "constructor generic arity does not match its declaration" Position.none
      val segments = [Rust_Type_Path_Segment (rust_name, Position.none, SOME arguments,
        make_source_layout Position.none [])]
      val result = the_single (resolve_signature ctxt [Path_Type (segments, make_source_layout Position.none [])])
      val native = constructor |> Term.map_types Type.legacy_freeze_type
      val substitution = Sign.typ_match (Proof_Context.theory_of ctxt)
        (fastype_of native |> body_type |> Logic.varifyT_global, result) Vartab.empty
    in Term.map_types (Envir.subst_type substitution o Logic.varifyT_global) native end

  fun alias_error message pos =
    error ("urust_type_alias: " ^ message ^ Position.here pos)

  fun split_alias_path raw =
    let
      fun split input =
        let val (segment, rest) = Substring.position "::" input in
          if Substring.isEmpty rest then [Substring.string segment]
          else Substring.string segment :: split (Substring.triml 2 rest)
        end
    in split (Substring.full raw) end

  val alias_reserved_segments =
    Micro_Rust_Names.reserved_key_segments @
    ["true", "false", "as", "let", "const", "return", "if", "else",
     "fuel", "while", "loop", "for", "in", "unsafe", "match",
     "match_switch", "match_case", "mut", "type", "struct", "enum", "fn",
     "async", "await", "break", "continue", "crate", "dyn", "extern",
     "impl", "mod", "move", "pub", "ref", "static",
     "super", "trait", "use", "where"] @
    map rust_primitive_name
      [DPT_U8, DPT_U16, DPT_U32, DPT_U64, DPT_U128, DPT_Usize,
       DPT_I8, DPT_I16, DPT_I32, DPT_I64, DPT_I128, DPT_Isize,
       DPT_Bool, DPT_Char, DPT_Str, DPT_Never, DPT_Unit]

  fun declare_generic_alias
      {registration, item_name = (item_name, declaration_pos), parameters = descriptors, rhs}
      lthy =
    let
      val parameters = map (fn Generic_Parameter (name, pos, _) => (name, pos)) descriptors
      val parameter_kinds = map (fn Generic_Parameter (_, _, kind) => kind) descriptors
      val (raw, registration_pos) =
        the_default (item_name, declaration_pos) registration
      val {base, segment_arities, parameters = key_parameters, ...} =
        (case Exn.result
            (fn () => parse_mapping_key_text (raw, Position.none)) () of
           Exn.Res key => key
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else alias_error
               ("invalid alias path " ^ quote raw ^ ": " ^ Runtime.exn_message exn)
               registration_pos)
      val _ =
        if null key_parameters andalso base <> "()" andalso base <> "!" then ()
        else alias_error
          "registration paths cannot contain generic arguments or primitive unit/never spellings"
          registration_pos
      val segments = split_alias_path base
      val _ =
        (case find_first (member (op =) alias_reserved_segments) segments of
           NONE => ()
         | SOME segment =>
             alias_error
               ("invalid alias path " ^ quote raw ^ ": reserved segment " ^
                 quote segment ^ " cannot occur in an alias path")
               registration_pos)
      val _ =
        if List.last segments = item_name then ()
        else error
          ("urust_type_alias: registration path terminal " ^
            quote (List.last segments) ^ " must match item name " ^
            quote item_name ^ Position.here_list [registration_pos, declaration_pos])
      val parameter_names = map fst parameters
      val _ =
        (case duplicates (op =) parameter_names of
           [] => ()
         | duplicate :: _ =>
             let
               val positions =
                 parameters |> filter (fn (name, _) => name = duplicate) |> map snd
             in error
               ("urust_type_alias: duplicate type parameter " ^ quote duplicate ^
                 Position.here_list positions)
             end)
      val {fresh, normalize, check_sort, backend, backend_slots, ...} =
        inference_state Alias_Declaration lthy []
      val base_sort = the_default [] (Object_Logic.get_base_sort lthy)
      val parameter_types = map (fn kind => fresh
        (case kind of Type_Parameter => base_sort | Const_Parameter => \<^sort>\<open>len0\<close>)) parameter_kinds
      val parameter_table =
        Symtab.make
          (map_index
            (fn (index, ((name, _), typ)) =>
              (name, {typ = typ, meaning = (case nth parameter_kinds index of
                Type_Parameter => Meaning_Parameter index
              | Const_Parameter => Meaning_Const_Parameter index)}))
            (parameters ~~ parameter_types))
      val used_parameters = Unsynchronized.ref ([]: string list)
      val dependencies = Unsynchronized.ref ([]: string list)
      val captured_escapes = Unsynchronized.ref ([]: (Input.source * typ) list)

      fun parameter name arities pos =
        (case Symtab.lookup parameter_table name of
           NONE => NONE
         | SOME value =>
             let
               val _ =
                 if arities = [0] then ()
                 else alias_error
                   ("type parameter " ^ quote name ^ " cannot take generic arguments")
                   pos
               val _ = used_parameters := insert (op =) name (!used_parameters)
               val _ = Navigation.defer_report lthy pos Markup.tfree
             in SOME value end)

      fun dependency name active pos =
        let
          val inherited =
            (case active of SOME (entry: entry) => #dependencies entry | NONE => [])
          val _ =
            if name = base orelse member (op =) inherited base then
              alias_error
                ("recursive alias dependency " ^ quote name ^ " reaches " ^ quote base)
                pos
            else ()
          val _ =
            dependencies :=
              fold (insert (op =)) (name :: inherited) (!dependencies)
        in () end

      fun read_escape source =
        let
          val pos = Input.pos_of source
          val typ =
            positioned_result Alias_Declaration [pos]
              (fn () => Syntax.read_typ lthy (Syntax.implode_input source))
          val _ =
            if null (Term.add_tfreesT typ []) andalso
                null (Term.add_tvarsT typ []) then ()
            else alias_error
              "unrelated HOL type variables are not supported in aliases; use Rust type parameters"
              pos
          val _ = captured_escapes := (source, typ) :: !captured_escapes
        in typ end

      val result =
        the_single
          (resolve_values Alias_Declaration lthy read_escape
            check_sort normalize backend parameter dependency [rhs])
      (* Rust rejects unused type alias parameters, but permits unused const
         parameters. Keep their slots and sorts in the registered scheme. *)
      val unused =
        parameter_names ~~ parameter_kinds
        |> filter (fn (name, kind) =>
          kind = Type_Parameter andalso not (member (op =) (!used_parameters) name))
        |> map fst
      val _ =
        if null unused then ()
        else alias_error
          ("unused type parameters " ^ commas_quote unused)
          (the_default declaration_pos
            (AList.lookup (op =) parameters (hd unused)))
      fun normalized_parameter typ =
        (case normalize typ of
           parameter as TVar (_, sort) =>
             (parameter, Sign.minimize_sort (Proof_Context.theory_of lthy) sort)
         | _ => raise Fail
             "uRust type registry: alias parameter became a concrete type")
      val normalized_parameters = map normalized_parameter parameter_types
      val normalized_backend =
        map (apsnd normalized_parameter) (backend_slots ())
      val parameter_sorts = map snd normalized_parameters
      val role_sorts = map (apsnd snd) normalized_backend
      val substitutions =
        map_index
          (fn (index, (parameter, sort)) =>
            (parameter, canonical_parameter index sort))
          normalized_parameters @
        map
          (fn (role, (parameter, sort)) =>
            (parameter, canonical_backend_parameter role sort))
          normalized_backend
      val template =
        normalize (#typ result)
        |> Term.typ_subst_atomic substitutions
        |> Proof_Context.cert_typ lthy
      val expected_variables =
        map_index (fn (index, sort) => canonical_parameter index sort)
          parameter_sorts @
        map (fn (role, sort) => canonical_backend_parameter role sort)
          role_sorts
      val _ =
        if null (Term.add_tfreesT template []) andalso
            forall
              (fn variable => member (op =) expected_variables (TVar variable))
              (Term.add_tvarsT template [])
        then ()
        else raise Fail
          "uRust type registry: alias template contains an uncaptured type variable"
      val arities =
        take (length segment_arities - 1) segment_arities @
          [length parameters]
      val erased_parameters = map_index (fn (index, ((name, _), sort)) =>
        if member (op =) (!used_parameters) name andalso
           not (member (op =) (Term.add_tvarsT template []) (("_urust_type", index), sort))
        then SOME index else NONE) (parameters ~~ parameter_sorts) |> map_filter I
      val candidate =
        make_entry Alias declaration_pos arities template
          parameter_kinds parameter_sorts erased_parameters role_sorts (#meaning result) (!dependencies)
      val prepared = preflight lthy base candidate
      val _ =
        List.app
          (fn (_, pos) => Navigation.defer_report lthy pos Markup.tfree)
          parameters
    in
      (case prepared of
         Existing _ => lthy
       | Refined _ => raise Fail "uRust alias declaration unexpectedly refined a shared policy"
       | Fresh entry =>
           let
             val recipe =
               {parameters = parameter_names,
                rhs = canonical_alias_recipe lthy parameter_names rhs,
                escapes = !captured_escapes, identity = #identity entry}: alias_recipe
             fun morph phi =
               {parameters = #parameters recipe, rhs = #rhs recipe,
                escapes = map (apsnd (Morphism.typ phi)) (#escapes recipe),
                identity = #identity recipe}: alias_recipe
           in
             install_new base entry lthy
             |> Local_Theory.declaration
                 {pervasive = false, syntax = true, pos = declaration_pos}
                 (fn phi => Alias_Recipes.map (Symtab.update (base, morph phi)))
           end)
    end

  fun declare_alias {registration, item_name, parameters, rhs} lthy =
    declare_generic_alias {registration = registration, item_name = item_name,
      parameters = map (fn (name, pos) => Generic_Parameter (name, pos, Type_Parameter)) parameters,
      rhs = rhs} lthy

  fun cast_target (Meaning_Primitive DPT_U8) = SOME (CT_Unsigned UT_U8)
    | cast_target (Meaning_Primitive DPT_U16) = SOME (CT_Unsigned UT_U16)
    | cast_target (Meaning_Primitive DPT_U32) = SOME (CT_Unsigned UT_U32)
    | cast_target (Meaning_Primitive DPT_U64) = SOME (CT_Unsigned UT_U64)
    | cast_target (Meaning_Primitive DPT_Usize) = SOME (CT_Unsigned UT_Usize)
    | cast_target (Meaning_Primitive DPT_I32) = SOME (CT_Signed ST_I32)
    | cast_target (Meaning_Primitive DPT_I64) = SOME (CT_Signed ST_I64)
    | cast_target (Meaning_Pointer (mutability, target)) =
        (case cast_target target of
           SOME (CT_Unsigned width) => SOME (CT_RawPointer (mutability, width))
         | _ => NONE)
    | cast_target _ = NONE

  fun resolve_cast _ (SCT_Primitive (target, _)) = target
    | resolve_cast ctxt source =
        let
          val rust_type = source_cast_target_rust_type source
          val {normalize, check_sort, backend, ...} =
            inference_state Cast_Target ctxt []
          fun read_escape source =
            unsupported Cast_Target "HOL type escapes" (Input.pos_of source)
          val result =
            the_single
              (resolve_values Cast_Target ctxt read_escape check_sort normalize
                backend no_parameter no_dependency [rust_type])
        in
          (case cast_target (#meaning result) of
             SOME target => target
           | NONE =>
               error
                 ("urust_expr: expanded Rust type has no supported cast operation" ^
                   Position.here (rust_type_position rust_type)))
        end

  fun unknown_mapping_option (name, pos) =
    mapping_error ("unknown option " ^ quote name) pos

  datatype mapping_option_config = Cartouche_Option | String_Option
  val mapping_option_configs =
    Symtab.make [("implicit", Cartouche_Option), ("erase", Cartouche_Option),
      ("model", Cartouche_Option), ("shared", Cartouche_Option),
      ("representation", String_Option)]

  fun add_mapping_option ((name, pos), value) options =
    if Symtab.defined options name then mapping_error ("duplicate option " ^ quote name) pos
    else
      (case value of
         SOME source => Symtab.update (name, source) options
       | NONE => mapping_error ("option " ^ quote name ^ " expects " ^
           (if name = "representation" then "a quoted representation name" else "a cartouche payload"))
           pos)

  val parse_mapping_options =
    URust_Option_Parser.command_list unknown_mapping_option mapping_option_configs
      (fn Cartouche_Option => Parse.token Parse.cartouche >> Parser_Lex_Util.cartouche_source
        | String_Option => Parse.token Parse.string >> Token.input_of)
      add_mapping_option Symtab.empty

  fun declare_manual (options, payload) lthy =
    let
      val (result, reports) = URust_Report_Transaction.capture (fn () =>
        let val roles = (case Symtab.lookup options "implicit" of
          NONE => [] | SOME source => read_implicit_roles lthy source) @
          (case Symtab.lookup options "model" of
            NONE => [] | SOME source => read_model_roles lthy source)
            val erased = case Symtab.lookup options "erase" of
              NONE => [] | SOME source => read_erased_parameters lthy source
             val shared = Option.map (read_shared_policy lthy)
               (Symtab.lookup options "shared")
        in
          case Symtab.lookup options "representation" of
            NONE => declare_mapping Manual roles erased shared payload lthy
          | SOME name_source =>
              declare_representation name_source roles erased shared payload lthy
        end)
      val _ = URust_Report_Transaction.replay result reports
    in result end

  val _ =
    Outer_Syntax.local_theory \<^command_keyword>\<open>urust_type\<close>
      "declare a context-local Rust-to-HOL type mapping"
      (parse_mapping_options --
        ((Parse.token Parse.string --| \<^keyword>\<open>=\<close>) --
        Parse.embedded_input >>
          (fn (token, source) =>
            (Token.input_of token, source))) >> declare_manual)
end
\<close>

end
