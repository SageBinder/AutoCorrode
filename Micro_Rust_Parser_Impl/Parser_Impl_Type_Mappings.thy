theory Parser_Impl_Type_Mappings
  imports
    Parser_Impl_AST
    Parser_Utils
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
parameters and then erased; they never change the resolved type. Shared references \<open>&T\<close>, and
references in datatype fields, aliases and cast targets, remain rejected. A function with a
declared HOL type resolves no signature type while retaining these lifetime scope rules and the
lexical restrictions on Self and self in Rust type paths.

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
subset excludes references, pointers, arrays, slices, callable types, impl Trait, macros, HOL
escapes, lifetimes, associated bindings and general const expressions, recursively. Known bounds
require rigid existing evidence, without strengthening a discarded implicit role.
\<close>

ML\<open>
signature URUST_TYPE_MAPPINGS =
sig
  type entry
  datatype backend_role = Address | Global

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

  type impl_self =
    {canonical_path: string, self_type: typ, target_pos: Position.T,
     report_reference: Position.T -> unit}
  val resolve_impl_target: Proof.context -> URust_AST.rust_type -> impl_self
  type source_identity
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
end

structure URust_Type_Mappings :> URUST_TYPE_MAPPINGS =
struct
  open URust_AST
  structure Navigation = Micro_Rust_Semantic_Navigation

  val mappingN = "micro_rust_type_mapping"

  datatype backend_role = Address | Global

  fun role_index Address = 0 | role_index Global = 1
  fun role_name Address = "address" | role_name Global = "global"
  val backend_roles = [Address, Global]
  fun role_order roles = filter (member (op =) roles) backend_roles

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

  fun origin_text Manual = "urust_type declaration"
    | origin_text (Generated hol_type_name) =
        "generated datatype " ^ quote hol_type_name
    | origin_text Alias = "urust_type_alias declaration"

  fun alias_origin Alias = true
    | alias_origin _ = false

  fun entry_origin ({origin, ...}: entry) = origin_text origin

  fun same_entry
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

  fun join_entry base (left: entry, right: entry) =
    if same_entry (left, right)
    then #1 (ordered_entries (left, right))
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

  fun canonical_backend_parameter index sort =
    TVar (("_urust_backend", index), sort)

  (* A native locale export may rename schematic indexes and basenames. Transport the
     template and all slot witnesses as one type, then restore canonical identities from
     those transported witnesses. Transforming witnesses separately loses their sharing. *)
  fun morph_scheme phi template parameter_sorts erased_parameters role_sorts =
    let
      val retained = map_index I parameter_sorts
        |> filter_out (fn (index, _) => member (op =) erased_parameters index)
      val parameters = map (fn (index, sort) => canonical_parameter index sort) retained
      val roles = map (fn (role, sort) => canonical_backend_parameter (role_index role) sort)
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
        map (fn (role, sort) => canonical_backend_parameter (role_index role) sort) role_sorts'
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
        | finish_source (Meaning_Array (element, length)) =
            Meaning_Array (finish_source element, finish_source length)
        | finish_source (Meaning_Pointer (mode, typ)) = Meaning_Pointer (mode, finish_source typ)
        | finish_source (Meaning_Reference (mode, typ)) = Meaning_Reference (mode, finish_source typ)
        | finish_source (Meaning_HOL typ) = Meaning_HOL (the_single (finish [typ]))
        | finish_source meaning = meaning
    in finish_source end

  fun read_implicit_roles lthy source =
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
      fun role (name, pos) =
        (case name of "address" => Address | "global" => Global
         | _ => mapping_error ("unknown implicit role " ^ quote name) pos)
      val roles = map (fn (name, variable) => (role name, variable, snd name)) bindings
      fun distinct_binding (role, (name, pos), role_pos) (seen_roles, seen_names) =
        if member (op =) seen_roles role then
          mapping_error ("duplicate implicit role " ^ quote (role_name role)) role_pos
        else if member (op =) seen_names name then
          mapping_error ("duplicate implicit template variable " ^ quote name) pos
        else (role :: seen_roles, name :: seen_names)
      val _ = fold distinct_binding roles ([], [])
    in map (fn (role, variable, _) => (role, variable)) roles end

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
          (TFree (name, sort), canonical_backend_parameter (role_index role) sort))
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
     declaration_pos = declaration_pos,
     origin = origin,
     identity = serial ()}: entry

  fun morph_entry phi
      ({segment_arities, template, parameter_kinds, parameter_sorts, erased_parameters,
        backend_roles, backend_parameter_sorts,
        meaning, dependencies, declaration_pos, origin, identity}: entry) =
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
       declaration_pos = declaration_pos,
       origin = origin,
       identity = identity}: entry
    end

  datatype preflight =
      Existing of entry
    | Fresh of entry

  fun preflight ctxt base (candidate: entry) =
    (case lookup ctxt base of
       NONE => Fresh candidate
     | SOME active =>
         if same_entry (active, candidate)
         then Existing active
         else
           (ignore (join_entry base (active, candidate));
            raise Fail
              "uRust type registry: conflicting join unexpectedly returned"))

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
     | Fresh entry => install_new base entry lthy)

  fun report_parameters ctxt
      ({parameters, parameter_positions, ...}: key) =
    List.app
      (fn (parameter, pos) =>
        Navigation.defer_report ctxt pos Markup.tfree)
      (parameters ~~ parameter_positions)

  fun declare_mapping origin roles erased_names (key_source, source)
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
    in install_prepared base candidate lthy end

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
          (TFree parameter, canonical_backend_parameter (role_index role) sort)) role_parameters
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

  (* Match declared canonical role slots against the checked Self type. Neither variable names
     nor sort coincidence identify a role, and source placeholders remain separate. *)
  fun impl_backend_parameters ctxt ({canonical_path, self_type, ...}: impl_self) =
    (case lookup ctxt canonical_path of
       NONE => []
     | SOME entry =>
         if null (#backend_roles entry) then []
         else
           let
             val substitution = Sign.typ_match (Proof_Context.theory_of ctxt)
               (#template entry, self_type) Vartab.empty
           in map2 (fn role => fn sort =>
             (role, Envir.subst_type substitution (canonical_backend_parameter (role_index role) sort)))
             (#backend_roles entry) (#backend_parameter_sorts entry) end)

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

  structure Generic_Scope = Proof_Data
  (
    type T = generic_scope option
    fun init _ = NONE
  )

  val generic_scope = Generic_Scope.get

  fun scope_parameters ctxt =
    (case generic_scope ctxt of NONE => [] | SOME {parameters} => parameters)

  structure Generic_Uses = Proof_Data
  (
    type T = (generic_parameter list -> typ list -> bool -> unit) option
    fun init _ = NONE
  )

  fun same_generic_parameter (left: generic_parameter, right: generic_parameter) =
    #rust left = #rust right andalso #kind left = #kind right andalso
    #hol left = #hol right andalso #bounds left = #bounds right andalso
    Position.properties_of (#pos left) = Position.properties_of (#pos right) andalso
    pointer_eq (#report_reference left, #report_reference right)

  structure Generic_Identities = Proof_Data
  (
    type T = (generic_parameter * serial) list
    fun init _ = []
  )
  structure Source_Only_Parameters = Proof_Data
  (
    type T = generic_parameter list
    fun init _ = []
  )
  structure Source_Only_Positions = Proof_Data
  (
    type T = Position.T list Unsynchronized.ref option
    fun init _ = NONE
  )

  fun with_generic_scope (scope as {parameters}: generic_scope) ctxt =
    let
      val previous = Generic_Identities.get ctxt
      fun identity parameter =
        (parameter, case find_first (fn (old, _) => same_generic_parameter (parameter, old)) previous of
          SOME (_, identity) => identity | NONE => serial ())
    in ctxt |> Generic_Scope.put (SOME scope)
      |> Generic_Identities.put (map identity parameters)
      |> Source_Only_Parameters.put [] end

  fun with_source_only_parameters names ctxt =
    Source_Only_Parameters.put
      (filter (fn parameter => member (op =) names (fst (#hol parameter)))
        (scope_parameters ctxt)) ctxt

  fun parameter_has_witness ctxt parameter =
    not (exists (fn installed => same_generic_parameter (parameter, installed))
      (Source_Only_Parameters.get ctxt))

  fun scoped_meaning ctxt parameter =
    let
      val identity = #2 (the (find_first
        (fn (installed, _) => same_generic_parameter (parameter, installed))
        (Generic_Identities.get ctxt)))
    in Meaning_Scoped_Parameter (identity, #kind parameter) end

  fun capture_generic_use_events ctxt action =
    (case generic_scope ctxt of
       NONE => (action ctxt, {source_uses = [], witness_uses = []})
     | SOME {parameters = []} => (action ctxt, {source_uses = [], witness_uses = []})
     | SOME {parameters} =>
         let
           val source_uses = Unsynchronized.ref ([]: string list)
           val witness_uses = Unsynchronized.ref ([]: string list)
           val active = Unsynchronized.ref true
           fun note uses name = if !active then uses := insert (op =) name (!uses) else ()
           val parent = Generic_Uses.get ctxt
           (* An empty type list explicitly observes source identity, without creating a HOL
              witness. Native type reads observe only the actual variables in those types. *)
           fun observe current types demand =
             let
               val names = maps (fn typ => map fst (Term.add_tfreesT typ [])) types
               fun observe_parameter parameter =
                 if exists (fn tracked => same_generic_parameter (parameter, tracked)) parameters
                    andalso (null types orelse member (op =) names (fst (#hol parameter)))
                 then (note source_uses (fst (#hol parameter));
                   if demand then note witness_uses (fst (#hol parameter)) else ())
                 else ()
               val _ = List.app observe_parameter current
             in Option.app (fn observe_parent => observe_parent current types demand) parent end
           val observed_ctxt = Generic_Uses.put (SOME observe) ctxt
         in
           Thread_Attributes.uninterruptible_body (fn run =>
             let
               val result = Exn.capture0 (run (fn () => action observed_ctxt)) ()
               val recorded = {source_uses = rev (!source_uses), witness_uses = rev (!witness_uses)}
               val _ = active := false
             in (Exn.release result, recorded) end)
         end)

  fun capture_generic_uses ctxt action =
    let val (result, {witness_uses, ...}) = capture_generic_use_events ctxt action
    in (result, witness_uses) end

  val speculative_generic_callbacks = Thread_Data.var (): bool Thread_Data.var

  fun capture_generic_argument_events ctxt action =
    Thread_Data.setmp speculative_generic_callbacks (SOME true)
      (fn () => capture_generic_use_events (Generic_Uses.put NONE ctxt) action) ()

  fun replay_generic_argument_events ctxt {source_uses, witness_uses} =
    let
      fun replay parameter =
        let val name = fst (#hol parameter)
        in
          if member (op =) source_uses name then
            Option.app (fn observe => observe [parameter] []
              (member (op =) witness_uses name)) (Generic_Uses.get ctxt)
          else ()
        end
    in List.app replay (scope_parameters ctxt) end

  fun note_generic_types ctxt types =
    if null types then () else
      Option.app (fn observe => observe (scope_parameters ctxt) types true) (Generic_Uses.get ctxt)

  fun observe_generic_reference demand ctxt parameter =
    if exists (fn installed => same_generic_parameter (parameter, installed))
        (scope_parameters ctxt)
    then Option.app (fn observe => observe [parameter] [] demand) (Generic_Uses.get ctxt)
    else ()

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
    (observe_generic_reference true ctxt parameter;
     generic_reference_callback true parameter pos)

  fun report_generic_source_reference ctxt parameter pos =
    (observe_generic_reference false ctxt parameter;
     Option.app (fn positions => positions := pos :: !positions) (Source_Only_Positions.get ctxt);
     generic_reference_callback false parameter pos)

  fun resolve_generic ctxt normalize base arities pos =
    (case find_index (fn ({rust, ...}: generic_parameter) => rust = base)
        (scope_parameters ctxt) of
       ~1 => NONE
     | index =>
         let
           val parameter as {hol, kind, ...} =
             nth (scope_parameters ctxt) index
           val _ = if arities = [0] then ()
             else error ("urust: generic parameter " ^ base ^
               " takes no generic arguments" ^ Position.here pos)
           val _ = Navigation.defer_report ctxt pos Markup.tfree
           val _ = report_generic_reference ctxt parameter pos
         in
           SOME {typ = normalize (TFree hol),
             meaning = scoped_meaning ctxt parameter}
         end)

  type generic_scheme_parameter =
    {rust: string, kind: generic_parameter_kind, hol: string * sort}
  type generic_source_parameter =
    {rust: string, kind: generic_parameter_kind, hol: (string * sort) option,
     sort: sort, bounds: string list, source_used: bool option}
  type function_scheme =
    {terms: term list, sources: serial list,
     parameters: generic_source_parameter list, pos: Position.T}

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

  fun same_function_scheme (left: function_scheme, right: function_scheme) =
    eq_list (op aconv) (#terms left, #terms right) andalso
      map parameter_core (#parameters left) = map parameter_core (#parameters right) andalso
      #sources left = #sources right

  fun merge_source_usage (left: generic_source_parameter, right: generic_source_parameter) =
    let
      val used = (case (#source_used left, #source_used right) of
          (NONE, used) => used | (used, NONE) => used
        | (SOME first, SOME second) => if first = second then SOME first
            else error "urust_fn: conflicting source-use metadata for one source")
    in {rust = #rust left, kind = #kind left, hol = #hol left, sort = #sort left,
      bounds = #bounds left, source_used = used}: generic_source_parameter end

  fun add_function_scheme (candidate: function_scheme) entries =
    (case find_first (fn entry => same_function_scheme (entry, candidate)) entries of
       SOME existing =>
         let
           val parameters = map merge_source_usage (#parameters existing ~~ #parameters candidate)
           val merged = {terms = #terms existing, sources = #sources existing,
             parameters = parameters, pos = #pos existing}: function_scheme
         in map (fn entry => if same_function_scheme (entry, existing) then merged else entry) entries end
     | NONE =>
      (case find_first (fn (entry: function_scheme) =>
          hd (#terms entry) aconv hd (#terms candidate) andalso
          nth (#terms entry) 1 aconv nth (#terms candidate) 1 andalso
          not (eq_list (op aconv) (#terms entry, #terms candidate) andalso
            #parameters entry = #parameters candidate)) entries of
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

  fun register_function_scheme {identity, backend, sources, parameters, pos} witnesses lthy =
    if null parameters then lthy
    else
      let
        val terms = Variable.polymorphic lthy
          (backend :: identity :: map Logic.mk_type witnesses)
        fun install phi =
          let
            val transformed =
              map (Morphism.term phi) terms |> normalize_function_scheme
            val witnesses = map Logic.dest_type (drop 2 transformed)
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
            {terms = transformed, sources = sources, parameters = transported, pos = pos}) end
      in
        Local_Theory.declaration {pervasive = false, syntax = false, pos = pos} install lthy
      end

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

  fun consistent_parameters [] = NONE
    | consistent_parameters (entry :: entries: function_scheme list) =
        if forall (fn other => #parameters other = #parameters entry) entries
        then SOME (#parameters entry)
        else error ("urust_fn: inconsistent generic metadata for one source" ^
          Position.here_list (map #pos (entry :: entries)))

  fun witnessed_parameters parameters =
    if forall (is_some o #hol) (parameters: generic_source_parameter list) then
      SOME (map (fn {rust, kind, hol, ...} => {rust = rust, kind = kind, hol = the hol}) parameters)
    else NONE

  fun generic_scheme ctxt backend =
    Option.mapPartial witnessed_parameters
      (consistent_parameters (matching_function_schemes ctxt backend))

  fun schemes_for_source ctxt source =
    filter (fn (entry: function_scheme) => member (op =) (#sources entry) source)
      (function_schemes ctxt)

  fun generic_source_scheme_for_source ctxt source = consistent_parameters (schemes_for_source ctxt source)
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
          val witnesses = map (Logic.dest_type #> Envir.subst_type (#1 environment)) (drop 2 terms)
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
      fun instantiate ({terms, parameters, ...}: function_scheme) =
        if length parameters <> length arguments orelse
          not (forall (fn (parameter, (argument, _)) =>
            is_some (#hol parameter) = is_some argument) (parameters ~~ arguments)) then NONE
        else
           let
             val thy = Proof_Context.theory_of ctxt
             val witnesses = map Logic.dest_type (drop 2 terms)
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
    instantiate_function_schemes ctxt (matching_function_schemes ctxt backend) candidate
      (map (apfst SOME) arguments)

  fun instantiate_generic_scheme_for_source ctxt source candidate arguments =
    instantiate_function_schemes ctxt (schemes_for_source ctxt source) candidate
      (map (apfst SOME) arguments)

  fun instantiate_generic_source_scheme_for_source ctxt source candidate arguments =
    instantiate_function_schemes ctxt (schemes_for_source ctxt source) candidate arguments

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

  (* One inference environment and one lazy role table belong to a complete
     signature or field batch. Canonical registry slots are never reused as
     flexible variables by two independent resolutions. *)
  fun inference_state kind ctxt initial_types =
    let
      val instance_name = "_urust_inference_" ^ string_of_int (serial ())
      val unification: (Type.tyenv * int) Unsynchronized.ref =
        Unsynchronized.ref
          (Vartab.empty,
           fold Term.maxidx_typ initial_types (Variable.maxidx_of ctxt))
      val backend_slots: (backend_role * typ) list Unsynchronized.ref =
        Unsynchronized.ref
          (case impl_self ctxt of NONE => [] | SOME self => impl_backend_parameters ctxt self)

      fun fresh sort =
        let
          val (environment, index) = !unification
          val next = index + 1
          val _ = unification := (environment, next)
        in Type_Infer.param next (instance_name, sort) end

      fun normalize typ =
        Envir.norm_type (#1 (!unification)) typ

      fun check_sort base argument sort pos =
        let
          val constraint = fresh sort
          val environment =
            Type.unify (Proof_Context.tsig_of ctxt)
              (argument, constraint) (!unification)
            handle Type.TUNIFY =>
              sort_error kind ctxt base (normalize argument) sort pos
        in unification := environment end

      fun backend role_sorts pos =
        let
          fun allocated (role, _) =
            (case AList.lookup (op =) (!backend_slots) role of
               SOME slot => slot
             | NONE =>
                 let
                   val slot = fresh []
                   val _ = backend_slots := (role, slot) :: !backend_slots
                 in slot end)
          (* Allocate the whole request before adding constraints, retaining the established
             pair's fresh-variable order while allowing a later request to add one role. *)
          val slots = map allocated role_sorts
          val _ = List.app (fn (slot, (role, sort)) =>
            check_sort ("implicit " ^ role_name role ^ " backend") slot sort pos)
            (slots ~~ role_sorts)
        in map normalize slots end
    in
      {fresh = fresh, normalize = normalize, check_sort = check_sort,
       backend = backend,
       backend_slots = fn () =>
         map_filter (fn role =>
           Option.map (pair role) (AList.lookup (op =) (!backend_slots) role)) backend_roles}
    end

  fun resolve_value_operations kind ctxt read_escape check_sort normalize backend
      parameter dependency =
    let
      (* Raw pointers and mutable references share one reference model and one backend pair. *)
      fun reference_typ target pos =
        let
          val [address, global] =
            backend [(Address, \<^sort>\<open>type\<close>), (Global, \<^sort>\<open>type\<close>)] pos
        in
          Term.typ_subst_atomic
            [(\<^typ>\<open>'urust_address\<close>, address),
             (\<^typ>\<open>'urust_global\<close>, global),
             (\<^typ>\<open>'urust_value\<close>, target)]
            \<^typ>\<open>('urust_address, 'urust_global, 'urust_value) Global_Store.ref\<close>
          |> Proof_Context.cert_typ ctxt
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
        if null sort orelse Sign.subsort (Proof_Context.theory_of ctxt) (\<^sort>\<open>type\<close>, sort)
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

      fun source_argument expected (Rust_Type_Argument typ) = source_type (SOME expected) typ
        | source_argument Const_Parameter (Rust_Numeric_Argument integer) =
            {meaning = Meaning_Numeric (unsigned_value integer), evidence = NONE,
             pos = integer_literal_position integer}
        | source_argument Type_Parameter (Rust_Numeric_Argument integer) =
            unsupported kind "numeric generic arguments for type parameters"
              (integer_literal_position integer)
        | source_argument _ (Rust_Lifetime_Argument (Rust_Lifetime (_, pos))) =
            unsupported kind "lifetime generic arguments" pos
        | source_argument _ (Rust_Associated_Type_Argument (_, pos, _)) =
            unsupported kind "associated type bindings" pos
        | source_argument _ (Rust_Const_Expression_Argument source) =
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
                  evidence = SOME (TFree (#hol parameter)), pos = pos} end
            else if base = "Self" then
              (case impl_self ctxt of NONE => self_outside_impl pos
               | SOME {self_type, report_reference, ...} =>
                   (if arities = [0] then () else mapping_error
                     "Self cannot take generic arguments" pos;
                    report_reference pos;
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
                val _ = List.app (fn position => report_reference ctxt position base entry) positions
              in {meaning = instantiate_meaning (map #meaning resolved) (#meaning entry),
                evidence = evidence, pos = pos} end
        end

      and source_type expected rust_type =
        let
          val value = (case rust_type of
              Group_Type (typ, _) => source_type expected typ
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
            | _ => unsupported kind "this source type form in an erased argument"
                (rust_type_position rust_type))
          val _ = case expected of NONE => () | SOME role =>
            if source_kind (#meaning value) = role then ()
            else unsupported kind (if role = Const_Parameter then "type parameters used as const arguments"
              else "const parameters used as type arguments") (#pos value)
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
                 (case active of
                    SOME entry => entry
                  | NONE => unknown_type kind base pos)
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
                     ((("_urust_backend", role_index role), sort), argument))
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
               val _ = report_use ctxt base entry positions primitive
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
        | resolve_type_value role (Group_Type (typ, _)) =
            resolve_type role typ
        (* Function_Signature also resolves constructor turbofish arguments, but the generic lexer
           has no reference syntax, so only function signatures reach the mutable case. *)
        | resolve_type_value _ (Reference_Type (BM_Mut, _, target, layout)) =
            if signature_kind kind then
              let val target_type = resolve_type NONE target in
                {typ = reference_typ (#typ target_type) (source_span layout),
                 meaning = Meaning_Reference (BM_Mut, #meaning target_type)}
              end
            else unsupported kind "Rust reference types" (source_span layout)
        | resolve_type_value _ (Reference_Type (BM_Imm, _, _, layout)) =
            if signature_kind kind then
              error
                ("urust_fn: shared Rust references (&T) are not supported in function signatures; " ^
                  "use &mut T or \<tau>\<open>...\<close>" ^ Position.here (source_span layout))
            else unsupported kind "Rust reference types" (source_span layout)
        | resolve_type_value _ (Raw_Pointer_Type (mutability, target, layout)) =
            let val target_type = resolve_type NONE target in
              {typ = reference_typ (#typ target_type) (source_span layout),
               meaning = Meaning_Pointer (mutability, #meaning target_type)}
            end
        | resolve_type_value _ (Slice_Type (_, layout)) =
            unsupported kind "Rust slice types" (source_span layout)
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
      fun call_argument ({kind = expected, hol, sort, ...}: generic_source_parameter) argument =
        (case hol of
           NONE =>
             let
               val value = source_argument expected argument
               val _ = source_sort "function argument" sort value
             in {typ = NONE, meaning = #meaning value, pos = #pos value} end
         | SOME (_, sort) =>
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
             in {typ = SOME (#typ value), meaning = #meaning value, pos = pos} end)
    in {types = map (resolve_type NONE),
      arguments = fn specifications => fn arguments => map2 call_argument specifications arguments} end

  fun resolve_values kind ctxt read_escape check_sort normalize backend parameter dependency rust_types =
    #types (resolve_value_operations kind ctxt read_escape check_sort normalize backend
      parameter dependency) rust_types

  fun no_parameter _ _ _ = NONE
  fun no_dependency _ _ _ = ()

  fun finish_backend ctxt normalize slots types =
    let
      val names =
        Name.variants (Variable.names_of ctxt)
          ["'urust_address", "'urust_global"]
      fun parameter (typ as TVar (_, sort)) =
            (typ, sort)
        | parameter (typ as TFree (_, sort)) = (typ, sort)
        | parameter _ =
            raise Fail
              "uRust type registry: backend parameter became a concrete type"
      val normalized = map (apsnd (parameter o normalize)) slots
      val parameters = map (fn (role, (TFree parameter, _)) => (role, parameter)
        | (role, (_, sort)) => (role, (nth names (role_index role), sort))) normalized
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

  (* Datatypes and functions share the positioned override reader and name checks. Sort
     inference remains with each declaration's existing resolution environment. *)
  fun read_parameter_names ctxt parameters overrides =
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
          val declared = case explicit of NONE => NONE | SOME (raw, override_pos) =>
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

  fun parameter_names ctxt parameters overrides =
    map #hol (read_parameter_names ctxt parameters overrides)

  fun resolve_declaration_roles ctxt parameters overrides rust_types =
    let
      fun descriptor (Generic_Parameter (name, pos, kind)) = (name, pos, kind)
      val descriptors = map descriptor parameters
      val names = map (fn {hol = (name, _), declared, pos} => (name, declared, pos))
        (read_parameter_names ctxt parameters overrides)
      val {fresh, normalize, check_sort, backend, backend_slots} =
        inference_state Datatype_Fields ctxt []
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
      val resolved = resolve_values Datatype_Fields ctxt escape check_sort normalize backend
        parameter no_dependency rust_types
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
    in {types = types, source_parameters = map snd inferred, backend_parameters = backend_parameters} end

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

  (* Check lexical Rust restrictions without interpreting any retained type. The operand walk
     includes function-pointer types, impl Trait and associated-type binding values. Const-expression
     and HOL source escapes retain their own syntax and are not Rust type paths. *)
  fun check_signature_syntax ctxt rust_types =
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
                        NONE => self_outside_impl pos
                      | SOME _ =>
                          if null (the_default [] arguments) then ()
                          else error ("urust: Self cannot take generic arguments" ^ Position.here pos))
                 | Rust_Type_Path_Segment (name, pos, _, _) :: _ => key name pos
                 | [] => ())
              val _ = List.app segment segments
            in List.app check (rust_type_operands typ) end
        | check typ = List.app check (rust_type_operands typ)
    in List.app check rust_types end

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
  fun resolve_signature_operations kind original_ctxt leading lifetimes rust_types
      specifications arguments assemble =
    let
      val source_positions = Unsynchronized.ref ([]: Position.T list)
      val ctxt = Source_Only_Positions.put (SOME source_positions) original_ctxt
      val _ = check_lifetimes lifetimes rust_types
      val parameters = scope_parameters ctxt
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
          let val parsed = map (parse read_ctxt) reads in
            positioned_result kind (maps #cited reads)
              (fn () => Syntax.check_typs read_ctxt
                (map (TFree o #hol) parameters @ parsed))
          end)
      val (parameter_types, checked) = chop (length parameters) checked_all
       val _ = note_generic_types ctxt checked

      (* Keep sort inference shared across the whole signature. Only fresh
         signature variables are flexible; ambient variables remain rigid. *)
      val {fresh, normalize, check_sort, backend, backend_slots} =
        inference_state kind ctxt checked_all
      val named_parameters: typ Symtab.table Unsynchronized.ref =
        Unsynchronized.ref (Symtab.make (map2
          (fn {hol = (name, _), ...}: generic_parameter => fn typ =>
            (name, fresh (Type.sort_of_atyp typ))) parameters parameter_types))

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
          fun inference_parameter (typ as TVar ((name, index), sort)) =
                if Type_Infer.is_param (name, index) then typ
                else Type_Infer.param index (name, sort)
            | inference_parameter typ = typ
        in
          map
            (normalize #>
              Term_Subst.instantiateT names #>
              Term.map_atyps inference_parameter #>
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
            in #types (finish_backend named_context normalize (backend_slots ()) finished) end
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
      val resolved_arguments = #arguments operations specifications arguments
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
      fun finish_argument {typ = NONE, meaning, pos} pending =
            ((NONE, pos), pending)
        | finish_argument {typ = SOME _, meaning, pos} (typ :: pending) =
            ((SOME typ, pos), pending)
        | finish_argument _ [] = raise Fail "missing finished function argument"
      val (actual_arguments, unused) = fold_map finish_argument resolved_arguments finished_types
      val _ = if null unused then () else raise Fail "extra finished function arguments"
      val finished_resolved = map (fn {typ, meaning} =>
        {typ = typ, meaning = finish_meaning finish meaning}) resolved
    in (finish (assemble leading_types finished_resolved),
      {arguments = actual_arguments, identities =
        map (source_identity_name o finish_meaning finish o #meaning) resolved_arguments}) end

  fun resolve_signature_with kind ctxt leading lifetimes rust_types assemble =
    #1 (resolve_signature_operations kind ctxt leading lifetimes rust_types [] [] assemble)

  fun resolve_source_arguments ctxt specifications arguments =
    let
      val result = #2 (resolve_signature_operations Function_Signature ctxt [] [] []
        specifications arguments (K (K [])))
      fun validate ((SOME argument, pos), {sort, ...}: generic_source_parameter) =
            if Sign.of_sort (Proof_Context.theory_of ctxt) (argument, sort) then ()
            else sort_error Function_Signature ctxt "function argument" argument sort pos
        | validate ((NONE, _), _) = ()
      val _ = List.app validate (#arguments result ~~ specifications)
    in result end

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

  fun resolve_impl_target_identity ctxt target =
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
        the_single (resolve_signature_with Impl_Target ctxt [] [] [target] assemble)
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
       if identity_sensitive (the (!meaning)) then !meaning else NONE)
    end

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
            (parameter, canonical_backend_parameter (role_index role) sort))
          normalized_backend
      val template =
        normalize (#typ result)
        |> Term.typ_subst_atomic substitutions
        |> Proof_Context.cert_typ lthy
      val expected_variables =
        map_index (fn (index, sort) => canonical_parameter index sort)
          parameter_sorts @
        map (fn (role, sort) => canonical_backend_parameter (role_index role) sort)
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
       | Fresh entry => install_new base entry lthy)
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

  val mapping_option_configs = Symtab.make [("implicit", ()), ("erase", ())]

  fun add_mapping_option ((name, pos), value) options =
    if Symtab.defined options name then mapping_error ("duplicate option " ^ quote name) pos
    else
      (case value of
         SOME source => Symtab.update (name, source) options
       | NONE => mapping_error ("option " ^ quote name ^ " expects a cartouche payload") pos)

  val parse_mapping_options =
    URust_Option_Parser.command_list unknown_mapping_option mapping_option_configs
      (K (Parse.token Parse.cartouche >> Parser_Lex_Util.cartouche_source))
      add_mapping_option Symtab.empty

  fun declare_manual (options, payload) lthy =
    let
      val (result, reports) = URust_Report_Transaction.capture (fn () =>
        let val roles = case Symtab.lookup options "implicit" of
          NONE => [] | SOME source => read_implicit_roles lthy source
            val erased = case Symtab.lookup options "erase" of
              NONE => [] | SOME source => read_erased_parameters lthy source
        in declare_mapping Manual roles erased payload lthy end)
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
