theory Parser_Impl_Imports
  imports
    Parser_Impl_Item_Scope
    Parser_Impl_Type_Mappings
begin

section\<open> Rust import preparation \<close>

text\<open>
This theory owns the higher import interface: it flattens positioned use trees into explicit leaf
imports, resolves each leaf against the active import scope and the exact item, type and notation
registries, validates the complete batch and either installs it persistently for
\<open>urust_use\<close> or returns a context extended with one immutable block frame.
\<close>

ML\<open>
signature URUST_IMPORTS =
sig
  type leaf
  val flatten: URust_AST.use_item -> leaf list
  val leaf_path: leaf -> string list
  val leaf_alias: leaf -> string * Position.T
  type batch
  type entity =
    {key: string, namespace: URust_Import_Scope.namespace, roles: URust_Import_Scope.role list}
  val item_entities: {registered_function: bool} -> URust_AST.urust_item -> entity list
  datatype target_policy =
      Require_Targets
    | Allow_Unavailable_Targets
    | Declared_Later of entity list
  val validate_batch: URust_AST.use_item list -> batch
  val batch_leaves: batch -> leaf list
  val resolve_batch:
    {persistent: bool, targets: target_policy} -> Proof.context -> batch ->
      URust_Import_Scope.binding list
  val prepare_batch: target_policy -> Proof.context -> batch -> Proof.context
  val prepare_batch_unreported: target_policy -> Proof.context -> batch -> Proof.context
  val conclude_batch: {initial: Proof.context} -> Proof.context -> batch -> unit
  val install: URust_AST.use_item -> local_theory -> local_theory
  val same_scope_item:
    Proof.context -> URust_Import_Scope.namespace -> string ->
      {item: string, pos: Position.T} option
end

(*
  URust_Imports is the only producer of import bindings.

  - flatten expands one use item into its explicit leaves in source order. A leaf retains the
    complete path written for it, including every enclosing group prefix with its single source
    position, the segments written by the leaf itself, its effective alias (the final path segment
    unless renamed; for a grouped `self`, the group's final prefix segment at the `self` token) and
    the smallest meaningful span of its own path.
  - validate_batch is the target-independent phase. It flattens a complete import list and rejects,
    before any registry is consulted, the duplicates that hold for every target (two leaves with
    one alias, one path and the same grouped-self form) and every cycle of the alias dependency
    graph, whose edges lead from a leaf's head segment to the other leaves with that alias.
    Unsupported forms never reach a batch: the parser and the AST constructors reject them.
    Every leaf of a validated batch receives its import identity here, so all preparations of one
    batch bind the same identities.
  - resolve_batch resolves every leaf of a validated batch, used or not, against the batch and the
    supplied context.
    A single-segment target is looked up per namespace: the nearest batch import with that alias
    (never the leaf itself), then the enclosing import scope, and otherwise the exact registry key.
    A multi-segment target resolves its head in the type namespace through the same scopes; an
    imported head must be a generated enum and the remainder exactly one of its variants. Without an
    imported head the complete path is an exact registry key. Imports therefore resolve only through
    import scope and exact registry keys; lexical locals, arguments, HOL fixes and unresolved Frees
    are never consulted. Dependencies between batch imports may occur in any source order; cyclic
    dependencies are rejected on every participating import path, and duplicate aliases in one
    namespace are rejected at the later alias. A grouped `self` imports only the type identity of a
    generated enum. Exact keys obtain their namespace memberships from item origin and shape,
    type mappings and literal/call notation registrations; field-only notations and keys without
    any supported item are positioned rejections. Persistent batches additionally reject an alias
    that collides with a same-scope generated item or registered type. Bindings carry the identity
    of their validated leaf. Semantic reports are deferred only after the complete batch validates.
    Require_Targets rejects a target that is absent from the context. Allow_Unavailable_Targets
    instead binds such a leaf, and every leaf depending on it, as an unavailable binding whose uses
    reject without fallback; a target that exists but cannot be imported still rejects.
    Declared_Later entities is namespace precise: a target entity that is absent from the context
    but listed among the entities that will be declared binds an unavailable binding in that
    namespace only, entities that exist keep resolving, and a target that neither exists nor is
    listed is unknown, as under Require_Targets. Duplicates among available bindings are rejected
    in every policy.
  - prepare_batch is the batch preparation operation shared by real blocks, implicit command bodies
    and composition: it returns the supplied context extended with one immutable frame, or the
    context itself for an empty batch. Blocks, bodies and persistent imports require targets; a
    composer that re-prepares one validated batch for each declaration passes the item_entities
    of the items still to be declared as Declared_Later (or, without that knowledge, allows
    unavailable targets) and requires every target at the end. prepare_batch_unreported prepares
    the same frame without semantic reports; such a composer uses it for every preparation of the
    batch except the one that reports it. conclude_batch is that composer's final step: it
    resolves the batch with Require_Targets and reports it, and rejects an import whose alias
    shares a namespace with an item declared alongside the batch, that is, present in the final
    context but not in the initial one, as Rust rejects an import and an item of one name in one
    scope. install validates and installs one use item as persistent local-theory declarations,
    capturing the canonical keys at installation.
  - same_scope_item finds the generated function or unit/tuple constructor (value namespace) or the
    Rust type (type namespace) whose single-segment key is a given name.
  - item_entities lists the keys, namespaces and roles that one item will contribute to the
    registries once declared, as registry_member derives them from the installed registrations:
    a datatype its type, unit/tuple constructors and enum variants; a function its call key when
    it is registered. Other items contribute none.
*)
structure URust_Imports :> URUST_IMPORTS =
struct
  open URust_AST
  structure S = URust_Import_Scope
  structure I = URust_Item_Scope
  structure Navigation = Micro_Rust_Semantic_Navigation

  type leaf =
    {path: (string * Position.T) list,
     written: (string * Position.T) list,
     alias: string * Position.T,
     self_pos: Position.T option,
     span: Position.T}

  fun leaf_path ({path, ...}: leaf) = map #1 path
  fun leaf_alias ({alias, ...}: leaf) = alias

  fun import_error message pos =
    error ("uRust import: " ^ message ^ Position.here pos)

  fun segments_span [] = Position.none
    | segments_span [(_, pos)] = pos
    | segments_span ((_, first) :: rest) =
        Position.range_position
          (first, Parser_Lex_Util.exclusive_end (#2 (List.last rest)))

  fun flatten_tree prefix (Use_Path (segments, alias, _)) =
        [{path = prefix @ segments,
          written = segments,
          alias = the_default (List.last segments) alias,
          self_pos = NONE,
          span = segments_span segments}]
    | flatten_tree prefix (Use_Self (self_pos, alias, _)) =
        [{path = prefix,
          written = [],
          alias = the_default (#1 (List.last prefix), self_pos) alias,
          self_pos = SOME self_pos,
          span = self_pos}]
    | flatten_tree prefix (Use_Group (group_prefix, members, _)) =
        maps (flatten_tree (prefix @ group_prefix)) members

  fun flatten item = flatten_tree [] (use_item_tree item)

  (* An unavailable member stands for an entity that is declared later. *)
  type member = {key: string, roles: S.role list, available: bool}
  type resolved = {type_member: member option, value_member: member option}

  fun member_of S.Type_Namespace ({type_member, ...}: resolved) = type_member
    | member_of S.Value_Namespace ({value_member, ...}: resolved) = value_member

  fun generated_struct ctxt key =
    (case I.lookup_constructor ctxt key of
       SOME entry => I.constructor_origin entry = I.Struct_Constructor
     | NONE => false)

  fun variant_entry ctxt key =
    (case I.lookup_constructor ctxt key of
       SOME entry =>
         if I.constructor_origin entry = I.Enum_Variant then SOME entry else NONE
     | NONE => NONE)

  fun registry_member ctxt key : resolved =
    let
      val type_roles =
        (case I.lookup_type ctxt key of
           SOME _ => [if generated_struct ctxt key then S.Generated_Struct else S.Generated_Enum]
         | NONE => []) @
        (if is_some (URust_Type_Mappings.lookup ctxt key) then [S.Mapped_Type] else []) @
        (if is_some (variant_entry ctxt key) then [S.Enum_Variant] else [])
      val value_roles =
        (if is_some (I.lookup_function ctxt key) then [S.Generated_Function] else []) @
        (case I.lookup_constructor ctxt key of
           SOME entry =>
             if I.constructor_shape entry = I.Named_Constructor then []
             else [S.Generated_Constructor]
         | NONE => []) @
        (if null (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral key) then []
         else [S.Literal_Notation]) @
        (if null (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction key) then []
         else [S.Call_Notation])
      fun member [] = NONE
        | member roles = SOME {key = key, roles = roles, available = true}
    in {type_member = member type_roles, value_member = member value_roles} end

  type entity = {key: string, namespace: S.namespace, roles: S.role list}

  fun item_entities {registered_function} item =
    let
      fun entity namespace roles key = {key = key, namespace = namespace, roles = roles}: entity
      fun constructor_value _ (Named_Shape _) = []
        | constructor_value key _ = [entity S.Value_Namespace [S.Generated_Constructor] key]
      fun datatype_entities (Struct_Item (name, _, shape, _)) =
            entity S.Type_Namespace [S.Generated_Struct, S.Mapped_Type] name ::
              constructor_value name shape
        | datatype_entities (Enum_Item (name, _, variants, _)) =
            entity S.Type_Namespace [S.Generated_Enum, S.Mapped_Type] name ::
              maps
                (fn Datatype_Variant (variant, _, shape) =>
                  let val key = name ^ "::" ^ variant
                  in
                    entity S.Type_Namespace [S.Enum_Variant] key :: constructor_value key shape
                  end)
                variants
        | datatype_entities (Datatype_Header (_, _, _, item)) = datatype_entities item
    in
      (case item of
         Datatype_Item item => datatype_entities item
       | Function_Item_Node function =>
           if registered_function
           then [entity S.Value_Namespace [S.Generated_Function] (#1 (function_name function))]
           else []
       | _ => [])
    end

  datatype target_policy =
      Require_Targets
    | Allow_Unavailable_Targets
    | Declared_Later of entity list

  (* The registry members of a key, completed under Declared_Later by an unavailable member for
     each namespace whose entity a later declaration introduces. *)
  fun known_member policy ctxt key : resolved =
    let
      val registered = registry_member ctxt key
      fun declared namespace =
        (case policy of
           Declared_Later entities =>
             Option.map
               (fn ({roles, ...}: entity) => {key = key, roles = roles, available = false})
               (find_first
                 (fn entity => #key entity = key andalso #namespace entity = namespace) entities)
         | _ => NONE)
      fun slot _ (SOME member) = SOME member
        | slot namespace NONE = declared namespace
    in
      {type_member = slot S.Type_Namespace (#type_member registered),
       value_member = slot S.Value_Namespace (#value_member registered)}
    end

  (* Raised while resolving under Allow_Unavailable_Targets for a target that may still appear. *)
  exception Unavailable_Target

  fun require_target policy ctxt key pos (resolved as {type_member, value_member}: resolved) =
    if is_some type_member orelse is_some value_member then resolved
    else if not (null (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NField key)) then
      import_error
        ("field notation " ^ quote key ^
          " is outside the import surface; field-only lens aliases are not importable") pos
    else
      (case policy of
         Allow_Unavailable_Targets => raise Unavailable_Target
       | _ =>
          import_error
            ("unknown import target " ^ quote key ^
              "; imports name exact generated items, Rust type mappings and literal or call " ^
              "notations")
            pos)

  fun same_scope_item ctxt S.Value_Namespace name =
        (case I.lookup_function ctxt name of
           SOME entry => SOME {item = "generated Rust function", pos = I.function_position entry}
         | NONE =>
             (case I.lookup_constructor ctxt name of
                SOME entry =>
                  if I.constructor_shape entry = I.Named_Constructor then NONE
                  else SOME {item = "generated Rust constructor", pos = I.constructor_position entry}
              | NONE => NONE))
    | same_scope_item ctxt S.Type_Namespace name =
        (case I.lookup_type ctxt name of
           SOME entry => SOME {item = "generated Rust item", pos = I.type_position entry}
         | NONE =>
             Option.map
               (fn entry =>
                 {item = "Rust type", pos = URust_Type_Mappings.entry_declaration_position entry})
               (URust_Type_Mappings.lookup ctxt name))

  type batch = (leaf * serial) list

  fun batch_leaves (batch: batch) = map #1 batch

  fun head_name ({path, ...}: leaf) = (case path of (name, _) :: _ => SOME name | [] => NONE)

  fun cycle_error (leaves: leaf list) participants =
    let
      val ordered = sort int_ord participants
      val described =
        map (fn index =>
          space_implode "::" (leaf_path (nth leaves index)) ^ " as " ^
            #1 (#alias (nth leaves index))) ordered
    in
      error
        ("uRust import: cyclic imports: " ^ commas_quote described ^
          Position.here_list (map (fn index => #span (nth leaves index)) ordered))
    end

  fun validate_batch items =
    let
      val leaves = maps flatten items
      val indexed = map_index I leaves
      fun same_form (left: leaf, right: leaf) =
        #1 (#alias left) = #1 (#alias right) andalso leaf_path left = leaf_path right andalso
          is_some (#self_pos left) = is_some (#self_pos right)
      val _ =
        fold
          (fn (index, leaf) => fn () =>
            (case find_first (fn (earlier, other) => earlier < index andalso same_form (other, leaf))
                indexed of
               SOME (_, earlier) =>
                 error
                   ("uRust import: duplicate import " ^ quote (#1 (#alias leaf)) ^
                     Position.here (#2 (#alias leaf)) ^
                     "\nThe earlier import is here" ^ Position.here (#2 (#alias earlier)))
             | NONE => ()))
          indexed ()
      fun dependencies (index, leaf) =
        (case head_name leaf of
           SOME name =>
             indexed
             |> filter (fn (other, candidate) => other <> index andalso #1 (#alias candidate) = name)
             |> map #1
         | NONE => [])
      val graph = map dependencies indexed
      val states = Array.array (length leaves, 0)
      fun visit stack index =
        (case Array.sub (states, index) of
           2 => ()
         | 1 => cycle_error leaves (index :: take_prefix (fn other => other <> index) stack)
         | _ =>
             (Array.update (states, index, 1);
              List.app (visit (index :: stack)) (nth graph index);
              Array.update (states, index, 2)))
      val _ = List.app (visit []) (0 upto length leaves - 1)
    in map (fn leaf => (leaf, serial ())) leaves end

  datatype outcome = Available of resolved | Unavailable
  datatype state = Unresolved | Active | Done of outcome

  fun binding_member (binding: S.binding) =
    {key = #key binding, roles = #roles binding, available = #available binding}

  fun resolve_leaves policy ctxt (leaves: leaf list) =
    let
      val count = length leaves
      val states = Array.array (count, Unresolved)
      val indexed = map_index I leaves

      fun unavailable_or_error pos (binding: S.binding) =
        (case policy of
           Allow_Unavailable_Targets => raise Unavailable_Target
         | _ => S.require_available pos binding)

      fun resolve index =
        (case Array.sub (states, index) of
           Done outcome => outcome
         | Active => import_error "internal import dependency cycle" (#span (nth leaves index))
         | Unresolved =>
             let
               val _ = Array.update (states, index, Active)
               val outcome =
                 Available (resolve_leaf index)
                   handle Unavailable_Target => Unavailable
               val _ = Array.update (states, index, Done outcome)
             in outcome end)

      and scope_lookup exclude pos namespace name =
        let
          val candidates =
            indexed
            |> filter (fn (index, leaf) => index <> exclude andalso #1 (#alias leaf) = name)
            |> map_filter (fn (index, _) =>
                 (case resolve index of
                    Unavailable => raise Unavailable_Target
                  | Available resolved => Option.map (pair index) (member_of namespace resolved)))
        in
          (case candidates of
             [] =>
               (case S.lookup ctxt namespace name of
                  NONE => NONE
                | SOME binding =>
                    (if #available binding then () else unavailable_or_error pos binding;
                     S.check_merged_collision ctxt binding (same_scope_item ctxt namespace name);
                     SOME (binding_member binding)))
           | [(_, member)] => SOME member
           | (earlier, _) :: (later, _) :: _ =>
               error
                 ("uRust import: duplicate " ^ S.namespace_name namespace ^ " import " ^
                   quote name ^ Position.here (#2 (#alias (nth leaves later))) ^
                   "\nThe earlier import is here" ^ Position.here (#2 (#alias (nth leaves earlier)))))
        end

      and resolve_path index (leaf: leaf) path =
        (case path of
           [] => import_error "internal empty import path" (#span leaf)
         | [(name, pos)] =>
             let
               val imported_type = scope_lookup index pos S.Type_Namespace name
               val imported_value = scope_lookup index pos S.Value_Namespace name
               val registered = known_member policy ctxt name
               val resolved =
                 {type_member =
                    (case imported_type of
                       SOME member => SOME member
                     | NONE => #type_member registered),
                  value_member =
                    (case imported_value of
                       SOME member => SOME member
                     | NONE => #value_member registered)}
             in require_target policy ctxt name pos resolved end
         | (head, head_pos) :: rest =>
             (case scope_lookup index head_pos S.Type_Namespace head of
                SOME {key = owner, roles, available} =>
                  if not (member (op =) roles S.Generated_Enum) then
                    import_error
                      ("imported " ^ quote head ^ " (" ^ quote owner ^
                        ") is not a generated enum and cannot qualify a use path") head_pos
                  else
                    (case rest of
                       [(variant, variant_pos)] =>
                         let
                           val key = owner ^ "::" ^ variant
                           fun not_a_variant () =
                             import_error
                               (quote variant ^ " is not a variant of enum " ^ quote owner)
                               variant_pos
                         in
                           if available then
                             (case variant_entry ctxt key of
                                SOME entry =>
                                  if I.constructor_rust_type entry = owner
                                  then registry_member ctxt key
                                  else not_a_variant ()
                              | NONE => not_a_variant ())
                           else
                             (* An enum declared later qualifies exactly its declared variants. *)
                             (case known_member policy ctxt key of
                                {type_member = NONE, value_member = NONE} => not_a_variant ()
                              | declared => declared)
                         end
                     | _ :: (_, nested_pos) :: _ =>
                         import_error "enum variants have no nested importable items" nested_pos
                     | [] => import_error "internal empty variant path" head_pos)
              | NONE =>
                  let val key = space_implode "::" (map #1 path) in
                    require_target policy ctxt key (#span leaf) (known_member policy ctxt key)
                  end))

      and resolve_leaf index =
        let
          val leaf = nth leaves index
        in
          (case #self_pos leaf of
             NONE => resolve_path index leaf (#path leaf)
           | SOME self_pos =>
               (case #type_member (resolve_path index leaf (#path leaf)) of
                  SOME (found as {roles, ...}) =>
                    if member (op =) roles S.Generated_Enum
                    then {type_member = SOME found, value_member = NONE}
                    else
                      import_error
                        ("grouped `self` requires a generated enum; " ^
                          quote (#key found) ^ " is not one") self_pos
                | NONE =>
                    import_error
                      ("grouped `self` requires a generated enum; " ^
                        quote (space_implode "::" (leaf_path leaf)) ^ " has no type identity")
                      self_pos))
        end
    in map resolve (0 upto count - 1) end

  fun leaf_bindings ((leaf: leaf, identity), outcome) =
    let
      val (alias, alias_pos) = #alias leaf
      fun make namespace key roles available =
        {alias = alias, alias_pos = alias_pos, namespace = namespace, key = key, roles = roles,
         available = available, identity = identity, declaration_pos = #span leaf}: S.binding
    in
      (case outcome of
         Available resolved =>
           map_filter
             (fn namespace =>
               Option.map
                 (fn {key, roles, available} =>
                   make namespace key (if available then roles else []) available)
                 (member_of namespace resolved))
             [S.Type_Namespace, S.Value_Namespace]
       | Unavailable =>
           map (fn namespace => make namespace (space_implode "::" (leaf_path leaf)) [] false)
             [S.Type_Namespace, S.Value_Namespace])
    end

  fun check_scope_items lookup_item (binding: S.binding) =
    (case lookup_item (#namespace binding) (#alias binding) of
       SOME {item, pos} =>
         error
           ("uRust import: " ^ S.namespace_name (#namespace binding) ^ " import " ^
             quote (#alias binding) ^ " collides with the same-scope " ^ item ^ " " ^
             quote (#alias binding) ^ Position.here (#alias_pos binding) ^
             "\nThe item is here" ^ Position.here pos)
     | NONE => ())

  (* Reports are issued once per source position, because group prefixes are shared by leaves. *)
  fun report_once seen pos action =
    if not (Position.is_reported pos) then ()
    else
      let val key = Position.properties_of pos in
        if member (op =) (!seen) key then ()
        else (seen := key :: !seen; action ())
      end

  fun report_target ctxt pos (member: member) =
    let
      val key = #key member
      fun role S.Generated_Struct =
            Option.app
              (fn entry =>
                (Navigation.defer_report ctxt pos Markup.keyword3;
                 I.report_type_reference ctxt pos entry))
              (I.lookup_type ctxt key)
        | role S.Generated_Enum = role S.Generated_Struct
        | role S.Mapped_Type =
            Option.app (URust_Type_Mappings.report_reference ctxt pos key)
              (URust_Type_Mappings.lookup ctxt key)
        | role S.Enum_Variant =
            Option.app
              (fn entry =>
                (Navigation.defer_report ctxt pos Markup.keyword3;
                 I.report_constructor_reference ctxt pos entry))
              (variant_entry ctxt key)
        | role S.Generated_Constructor =
            Option.app
              (fn entry =>
                if I.constructor_origin entry = I.Enum_Variant then ()
                else
                  (Navigation.defer_report ctxt pos Markup.keyword3;
                   I.report_constructor_reference ctxt pos entry))
              (I.lookup_constructor ctxt key)
        | role S.Generated_Function =
            Option.app (I.defer_function_reference ctxt pos) (I.lookup_function ctxt key)
        | role S.Literal_Notation = notations Micro_Rust_Names.NLiteral
        | role S.Call_Notation = notations Micro_Rust_Names.NFunction
      and notations kind =
        List.app
          (fn ({reg_pos, serial, ...}: Micro_Rust_Names.entry) =>
            Navigation.defer_report ctxt pos
              (Position.make_entity_markup {def = false} serial Micro_Rust_Names.notationN
                (key, reg_pos)))
          (Micro_Rust_Names.lookups ctxt kind key)
      val roles = #roles member
      val ordered =
        filter (fn role => role = S.Mapped_Type) roles @
        filter (fn role => role <> S.Mapped_Type) roles
    in List.app role ordered end

  (* A path head resolved through an import references that import; the nearest qualifier of a
     generated enum references the enum. Other qualifiers are syntax-only module-like segments. *)
  fun report_qualifiers ctxt batch_ctxt seen qualifiers =
    let
      val head_import =
        (case qualifiers of
           (head, _) :: _ =>
             (case S.lookup batch_ctxt S.Type_Namespace head of
                SOME binding =>
                  if S.has_role binding S.Generated_Enum then SOME binding else NONE
              | NONE => NONE)
         | [] => NONE)
      val owner =
        (case head_import of
           SOME binding =>
             space_implode "::" (#key binding :: map #1 (drop 1 qualifiers))
         | NONE => space_implode "::" (map #1 qualifiers))
      val last_index = length qualifiers - 1
      fun report (index, (_, pos)) =
        report_once seen pos (fn () =>
          let
            val _ =
              if index = last_index then
                Option.app
                  (fn entry =>
                    (Navigation.defer_report ctxt pos Markup.keyword3;
                     I.report_type_reference ctxt pos entry))
                  (I.lookup_type ctxt owner)
              else ()
          in
            (case (index, head_import) of
               (0, SOME binding) => S.defer_use_reference ctxt pos binding
             | _ =>
                 if index = last_index andalso is_some (I.lookup_type ctxt owner) then ()
                 else S.defer_declaration_report ctxt pos Markup.typing (SOME "use path qualifier"))
          end)
    in List.app report (map_index I qualifiers) end

  fun report_leaf ctxt batch_ctxt seen (leaf: leaf, resolved: resolved) =
    let
      val qualifiers =
        (case #self_pos leaf of
           SOME _ => #path leaf
         | NONE => #1 (split_last (#path leaf)))
      val _ = report_qualifiers ctxt batch_ctxt seen qualifiers
      val target_pos =
        (case #self_pos leaf of
           SOME self_pos => self_pos
         | NONE => #2 (List.last (#path leaf)))
      val _ =
        (case #self_pos leaf of
           SOME self_pos =>
             (S.defer_declaration_report ctxt self_pos Markup.keyword1 NONE;
              S.defer_declaration_report ctxt self_pos Markup.typing
                (SOME "grouped self import of the enum type"))
         | NONE => ())
      val _ =
        if #2 (#alias leaf) = target_pos then ()
        else
          S.defer_declaration_report ctxt target_pos Markup.typing
            (SOME ("use target " ^ quote (space_implode "::" (leaf_path leaf))))
    in
      List.app (report_target ctxt target_pos)
        (filter #available (map_filter I [#type_member resolved, #value_member resolved]))
    end

  fun resolve report {persistent, targets} ctxt (batch: batch) =
    let
      val leaves = batch_leaves batch
      val outcomes = resolve_leaves targets ctxt leaves
      val bindings = maps leaf_bindings (batch ~~ outcomes)
      val _ = S.check_batch bindings
      val _ =
        if persistent then
          (S.check_persistent_duplicates ctxt bindings;
           List.app (check_scope_items (same_scope_item ctxt)) bindings)
        else ()
      val _ =
        if report then
          let
            val batch_ctxt = S.push_frame bindings ctxt
            val seen = Unsynchronized.ref ([]: Properties.T list)
            val _ = S.report_alias_definitions ctxt bindings
          in
            List.app
              (fn (leaf, Available resolved) => report_leaf ctxt batch_ctxt seen (leaf, resolved)
                | (_, Unavailable) => ())
              (leaves ~~ outcomes)
          end
        else ()
    in bindings end

  val resolve_batch = resolve true

  fun gen_prepare_batch _ _ ctxt [] = ctxt
    | gen_prepare_batch report targets ctxt batch =
        S.push_frame (resolve report {persistent = false, targets = targets} ctxt batch) ctxt

  val prepare_batch = gen_prepare_batch true
  val prepare_batch_unreported = gen_prepare_batch false

  fun conclude_batch {initial} ctxt batch =
    let
      val bindings = resolve_batch {persistent = false, targets = Require_Targets} ctxt batch
      fun declared_alongside namespace name =
        (case same_scope_item ctxt namespace name of
           SOME found =>
             if is_none (same_scope_item initial namespace name) then SOME found else NONE
         | NONE => NONE)
    in List.app (check_scope_items declared_alongside) bindings end

  fun install item lthy =
    S.declare_persistent
      (resolve_batch {persistent = true, targets = Require_Targets} lthy (validate_batch [item]))
      lthy
end
\<close>

end
