theory Parser_Impl_Import_Scope
  imports
    Parser_Impl_AST
    Shallow_Micro_Rust.Semantic_Navigation
begin

section\<open> Rust import scopes \<close>

text\<open>
This theory owns the scope model of Rust \<open>use\<close> imports below the item and type registries.
A binding maps one alias in one Rust namespace to a canonical exact source key. It records the
namespace memberships of that key, but no terms, types or backends: those remain owned by their
registries and are reached by delegation through the canonical key. Persistent bindings are native
context data installed by local-theory declarations; block bindings live only in derived proof
contexts.
\<close>

ML\<open>
signature URUST_IMPORT_SCOPE =
sig
  datatype namespace = Type_Namespace | Value_Namespace
  datatype role =
      Mapped_Type
    | Generated_Struct
    | Generated_Enum
    | Enum_Variant
    | Generated_Function
    | Generated_Constructor
    | Literal_Notation
    | Call_Notation
  type binding =
    {alias: string,
     alias_pos: Position.T,
     namespace: namespace,
     key: string,
     roles: role list,
     available: bool,
     identity: serial,
     declaration_pos: Position.T}

  val key_segments: string -> string list
  val namespace_name: namespace -> string
  val role_name: role -> string
  val role_namespace: role -> namespace
  val has_role: binding -> role -> bool
  val describe: binding -> string
  val require_available: Position.T -> binding -> unit
  val unavailable_use_error: Position.T -> binding -> string -> 'a

  val lookup: Proof.context -> namespace -> string -> binding option
  val lookup_persistent: Proof.context -> namespace -> string -> binding option
  val dump_persistent: Proof.context -> binding list
  val frame_depth: Proof.context -> int
  val transfer_frames: Proof.context -> Proof.context -> Proof.context

  val check_batch: binding list -> unit
  val push_frame: binding list -> Proof.context -> Proof.context
  val add_pending_roles: (binding * role list) list -> Proof.context -> Proof.context
  val pending_roles: Proof.context -> binding -> role list
  val check_persistent_duplicates: Proof.context -> binding list -> unit
  val declare_persistent: binding list -> local_theory -> local_theory
  val merge_persistent: binding list * binding list -> binding list
  val check_item_collision:
    Proof.context -> {item: string, name: string, pos: Position.T} -> namespace -> unit
  val check_merged_collision:
    Proof.context -> binding -> {item: string, pos: Position.T} option -> unit

  type reports
  val defer_declaration_report:
    Proof.context -> Position.T -> Markup.T -> string option -> unit
  val defer_use_reference: Proof.context -> Position.T -> binding -> unit
  val report_alias_definitions: Proof.context -> binding list -> unit
  val capture_reports: (unit -> 'a) -> 'a * reports
  val replay_use_reports: Proof.context -> reports -> unit
end

(*
  URust_Import_Scope is the lower import owner. It depends only on the AST and semantic navigation,
  so the type and item registries may consult it without a dependency cycle. The higher
  URust_Imports owner flattens and resolves use trees into bindings and is the only producer of
  bindings.

  - key_segments splits a canonical exact key at its `::` separators; keys never contain generic
    arguments because use paths cannot.
  - namespace distinguishes Rust's type and value namespaces. Notation roles are not namespaces: a
    literal and a call registration both occupy the value namespace. role records one exported
    capability of the canonical key; role_namespace gives the namespace it belongs to.
  - binding records one alias in one namespace: its declaration position, the canonical exact source
    key captured at installation, the key's roles in that namespace, the import identity shared by
    all namespace bindings of one imported leaf, and the leaf's declaration span. An unavailable
    binding (available = false) stands for a leaf whose target does not exist yet in the supplied
    context. It has no roles, and every consumer that finds it rejects the occurrence through
    require_available, without fallback. A leaf whose namespaces are not known yet occupies both
    namespaces with its written path as key; one whose later declaration is known occupies exactly
    the namespaces of that declaration, with its canonical key.
  - lookup returns the nearest binding in the requested namespace: block frames from innermost to
    outermost, then the persistent bindings of the context. lookup_persistent consults only the
    latter. frame_depth counts the active block frames. transfer_frames source target gives target
    the block frames of source: a read-only replay that runs in a context produced by a
    declaration backend resolves source names with the import scope of the declaration context.
  - check_batch rejects two available bindings with the same alias and namespace, even with
    identical targets; the later binding is reported with the earlier position. Unavailable
    bindings are not compared, because their namespaces are not known yet. push_frame returns a
    derived context with one immutable block frame, in which an available binding takes its
    namespace from an unavailable one; frames are proof data and never enter theory data.
    add_pending_roles records, beside a frame, the roles that a declaration still to be made adds
    to the target of an available binding in its namespace; pending_roles returns them (none for
    persistent bindings). unavailable_use_error rejects a use that needs such a role, naming the
    use, without fallback.
  - check_persistent_duplicates applies the same rule against the active persistent bindings.
    declare_persistent installs bindings through a non-pervasive local-theory declaration, so theory
    imports inherit them and locales, experiments and interpretations use native confinement and
    morphism replay. Replaying one declaration is idempotent. merge_persistent is the theory-merge
    rule: the same identity or the same canonical target keeps the lower identity, and different
    targets for one alias and namespace are a positioned conflict.
  - check_item_collision rejects a same-scope Rust item whose single-segment name equals an active
    persistent alias in the given namespace. Registries call it so that both declaration orders
    are diagnosed. check_merged_collision lets a resolver reject a persistent binding that a
    theory merge or interpretation placed beside a same-named item it has found.
  - Declaration reports (alias definitions and use-item tooltips) are deferred semantic navigation
    events, so they join the enclosing navigation transaction in emission order and are dropped
    with it. Use references at alias occurrences are queued while capture_reports is active, because
    typed dispatch adds the backend references of the same occurrence later. replay_use_reports
    hands them to deferred semantic navigation after the elaboration's other queues, so they follow
    every target reached through the alias, also inside an enclosing transaction, and the import
    declaration is the final source navigation target. Without an active capture, a use reference
    is deferred to semantic navigation at once.
*)
structure URust_Import_Scope :> URUST_IMPORT_SCOPE =
struct
  structure Navigation = Micro_Rust_Semantic_Navigation

  datatype namespace = Type_Namespace | Value_Namespace
  datatype role =
      Mapped_Type
    | Generated_Struct
    | Generated_Enum
    | Enum_Variant
    | Generated_Function
    | Generated_Constructor
    | Literal_Notation
    | Call_Notation

  type binding =
    {alias: string,
     alias_pos: Position.T,
     namespace: namespace,
     key: string,
     roles: role list,
     available: bool,
     identity: serial,
     declaration_pos: Position.T}

  val importN = "urust_import"

  fun key_segments key =
    let
      fun split input =
        let val (segment, rest) = Substring.position "::" input in
          if Substring.isEmpty rest then [Substring.string segment]
          else Substring.string segment :: split (Substring.triml 2 rest)
        end
    in split (Substring.full key) end

  fun namespace_name Type_Namespace = "type"
    | namespace_name Value_Namespace = "value"

  fun role_name Mapped_Type = "Rust type mapping"
    | role_name Generated_Struct = "generated struct"
    | role_name Generated_Enum = "generated enum"
    | role_name Enum_Variant = "enum variant"
    | role_name Generated_Function = "generated function"
    | role_name Generated_Constructor = "generated constructor"
    | role_name Literal_Notation = "literal notation"
    | role_name Call_Notation = "call notation"

  fun role_namespace Generated_Function = Value_Namespace
    | role_namespace Generated_Constructor = Value_Namespace
    | role_namespace Literal_Notation = Value_Namespace
    | role_namespace Call_Notation = Value_Namespace
    | role_namespace _ = Type_Namespace

  fun has_role ({roles, ...}: binding) role = member (op =) roles role

  fun describe ({alias, key, namespace, roles, available, ...}: binding) =
    if available then
      "Rust import " ^ quote alias ^ " of " ^ quote key ^ " (" ^
        namespace_name namespace ^ " namespace: " ^ commas (map role_name roles) ^ ")"
    else
      "Rust import " ^ quote alias ^ " of " ^ quote key ^ " (target not yet available)"

  fun require_available pos ({alias, key, available, ...}: binding) =
    if available then ()
    else
      error
        ("uRust import: import target " ^ quote key ^ " of " ^ quote alias ^
          " is not yet available" ^ Position.here pos)

  fun unavailable_use_error pos ({alias, key, ...}: binding) use =
    error
      ("uRust import: import target " ^ quote key ^ " of " ^ quote alias ^
        " is not yet available as " ^ use ^ Position.here pos)

  fun table_key namespace alias = namespace_name namespace ^ "\000" ^ alias

  fun same_target (left: binding, right: binding) =
    #namespace left = #namespace right andalso #alias left = #alias right andalso
      #key left = #key right andalso #roles left = #roles right andalso
      #available left = #available right

  fun conflict_error (left: binding, right: binding) =
    let
      val (first, second) =
        if #identity left <= #identity right then (left, right) else (right, left)
    in
      error
        ("uRust import: conflicting " ^ namespace_name (#namespace first) ^
          " imports for " ^ quote (#alias first) ^ ": " ^ quote (#key first) ^
          Position.here (#alias_pos first) ^ " versus " ^ quote (#key second) ^
          Position.here (#alias_pos second))
    end

  fun join_binding (left: binding, right: binding) =
    if #identity left = #identity right orelse same_target (left, right)
    then if #identity left <= #identity right then left else right
    else conflict_error (left, right)

  fun insert_binding (binding: binding) table =
    let val key = table_key (#namespace binding) (#alias binding) in
      (case Symtab.lookup table key of
         NONE => Symtab.update (key, binding) table
       | SOME existing => Symtab.update (key, join_binding (existing, binding)) table)
    end

  structure Persistent = Generic_Data
  (
    type T = binding Symtab.table
    val empty = Symtab.empty
    fun merge (left, right) = Symtab.join (K join_binding) (left, right)
  )

  (* Innermost frame first. Proof data keeps derived block scopes out of every theory. *)
  structure Frames = Proof_Data
  (
    type T = binding Symtab.table list
    fun init _ = []
  )

  fun lookup_persistent ctxt namespace alias =
    Symtab.lookup (Persistent.get (Context.Proof ctxt)) (table_key namespace alias)

  fun lookup ctxt namespace alias =
    (case get_first (fn frame => Symtab.lookup frame (table_key namespace alias))
        (Frames.get ctxt) of
       SOME binding => SOME binding
     | NONE => lookup_persistent ctxt namespace alias)

  fun dump_persistent ctxt =
    Persistent.get (Context.Proof ctxt) |> Symtab.dest |> map snd

  fun frame_depth ctxt = length (Frames.get ctxt)

  fun transfer_frames source = Frames.put (Frames.get source)

  fun duplicate_error (earlier: binding) (later: binding) =
    error
      ("uRust import: duplicate " ^ namespace_name (#namespace later) ^ " import " ^
        quote (#alias later) ^ Position.here (#alias_pos later) ^
        "\nThe earlier import is here" ^ Position.here (#alias_pos earlier))

  fun check_batch bindings =
    ignore
      (fold
        (fn binding => fn seen =>
          let val key = table_key (#namespace binding) (#alias binding) in
            (case Symtab.lookup seen key of
               NONE => Symtab.update (key, binding) seen
             | SOME earlier => duplicate_error earlier binding)
          end)
        (filter #available bindings) Symtab.empty)

  (* Keyed by import identity and namespace; derived like frames and never stored in theories. *)
  structure Pending = Proof_Data
  (
    type T = role list Symtab.table
    fun init _ = Symtab.empty
  )

  fun pending_key ({identity, namespace, ...}: binding) =
    string_of_int identity ^ "\000" ^ namespace_name namespace

  fun add_pending_roles entries =
    Pending.map (fold (fn (binding, roles) => Symtab.update (pending_key binding, roles)) entries)

  fun pending_roles ctxt binding =
    the_default [] (Symtab.lookup (Pending.get ctxt) (pending_key binding))

  fun push_frame bindings ctxt =
    let
      val _ = check_batch bindings
      fun add (binding: binding) frame =
        let val key = table_key (#namespace binding) (#alias binding) in
          (case Symtab.lookup frame key of
             SOME (existing: binding) =>
               if #available existing orelse not (#available binding) then frame
               else Symtab.update (key, binding) frame
           | NONE => Symtab.update (key, binding) frame)
        end
    in Frames.map (cons (fold add bindings Symtab.empty)) ctxt end

  fun check_persistent_duplicates ctxt bindings =
    List.app
      (fn binding =>
        (case lookup_persistent ctxt (#namespace binding) (#alias binding) of
           SOME earlier => duplicate_error earlier binding
         | NONE => ()))
      bindings

  fun declare_persistent bindings lthy =
    let
      val _ =
        if forall #available bindings then ()
        else error "uRust import: internal unavailable persistent import"
      val _ = check_batch bindings
      val _ = check_persistent_duplicates lthy bindings
      val pos =
        (case bindings of
           binding :: _ => #declaration_pos binding
         | [] => Position.none)
    in
      Local_Theory.declaration {pervasive = false, syntax = false, pos = pos}
        (fn _ => Persistent.map (fold insert_binding bindings)) lthy
    end

  fun merge_persistent (left, right) =
    Symtab.join (K join_binding)
      (fold insert_binding left Symtab.empty, fold insert_binding right Symtab.empty)
    |> Symtab.dest |> map snd

  fun collision_error {item, name, pos} (binding: binding) =
    error
      ("uRust import: " ^ item ^ " " ^ quote name ^ " collides with the " ^
        namespace_name (#namespace binding) ^ " import of " ^ quote (#key binding) ^
        " in the same scope" ^ Position.here pos ^
        "\nThe import is here" ^ Position.here (#alias_pos binding))

  fun check_item_collision ctxt {item, name, pos} namespace =
    (case lookup_persistent ctxt namespace name of
       NONE => ()
     | SOME binding => collision_error {item = item, name = name, pos = pos} binding)

  (* Declaration commands reject same-scope collisions in both orders, but independent theories
     or a locale interpretation may still merge a persistent alias with a same-named item. The
     resolver reports such a pair instead of letting the import shadow the item. *)
  fun check_merged_collision ctxt (binding: binding) item =
    (case (item, lookup_persistent ctxt (#namespace binding) (#alias binding)) of
       (SOME {item, pos}, SOME persistent) =>
         if #identity persistent = #identity binding
         then collision_error {item = item, name = #alias binding, pos = pos} binding
         else ()
     | _ => ())

  datatype report = Use_Report of Position.T * Markup.T

  type reports = report list

  val active_reports: report list Unsynchronized.ref Thread_Data.var = Thread_Data.var ()

  fun defer_declaration_report ctxt pos markup NONE = Navigation.defer_report ctxt pos markup
    | defer_declaration_report ctxt pos markup (SOME text) =
        Navigation.defer_report_text ctxt pos markup text

  fun use_markup ({alias, alias_pos, identity, ...}: binding) =
    Position.make_entity_markup {def = false} identity importN (alias, alias_pos)

  fun defer_use_reference ctxt pos binding =
    if not (Position.is_reported pos) then ()
    else
      (case Thread_Data.get active_reports of
         SOME reports => reports := Use_Report (pos, use_markup binding) :: !reports
       | NONE => Navigation.defer_report ctxt pos (use_markup binding))

  fun report_alias_definitions ctxt bindings =
    let
      val leaves =
        distinct (fn (left: binding, right: binding) => #identity left = #identity right) bindings
      fun leaf_description (binding: binding) =
        bindings
        |> filter (fn other: binding => #identity other = #identity binding)
        |> map describe
        |> distinct (op =)
        |> cat_lines
      fun report (binding as {alias, alias_pos, identity, ...}: binding) =
        (defer_declaration_report ctxt alias_pos
           (Position.make_entity_markup {def = true} identity importN (alias, alias_pos)) NONE;
         defer_declaration_report ctxt alias_pos Markup.typing (SOME (leaf_description binding)))
    in List.app report leaves end

  fun capture_reports action =
    (case Thread_Data.get active_reports of
       SOME _ => (action (), [])
     | NONE =>
         let
           val reports = Unsynchronized.ref ([]: report list)
           val result = Thread_Data.setmp active_reports (SOME reports) action ()
         in (result, rev (!reports)) end)

  fun replay_use_reports ctxt reports =
    List.app (fn Use_Report (pos, markup) => Navigation.defer_report ctxt pos markup) reports
end
\<close>

end
