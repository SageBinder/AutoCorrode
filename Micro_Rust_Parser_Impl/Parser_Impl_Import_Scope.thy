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
     identity: serial,
     declaration_pos: Position.T}

  val key_segments: string -> string list
  val namespace_name: namespace -> string
  val role_name: role -> string
  val role_namespace: role -> namespace
  val has_role: binding -> role -> bool
  val describe: binding -> string

  val lookup: Proof.context -> namespace -> string -> binding option
  val lookup_persistent: Proof.context -> namespace -> string -> binding option
  val dump_persistent: Proof.context -> binding list
  val frame_depth: Proof.context -> int

  val check_batch: binding list -> unit
  val push_frame: binding list -> Proof.context -> Proof.context
  val check_persistent_duplicates: Proof.context -> binding list -> unit
  val declare_persistent: binding list -> local_theory -> local_theory
  val merge_persistent: binding list * binding list -> binding list
  val check_item_collision:
    Proof.context -> {item: string, name: string, pos: Position.T} -> namespace -> unit
  val check_merged_collision:
    Proof.context -> binding -> {item: string, pos: Position.T} option -> unit

  type reports
  val defer_declaration_report: Position.T -> Markup.T -> string option -> unit
  val defer_use_reference: Proof.context -> Position.T -> binding -> unit
  val report_alias_definitions: binding list -> unit
  val capture_reports: (unit -> 'a) -> 'a * reports
  val replay_declaration_reports: Proof.context -> reports -> unit
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
    all namespace bindings of one imported leaf, and the leaf's declaration span.
  - lookup returns the nearest binding in the requested namespace: block frames from innermost to
    outermost, then the persistent bindings of the context. lookup_persistent consults only the
    latter. frame_depth counts the active block frames.
  - check_batch rejects two bindings with the same alias and namespace, even with identical targets;
    the later binding is reported with the earlier position. push_frame returns a derived context
    with one immutable block frame; frames are proof data and never enter theory data.
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
  - Semantic reports are queued in two classes while capture_reports is active. Declaration reports
    (alias definitions and use-item tooltips) are replayed by replay_declaration_reports before the
    ordinary navigation reports; use references at alias occurrences are replayed last by
    replay_use_reports, making the import declaration the final source navigation target. Without an
    active capture, use references fall back to deferred semantic navigation and declaration reports
    are emitted immediately.
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

  fun describe ({alias, key, namespace, roles, ...}: binding) =
    "Rust import " ^ quote alias ^ " of " ^ quote key ^ " (" ^
      namespace_name namespace ^ " namespace: " ^ commas (map role_name roles) ^ ")"

  fun table_key namespace alias = namespace_name namespace ^ "\000" ^ alias

  fun same_target (left: binding, right: binding) =
    #namespace left = #namespace right andalso #alias left = #alias right andalso
      #key left = #key right andalso #roles left = #roles right

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
        bindings Symtab.empty)

  fun push_frame bindings ctxt =
    let
      val _ = check_batch bindings
      val frame =
        fold (fn binding => Symtab.update (table_key (#namespace binding) (#alias binding), binding))
          bindings Symtab.empty
    in Frames.map (cons frame) ctxt end

  fun check_persistent_duplicates ctxt bindings =
    List.app
      (fn binding =>
        (case lookup_persistent ctxt (#namespace binding) (#alias binding) of
           SOME earlier => duplicate_error earlier binding
         | NONE => ()))
      bindings

  fun declare_persistent bindings lthy =
    let
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

  datatype report =
      Declaration_Report of Position.T * Markup.T * string option
    | Use_Report of Position.T * Markup.T

  type reports = report list

  val active_reports: report list Unsynchronized.ref Thread_Data.var = Thread_Data.var ()

  fun emit_now ctxt (pos, markup, NONE) = Context_Position.report ctxt pos markup
    | emit_now ctxt (pos, markup, SOME text) = Context_Position.report_text ctxt pos markup text

  fun defer_declaration_report pos markup text =
    if not (Position.is_reported pos) then ()
    else
      (case Thread_Data.get active_reports of
         SOME reports => reports := Declaration_Report (pos, markup, text) :: !reports
       | NONE =>
           (case text of
              NONE => Position.report pos markup
            | SOME body => Position.report_text pos markup body))

  fun use_markup ({alias, alias_pos, identity, ...}: binding) =
    Position.make_entity_markup {def = false} identity importN (alias, alias_pos)

  fun defer_use_reference ctxt pos binding =
    if not (Position.is_reported pos) then ()
    else
      (case Thread_Data.get active_reports of
         SOME reports => reports := Use_Report (pos, use_markup binding) :: !reports
       | NONE => Navigation.defer_report ctxt pos (use_markup binding))

  fun report_alias_definitions bindings =
    let
      val leaves =
        distinct (fn (left: binding, right: binding) => #identity left = #identity right) bindings
      fun leaf_description (binding: binding) =
        bindings
        |> filter (fn other: binding => #identity other = #identity binding)
        |> map describe
        |> cat_lines
      fun report (binding as {alias, alias_pos, identity, ...}: binding) =
        (defer_declaration_report alias_pos
           (Position.make_entity_markup {def = true} identity importN (alias, alias_pos)) NONE;
         defer_declaration_report alias_pos Markup.typing (SOME (leaf_description binding)))
    in List.app report leaves end

  fun capture_reports action =
    (case Thread_Data.get active_reports of
       SOME _ => (action (), [])
     | NONE =>
         let
           val reports = Unsynchronized.ref ([]: report list)
           val result = Thread_Data.setmp active_reports (SOME reports) action ()
         in (result, rev (!reports)) end)

  fun replay_declaration_reports ctxt reports =
    List.app
      (fn Declaration_Report event => emit_now ctxt event | Use_Report _ => ())
      reports

  fun replay_use_reports ctxt reports =
    List.app
      (fn Use_Report (pos, markup) => Context_Position.report ctxt pos markup
        | Declaration_Report _ => ())
      reports
end
\<close>

end
