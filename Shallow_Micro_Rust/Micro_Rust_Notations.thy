(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Table-backed registry of uRust name notations + a typed dispatcher.

   This is the sole mechanism for registering a uRust name with a HOL
   backend, via the `micro_rust_notation` command. It replaces an older
   approach based on per-name `translations` and per-operator
   `adhoc_overloading` consts emitted by a family of per-kind commands. The
   registry is a single string-indexed `Generic_Data` table; dispatch is a single
   `String.literal`-parametrized const `urust_dispatch` whose markers are
   resolved in a typed `term_check` phase, in adhoc-overloading style. *)

theory Micro_Rust_Notations
  imports
    Semantic_Navigation
  keywords
    "micro_rust_notation" :: thy_decl and
    "print_micro_rust_notations" :: diag
begin

text\<open>
The legacy \<open>associated_owner = {self_type, identity}\<close> record and
\<open>reserve_associated_function\<close>/\<open>associated_functions\<close> APIs remain unchanged.
\<open>reserve_associated_source_function\<close> and \<open>associated_source_functions\<close>
add an optional canonical source identity beside the morphism-transformed HOL Self type.
The old view remains available; source-aware selection compares both identities where erased
arguments matter. A method receiver carrying only a HOL type cannot recover an erased tag or
capacity, so an identity-dependent member requires an explicit associated/alias/Self path.
Native full-type filtering, freshening, maximal candidates, deduplication, ambiguity and explicit
notation precedence remain authoritative for sparse generated calls. Only a selected candidate
commits its source observations, callbacks and reports.
\<close>

(* ===================================================================== *)
(* uRust-name -> HOL-term registry, consulted by the dispatch term_check  *)
(* phase on identifier resolution.  Three contexts (literal/field/        *)
(* function); a name registered only as `field` must still fall back to   *)
(* identity in value position, so we key by (context, name).              *)
(* ===================================================================== *)

ML\<open>
structure Micro_Rust_Names = struct

\<comment>\<open>The three registration contexts (\<open>"literal"\<close> / \<open>"field"\<close> /
  \<open>"function"\<close>), selected by the optional \<open>micro_rust_notation\<close> kind
  modifier (\<open>(literal)\<close> / \<open>(field)\<close> / \<open>(call)\<close>) or inferred from the
  term's type when the modifier is omitted.\<close>
datatype ctxt_kind = NLiteral | NFunction | NField;

fun kind_to_string NLiteral = "literal"
  | kind_to_string NFunction = "function"
  | kind_to_string NField = "field";

fun string_to_kind "literal" = NLiteral
  | string_to_kind "function" = NFunction
  | string_to_kind "field" = NField
  | string_to_kind s = error ("unknown micro_rust_notation context: " ^ s);

\<comment>\<open>Sniff the registration kind from a HOL term's type --- a function call
  iff the type is \<open>_ \<Rightarrow> _ function_body\<close>, a field iff the type is \<open>_ lens\<close>,
  otherwise a literal. Shared by the auto-inferred-kind path of
  \<open>micro_rust_notation\<close> and by the shadow check (which only flags
  call-/field-shaped HOL constants as ambiguous shadows).\<close>
\<comment>\<open>Recognise the type by looking at its outermost shape:
   - any \<open>_ \<Rightarrow> ... \<Rightarrow> _ function_body\<close> chain (uncurried calls have a
     binary or higher \<open>function_body\<close> result) is a function backend;
   - any \<open>_ lens\<close> is a field backend;
   - everything else is a literal.

  The \<open>fun\<close>-walk handles multi-argument functions like
  \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, _, _, _) function_body\<close> --- without it the
  binary signature would collapse to literal at auto-infer time and a
  use site \<open>foo(x, y)\<close> would never reach the function-kind table.\<close>
fun infer_kind_of_type (Type ("Core_Expression.function_body", _)) = NFunction
  | infer_kind_of_type (Type ("fun", [_, T])) = infer_kind_of_type T
  | infer_kind_of_type (Type ("Lens.lens", _)) = NField
  | infer_kind_of_type _ = NLiteral;

\<comment>\<open>A registered entry: the resolved HOL \<^emph>\<open>term\<close> the notation stands for,
  an optional source constant retained before abbreviation expansion, the
  position of the registering command (so leaf markup can hyperlink to the
  declaration site), and a unique \<open>serial\<close> that pairs the def-side
  markup at the registration site with ref-side markup at every use site
  (mirrors the \<open>def\<close>/\<open>ref\<close> protocol of \<^ML>\<open>Position.make_entity_markup\<close>;
  see e.g. \<open>Pure/Isar/calculation.ML\<close> for a textbook use). Storing a TERM
  (not just a constant name) is what lets a notation target an arbitrary
  expression --- in particular a locale-fixed parameter (a \<open>Free\<close>) or a
  local definition --- not only a global constant. The declaration
  morphism is applied to both stored terms at registration (see
  \<open>do_register\<close>), so under locale interpretation / derivation they track
  the parameter substitution.\<close>
type entry =
  {hol_term: term, source_const: term option,
   reg_pos: Position.T, serial: serial};

\<comment>\<open>MULTIPLE BACKENDS PER NAME (adhoc-overloading-style dispatch). A single
  uRust name may have several HOL backends differing only by type, just as
  the existing code base does manually via an uninterpreted const +
  \<open>adhoc_overloading\<close>. We therefore store a LIST of entries per
  \<open>(kind, name)\<close>, and merge tables by UNION (\<open>Symtab.merge_list\<close>) ---
  exactly as \<open>adhoc_overloading.ML\<close>'s variant table does. This makes the
  registry MERGE-STABLE: if two theories independently register a backend
  for the same name, importing both yields the union of backends, no
  collision and no "last-write-wins" loss. (Resolution to a single backend
  happens later, in a typed \<open>term_check\<close> phase --- see \<open>urust_dispatch\<close>
  below --- because the parse phase runs pre-type and cannot itself choose
  by type.)

  \<open>reg_eq\<close> identifies backends by their typed term, without positions and up to the
  naming of schematic type variables, so theory merges stay transitive. Replaying a registration
  is idempotent (e.g. when a syntax declaration is replayed on context-open). The client-visible
  view of a key is computed from its registrations by \<open>lookups\<close>, which hides covered
  explicit schemes (\<open>backend_covers\<close>).\<close>
fun normalized_backend term =
  let
    val stripped = Term_Position.strip_positions term;
    val substitutions =
      Term.add_tvars stripped [] |> rev
      |> map_index (fn (index, (variable, sort)) =>
           ((variable, sort), TVar (("'backend" ^ string_of_int index, 0), sort)))
      |> TVars.make;
  in
    stripped |> Term.map_types (Term_Subst.instantiateT substitutions)
    |> Term_Subst.zero_var_indexes
  end;

(* A cheap prefilter. Normalization renames type variables and renumbers schematic indexes; the
   untyped skeleton is invariant under it as long as the backend has no term-level schematic
   variables, which registered backends never have (registration generalizes types only). *)
fun same_skeleton (e1 : entry, e2 : entry) =
  Term.aconv_untyped (apply2 (Term_Position.strip_positions o #hol_term) (e1, e2));

fun reg_eq (e1 : entry, e2 : entry) =
  same_skeleton (e1, e2) andalso
  Term.aconv (apply2 normalized_backend (#hol_term e1, #hol_term e2));

(* A specialization of an already registered polymorphic backend adds no capability. Match
   complete types and value syntax so concrete locale instances of different types stay distinct. *)
fun backend_covers thy (general: entry) (specific: entry) =
  same_skeleton (general, specific) andalso
  let
    val general_term = normalized_backend (#hol_term general);
    val specific_term = normalized_backend (#hol_term specific);
    val shifted = Term.map_types (Logic.incr_tvar (Term.maxidx_of_term specific_term + 1)) general_term;
  in can (Pattern.match thy (shifted, specific_term)) (Vartab.empty, Vartab.empty) end;

(* Data holds the registrations themselves; clients see the view computed by lookups below.
   Merging identifies only identical registrations (same serial and backend), so a theory union
   keeps every registration of its branches whatever the merge order. *)
fun same_registration (e1 : entry, e2 : entry) = #serial e1 = #serial e2 andalso reg_eq (e1, e2);

structure Data = Generic_Data
(
  type T = entry list Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge_list same_registration;
);

(* Namespace ownership is declaration-only: overloadable functions carry no backend here.
   Both insertion and theory merge check constructor conflicts independently of merge order.
   An associated function of an impl additionally carries its Self type and the identity of the
   impl member, the source serial of its path entry. *)
datatype source_kind = Type_Source | Const_Source

datatype source_head =
    Primitive_Source of string
  | Mapped_Source of string
  | Opaque_Source of (string * int) list
  | Numeric_Source of int
  | Tuple_Source | Slice_Source | Array_Source | Pointer_Source of bool | Reference_Source of bool;

datatype source_tree =
    Source_Variable of indexname * source_kind
  | Source_Rigid of serial * source_kind
  | Source_Node of source_head * source_tree list
  | Source_HOL of source_kind * typ;

type source_path = int list;
type source_variable = {name: indexname, kind: source_kind, witness: typ option};
type target_template =
  {self_type: typ, source: source_tree option, variables: source_variable list,
   requires_source_identity: bool};
type target_selection =
  {self_type: typ, source: source_tree option, source_identity: string option,
   evidence: (source_path * typ) list,
   inputs: (source_path * (string * Position.T)) list, pos: Position.T};
type source_binding =
  {variable: indexname, kind: source_kind, value: source_tree,
   path: source_path, witness: typ option, evidence: typ option};
type target_match = {types: Type.tyenv, maxidx: int, bindings: source_binding list};

fun source_kind (Source_Variable (_, kind)) = kind
  | source_kind (Source_Rigid (_, kind)) = kind
  | source_kind (Source_HOL (kind, _)) = kind
  | source_kind (Source_Node (Numeric_Source _, _)) = Const_Source
  | source_kind _ = Type_Source;

fun map_source_types f (Source_HOL (kind, T)) = Source_HOL (kind, f T)
  | map_source_types f (Source_Node (head, children)) =
      Source_Node (head, map (map_source_types f) children)
  | map_source_types _ tree = tree;
fun source_types (Source_HOL (_, T)) = [T]
  | source_types (Source_Node (_, children)) = maps source_types children
  | source_types _ = [];
fun map_source_variables f (Source_Variable (name, kind)) = Source_Variable (f name, kind)
  | map_source_variables f (Source_Node (head, children)) =
      Source_Node (head, map (map_source_variables f) children)
  | map_source_variables _ tree = tree;

fun map_target_types f ({self_type, source, variables, requires_source_identity}: target_template) =
  {self_type = f self_type, source = Option.map (map_source_types f) source,
   variables = map (fn {name, kind, witness} =>
     {name = name, kind = kind, witness = Option.map f witness}) variables,
   requires_source_identity = requires_source_identity}: target_template;
fun target_types ({self_type, source, variables, ...}: target_template) =
  self_type :: maps source_types (the_list source) @ map_filter #witness variables;

exception SOURCE_MATCH;

(* Source substitutions and native type constraints are solved together. Only explicit template
   variables bind; caller declarations are rigid. Evidence is supplied by the canonicalizer. *)
fun unify_source_trees unify variables evidence left right initial =
  let
    fun variable name = find_first (fn ({name = other, ...}: source_variable) => name = other) variables;
    fun witness name = Option.mapPartial #witness (variable name);
    fun resolve substitutions (Source_Variable (name, kind)) =
          (case AList.lookup (op =) substitutions name of NONE => Source_Variable (name, kind)
           | SOME value => resolve substitutions value)
      | resolve substitutions (Source_Node (head, children)) =
          Source_Node (head, map (resolve substitutions) children)
      | resolve _ tree = tree;
    fun occurs name (Source_Variable (other, _)) = name = other
      | occurs name (Source_Node (_, children)) = exists (occurs name) children
      | occurs _ _ = false;
    fun actual side path (Source_Variable (name, _)) = witness name
      | actual _ _ (Source_HOL (_, T)) = SOME T
      | actual side path _ = evidence side path;
    fun constrain NONE _ state = state
      | constrain _ NONE state = state
      | constrain (SOME T) (SOME U) (substitutions, (types, maxidx), bindings) =
          (substitutions, unify (T, U) (types, maxidx), bindings);
    fun bind side path (name, kind) value state =
      if source_kind value <> kind orelse occurs name value then raise SOURCE_MATCH
      else
        let
          val state = constrain (witness name) (actual side path value) state;
          val (substitutions, native, bindings) = state;
          val binding = {variable = name, kind = kind, value = value, path = path,
            witness = witness name, evidence = actual side path value}: source_binding;
        in ((name, value) :: substitutions, native, binding :: bindings) end;
    fun visit left_path right_path (left, right) state =
      let
        val (substitutions, _, _) = state;
        val left = resolve substitutions left;
        val right = resolve substitutions right;
      in
        case (left, right) of
          (Source_Variable (name, kind), Source_Variable (other, other_kind)) =>
            if name = other then (if kind = other_kind then state else raise SOURCE_MATCH)
            else bind false right_path (name, kind) right state
        | (Source_Variable parameter, value) => bind false right_path parameter value state
        | (value, Source_Variable parameter) => bind true left_path parameter value state
        | (Source_Rigid left, Source_Rigid right) =>
            if left = right then state else raise SOURCE_MATCH
        | (Source_HOL (kind, T), Source_HOL (other_kind, U)) =>
            if kind = other_kind then constrain (SOME T) (SOME U) state else raise SOURCE_MATCH
        | (Source_Node (head, children), Source_Node (other, others)) =>
            if head = other andalso length children = length others then
              fold_index (fn (index, pair) => visit (left_path @ [index]) (right_path @ [index]) pair)
                (children ~~ others) state
            else raise SOURCE_MATCH
        | _ => raise SOURCE_MATCH
      end;
    val (_, (types, maxidx), bindings) = visit [] [] (left, right) ([], initial, []);
  in {types = types, maxidx = maxidx, bindings = rev bindings}: target_match end;

fun match_target ctxt (template: target_template) (selection: target_selection) initial =
  let
    fun unify pair state = Sign.typ_unify (Proof_Context.theory_of ctxt) pair state;
    fun run () =
      let val native = unify (#self_type template, #self_type selection) initial in
        (* Delivered concrete owners select through native HOL equivalence. No structural
           assignment is needed unless an impl parameter or erased source identity exists. *)
        if not (#requires_source_identity template) andalso null (#variables template) then
          {types = #1 native, maxidx = #2 native, bindings = []}
        else case (#source template, #source selection) of
          (SOME left, SOME right) =>
            unify_source_trees unify (#variables template)
              (fn side => fn path => if side then NONE else AList.lookup (op =) (#evidence selection) path)
              left right native
        | (SOME _, NONE) => if #requires_source_identity template then raise SOURCE_MATCH
            else {types = #1 native, maxidx = #2 native, bindings = []}
        | _ => {types = #1 native, maxidx = #2 native, bindings = []}
      end;
  in SOME (run ()) handle SOURCE_MATCH => NONE | Type.TUNIFY => NONE end;

fun subst_target ({types, bindings, ...}: target_match) template =
  let
    fun source (Source_Variable (name, kind)) =
          (case find_first (fn ({variable, ...}: source_binding) => variable = name) bindings of
             NONE => Source_Variable (name, kind) | SOME {value, ...} => source value)
      | source (Source_Node (head, children)) = Source_Node (head, map source children)
      | source tree = tree;
    val {self_type, source = tree, variables, requires_source_identity} =
      map_target_types (Envir.norm_type types) template;
  in {self_type = self_type, source = Option.map source tree, variables = variables,
    requires_source_identity = requires_source_identity}: target_template end;

fun fresh_target shift ({self_type, source, variables, requires_source_identity}: target_template) =
  let
    fun rename (name, index) = (name, index + shift);
    val target = {self_type = self_type, source = Option.map (map_source_variables rename) source,
      variables = map (fn {name, kind, witness} =>
        {name = rename name, kind = kind, witness = witness}) variables,
      requires_source_identity = requires_source_identity}: target_template;
  in map_target_types (Logic.incr_tvar shift) target end;

fun overlapping_targets (left: target_template, right: target_template) =
  let
    val source_max = fold (fn ({name = (_, index), ...}: source_variable) => fn n => Int.max (index, n));
    val maxidx = fold Term.maxidx_typ (target_types left @ target_types right)
      (source_max (#variables left @ #variables right) ~1);
    val right = fresh_target (maxidx + 1) right;
    fun unify pair (types, n) = (Type.raw_unify pair types, n);
    fun run () =
      let val native = unify (#self_type left, #self_type right) (Vartab.empty, maxidx + 1) in
        (* Different retained source representations cannot establish native disjointness.
           Genuine erased identities still require the joint structural relation below. *)
        if not (#requires_source_identity left) andalso
            not (#requires_source_identity right) then ()
        else case (#source left, #source right) of
          (SOME first, SOME second) => ignore (unify_source_trees unify
            (#variables left @ #variables right) (fn _ => fn _ => NONE) first second native)
        | _ => ()
      end;
  in (run (); true) handle SOURCE_MATCH => false | Type.TUNIFY => false end;

type associated_owner = {self_type: typ, identity: serial};

datatype declaration_kind =
    Function_Declaration
  | Constructor_Declaration
  | Associated_Function_Declaration of associated_owner
  | Associated_Source_Function_Declaration of
      {self_type: typ, identity: serial, source_identity: string}
  | Associated_Template_Function_Declaration of
      {target: target_template, identity: serial, source_identity: string option};
type declaration_owner = {kind: declaration_kind, pos: Position.T};

(* Self types are stored generalized, with schematic variables named canonically, so a replay or a
   theory merge of the same owner is recognized structurally. *)
fun normalized_self_type T =
  let
    val substitutions =
      Term.add_tvarsT T [] |> rev
      |> map_index (fn (index, (variable, sort)) =>
           ((variable, sort), TVar (("'self" ^ string_of_int index, 0), sort)))
      |> TVars.make;
  in Term_Subst.instantiateT substitutions T end;

fun owner_eq (left: declaration_owner, right: declaration_owner) =
  #kind left = #kind right;

fun is_function_owner ({kind = Constructor_Declaration, ...}: declaration_owner) = false
  | is_function_owner _ = true;

fun associated_owner ({kind = Associated_Function_Declaration owner, pos}: declaration_owner) =
      SOME (owner, pos)
  | associated_owner ({kind = Associated_Source_Function_Declaration
        {self_type, identity, ...}, pos}: declaration_owner) =
      SOME ({self_type = self_type, identity = identity}, pos)
  | associated_owner ({kind = Associated_Template_Function_Declaration
        {target, identity, ...}, pos}: declaration_owner) =
      SOME ({self_type = #self_type target, identity = identity}, pos)
  | associated_owner _ = NONE;

fun associated_source_owner ({kind = Associated_Source_Function_Declaration
      {self_type, identity, source_identity}, pos}: declaration_owner) =
      SOME ({self_type = self_type, identity = identity,
        source_identity = SOME source_identity}, pos)
  | associated_source_owner ({kind = Associated_Template_Function_Declaration
        {target, identity, source_identity}, pos}: declaration_owner) =
      SOME ({self_type = #self_type target, identity = identity,
        source_identity = source_identity}, pos)
  | associated_source_owner owner =
      Option.map (fn ({self_type, identity}, pos) =>
        ({self_type = self_type, identity = identity, source_identity = NONE}, pos))
        (associated_owner owner);

(* Inherent impls overlap when their Self types unify. Theory merges have no type signature, so
   both checks use the same purely structural unification, which ignores sorts. *)
fun overlapping_self_types (left, right) =
  let
    val shifted = Logic.incr_tvar (Term.maxidx_of_typ left + 1) right;
  in can (Type.raw_unify (left, shifted)) Vartab.empty end;

fun associated_template_owner
    ({kind = Associated_Template_Function_Declaration owner, pos}: declaration_owner) =
      SOME (owner, pos)
  | associated_template_owner owner =
      Option.map (fn ({self_type, identity, source_identity}, pos) =>
        ({target = {self_type = self_type, source = NONE, variables = [],
            requires_source_identity = is_some source_identity}: target_template,
          identity = identity, source_identity = source_identity}, pos))
        (associated_source_owner owner);

(* Owner order and both checks use the same structural relation. Unenriched legacy tokens
   retain exact concrete equality; a generic template cannot decode or disprove their identity. *)
fun associated_conflict name owners =
  let
    val associated = map_filter associated_template_owner owners
      |> sort (int_ord o apply2 (#identity o fst));
    fun overlap (left, right) =
      let
        val generic = not (null (#variables (#target left))) orelse
          not (null (#variables (#target right)));
        val enriched = is_some (#source (#target left)) andalso is_some (#source (#target right));
        val compatible = enriched orelse generic orelse
          is_none (#source_identity left) orelse is_none (#source_identity right) orelse
          #source_identity left = #source_identity right;
      in compatible andalso overlapping_targets (#target left, #target right) end;
    fun search [] = NONE
      | search ((owner, pos) :: rest) =
          (case find_first (fn (other, _) => #identity owner <> #identity other andalso
              overlap (owner, other)) rest of
             NONE => search rest | SOME (_, other_pos) => SOME [pos, other_pos]);
  in Option.map (fn positions =>
    "urust: associated function " ^ quote name ^
      " is defined in more than one impl with overlapping Self types" ^
      implode (map Position.here positions)) (search associated) end;

fun check_owners name (owners: declaration_owner list) =
  if exists is_function_owner owners andalso
      exists (fn owner => #kind owner = Constructor_Declaration) owners
  then error ("urust_fn: Rust function path " ^ quote name ^
    " is already owned by a Rust constructor item" ^
    implode (map (Position.here o #pos) owners))
  else
    (case associated_conflict name owners of
       SOME message => error message
     | NONE => owners);

structure Declaration_Owners = Generic_Data
(
  type T = declaration_owner list Symtab.table;
  val empty = Symtab.empty;
  fun merge tables = Symtab.merge_list owner_eq tables |> Symtab.map check_owners;
);

(* Serials of automatic urust_fn registrations. They stand for Rust function items, which take no
   generic arguments at a call, whereas an explicit call notation may receive a turbofish payload. *)
structure Automatic_Registrations = Generic_Data
(
  type T = unit Inttab.table;
  val empty = Inttab.empty;
  val merge = Inttab.merge (K true);
);

fun mark_automatic s = Automatic_Registrations.map (Inttab.update (s, ()));

fun is_automatic_serial context s = Inttab.defined (Automatic_Registrations.get context) s;

(* Serials of automatic method entries: the bare-name registrations of impl members with a self
   receiver. A Rust method is not in scope as a free function, so direct calls exclude them. *)
structure Method_Only_Registrations = Generic_Data
(
  type T = unit Inttab.table;
  val empty = Inttab.empty;
  val merge = Inttab.merge (K true);
);

structure Method_Source_Owners = Generic_Data
(
  type T = serial Inttab.table;
  val empty = Inttab.empty;
  val merge = Inttab.merge (op =);
);

fun mark_method_only s = Method_Only_Registrations.map (Inttab.update (s, ()));
fun mark_method_only_owner s identity = mark_method_only s #>
  Method_Source_Owners.map (Inttab.update (s, identity));

fun is_method_only_serial context s =
  Inttab.defined (Method_Only_Registrations.get context) s;

fun reserve_owner name owner =
  Declaration_Owners.map (fn table =>
    let
      val owners = the_default [] (Symtab.lookup table name);
      (* A repeated declaration of an owned kind keeps the first owner and its position. *)
      val checked = check_owners name (insert owner_eq owner owners);
    in Symtab.update (name, checked) table end);

fun reserve_declaration kind name pos = reserve_owner name {kind = kind, pos = pos};

(* The caller allocates the identity before its declaration callback and applies the declaration
   morphism to the Self type, so a replay or an interpretation at the same type is idempotent while
   differently typed instances of one impl coexist. *)
fun reserve_associated_function {name, self_type, identity, pos} context =
  let
    val generalized =
      singleton (Variable.polymorphic (Context.proof_of context)) (Logic.mk_type self_type)
      |> Logic.dest_type |> normalized_self_type;
    val owner = {self_type = generalized, identity = identity};
  in reserve_owner name {kind = Associated_Function_Declaration owner, pos = pos} context end;

fun associated_functions ctxt name =
  the_default [] (Symtab.lookup (Declaration_Owners.get (Context.Proof ctxt)) name)
  |> map_filter associated_owner
  |> map (fn ({self_type, identity}, pos) =>
       {self_type = self_type, identity = identity, pos = pos});

fun reserve_associated_source_function {name, self_type, identity, pos, source_identity} context =
  (case source_identity of NONE =>
      reserve_associated_function {name = name, self_type = self_type, identity = identity, pos = pos} context
   | SOME source =>
       let
         val generalized = singleton (Variable.polymorphic (Context.proof_of context))
           (Logic.mk_type self_type) |> Logic.dest_type |> normalized_self_type;
       in reserve_owner name {kind = Associated_Source_Function_Declaration
         {self_type = generalized, identity = identity, source_identity = source}, pos = pos} context end);

fun associated_source_functions ctxt name =
  the_default [] (Symtab.lookup (Declaration_Owners.get (Context.Proof ctxt)) name)
  |> map_filter associated_source_owner
  |> map (fn ({self_type, identity, source_identity}, pos) =>
    {self_type = self_type, identity = identity, source_identity = source_identity, pos = pos});

fun reserve_associated_template_function {name, target, identity, source_identity, pos} context =
  let
    val ctxt = Context.proof_of context;
    val types = target_types target;
    val generalized = Variable.polymorphic ctxt (map Logic.mk_type types)
      |> map Logic.dest_type;
    val normalized = normalized_self_type (generalized ---> propT) |> binder_types;
    val substitutions = types ~~ normalized;
    fun replace T = the (AList.lookup (op =) substitutions T);
    val {self_type, source, variables, requires_source_identity} = map_target_types replace target;
    val names = map #name variables;
    val normalized_names = map_index (fn (index, _) => ("_urust_owner_source", index)) names;
    fun rename name = the (AList.lookup (op =) (names ~~ normalized_names) name);
    val target = {self_type = self_type, source = Option.map (map_source_variables rename) source,
      variables = map (fn {name, kind, witness} => {name = rename name, kind = kind,
        witness = witness}) variables, requires_source_identity = requires_source_identity};
  in reserve_owner name {kind = Associated_Template_Function_Declaration
    {target = target, identity = identity, source_identity = source_identity}, pos = pos} context end;

fun associated_template_functions ctxt name =
  the_default [] (Symtab.lookup (Declaration_Owners.get (Context.Proof ctxt)) name)
  |> map_filter associated_template_owner
  |> map (fn ({target, identity, source_identity}, pos) =>
    {target = target, identity = identity, source_identity = source_identity, pos = pos});

fun method_requires_source_identity ctxt serial =
  (case Inttab.lookup (Method_Source_Owners.get (Context.Proof ctxt)) serial of
     SOME identity =>
       Symtab.dest (Declaration_Owners.get (Context.Proof ctxt))
       |> maps (map_filter associated_template_owner o snd)
       |> exists (fn ({identity = owner, target, ...}, _) =>
         owner = identity andalso #requires_source_identity target)
   | _ => false);

fun is_associated_function ctxt name = not (null (associated_functions ctxt name));

fun mk_key kind name = kind_to_string kind ^ "\000" ^ name;

(* Rust keys never contain the keywords Self (reserved for impl blocks) or self (reserved for the
   module) as a segment. The one exception is a bare key self, which a literal notation may use
   for an ordinary HOL value. Every registration command applies this one check. *)
val reserved_key_segments = ["Self", "self"];

fun key_segments name =
  let
    fun split input =
      let val (segment, rest) = Substring.position "::" input in
        Substring.string segment ::
          (if Substring.isEmpty rest then [] else split (Substring.triml 2 rest))
      end
  in split (Substring.full name) end;

fun reserved_key_segment {bare_self} name =
  let
    val segments = key_segments name
    fun reserved segment =
      exists (fn keyword =>
          segment = keyword orelse String.isPrefix (keyword ^ "<") segment orelse
          segment = keyword ^ "!")
        reserved_key_segments
  in
    (case segments of
       [segment] => if bare_self andalso segment = "self" then NONE
         else if reserved segment then SOME segment else NONE
     | _ => find_first reserved segments)
  end;

fun reserved_key_message segment =
  if String.isPrefix "Self" segment
  then "Self is reserved for impl blocks and cannot be a key segment"
  else "self is reserved for module paths and cannot be a key segment";

\<comment>\<open>Markup kind for uRust notation entities (def/ref protocol).\<close>
val notationN = "micro_rust_notation";

\<comment>\<open>Shadow-check opt-out state. \<open>shadow_opts\<close> records two independent
  bits; the table tracks a \<^emph>\<open>default\<close> (concrete, applies to every name)
  plus per-(kind, name) overrides whose bits are \<open>bool option\<close>: a
  \<open>SOME\<close>-bit replaces the default for that bit, a \<open>NONE\<close>-bit inherits.
  The four user-facing modes each set exactly one override bit
  (see \<open>set_shadow_bit\<close> below).\<close>
type shadow_opts = { suppress_warning : bool, suppress_error : bool };
type shadow_opts_override =
  { suppress_warning : bool option, suppress_error : bool option };

\<comment>\<open>Default: errors are suppressed; the check still fires as a warning
  unless \<open>suppress_warning\<close> is also on.\<close>
val default_shadow_opts : shadow_opts =
  { suppress_warning = false, suppress_error = true };

val no_override : shadow_opts_override =
  { suppress_warning = NONE, suppress_error = NONE };

\<comment>\<open>Combine two defaults (OR each bit) for merging tables across imports:
  if either source said "suppress this bit", the merged default
  preserves the suppression.\<close>
fun merge_shadow_opts ({ suppress_warning = a1, suppress_error = b1 },
                       { suppress_warning = a2, suppress_error = b2 })
      : shadow_opts =
  { suppress_warning = a1 orelse a2, suppress_error = b1 orelse b2 };

\<comment>\<open>Combine two overrides per bit: \<open>NONE\<close> is identity; two \<open>SOME\<close>s OR
  (the more-suppressing setting wins, mirroring \<open>merge_shadow_opts\<close>).\<close>
fun merge_opt (NONE, x) = x
  | merge_opt (x, NONE) = x
  | merge_opt (SOME a, SOME b) = SOME (a orelse b);

fun merge_shadow_overrides ({ suppress_warning = a1, suppress_error = b1 },
                            { suppress_warning = a2, suppress_error = b2 })
      : shadow_opts_override =
  { suppress_warning = merge_opt (a1, a2),
    suppress_error = merge_opt (b1, b2) };

\<comment>\<open>The four single-bit setters: each updates one field of an existing
  override and leaves the other untouched.\<close>
datatype shadow_bit =
    Set_Suppress_Warning of bool
  | Set_Suppress_Error of bool;

fun apply_shadow_bit (Set_Suppress_Warning b)
                     ({ suppress_error, ... } : shadow_opts_override) =
      { suppress_warning = SOME b, suppress_error = suppress_error }
  | apply_shadow_bit (Set_Suppress_Error b)
                     ({ suppress_warning, ... } : shadow_opts_override) =
      { suppress_warning = suppress_warning, suppress_error = SOME b };

\<comment>\<open>Same setter, but applied to a concrete (non-optional) default
  \<open>shadow_opts\<close>: the bit value is forced (the override is collapsed
  into the default).\<close>
fun apply_shadow_bit_default (Set_Suppress_Warning b)
                             ({ suppress_error, ... } : shadow_opts) =
      { suppress_warning = b, suppress_error = suppress_error }
  | apply_shadow_bit_default (Set_Suppress_Error b)
                             ({ suppress_warning, ... } : shadow_opts) =
      { suppress_warning = suppress_warning, suppress_error = b };

\<comment>\<open>Storage: a concrete default plus a per-(kind, name) override table.
  Default-merge ORs each bit; per-name override merge ORs each \<open>SOME\<close>
  bit and treats \<open>NONE\<close> as identity.\<close>
type shadow_opts_state =
  { default : shadow_opts, per_name : shadow_opts_override Symtab.table };

val empty_shadow_opts_state : shadow_opts_state =
  { default = default_shadow_opts, per_name = Symtab.empty };

fun merge_shadow_opts_state
      ({ default = d1, per_name = p1 },
       { default = d2, per_name = p2 }) : shadow_opts_state =
  { default = merge_shadow_opts (d1, d2),
    per_name = Symtab.join (K merge_shadow_overrides) (p1, p2) };

structure ShadowOpts = Generic_Data
(
  type T = shadow_opts_state;
  val empty = empty_shadow_opts_state;
  val merge = merge_shadow_opts_state;
);

\<comment>\<open>Effective opts for a given \<open>(kind, name)\<close>: per-bit, the override's
  \<open>SOME\<close> value replaces the default, \<open>NONE\<close> inherits. So a default of
  \<open>suppress_error = true\<close> can be re-opened per name via
  \<open>[shadow_err] "foo"\<close>, and vice versa.\<close>
fun shadow_opts ctxt kind name =
  let
    val { default, per_name } = ShadowOpts.get (Context.Proof ctxt)
    fun resolve (NONE, d) = d | resolve (SOME b, _) = b
  in
    case Symtab.lookup per_name (mk_key kind name) of
      NONE => default
    | SOME ov =>
        { suppress_warning =
            resolve (#suppress_warning ov, #suppress_warning default),
          suppress_error =
            resolve (#suppress_error ov, #suppress_error default) }
  end;

\<comment>\<open>Set one shadow bit on the default opts (when \<open>names = []\<close>) or on
  each \<open>(kind, name)\<close> override (when \<open>names\<close> is non-empty).
  Only the named bit is changed; the other bit is preserved.\<close>
fun set_shadow_bit kind names bit =
  if null names then
    ShadowOpts.map (fn { default, per_name } =>
      { default = apply_shadow_bit_default bit default, per_name = per_name })
  else
    let
      fun update_entry (state as { default, per_name }) name =
        let
          val key = mk_key kind name
          val old = the_default no_override (Symtab.lookup per_name key)
          val new = apply_shadow_bit bit old
        in
          { default = default, per_name = Symtab.update (key, new) per_name }
        end
    in
      ShadowOpts.map (fn state => fold (fn n => fn s => update_entry s n) names state)
    end;

(* The key of each registration serial. A serial names one registering declaration under one
   key (impl members use one serial per entry), so the status of an entry is computed under its
   own key. *)
fun describe_key key =
  (case String.fields (fn ch => ch = #"\000") key of
     [kind, name] => kind ^ " " ^ quote name
   | _ => quote key);

(* The same message on insertion and on theory merge, with the two uses in key order. *)
fun serial_reuse_error uses =
  let val sorted = sort (string_ord o apply2 fst) uses
  in
    error ("urust: notation registration serial is reused under " ^
      space_implode " and " (map (describe_key o fst) sorted) ^
      implode (map (Position.here o snd) sorted))
  end;

structure Registration_Keys = Generic_Data
(
  type T = (string * Position.T) Inttab.table;
  val empty = Inttab.empty;
  fun merge tables =
    Inttab.join (fn _ => fn (left, right) =>
      if fst left = fst right then left else serial_reuse_error [left, right]) tables;
);

fun stored_registrations context key = the_default [] (Symtab.lookup (Data.get context) key);

(* Every stored registration of a key, including those the view hides (report-free). *)
fun registrations ctxt kind name = stored_registrations (Context.Proof ctxt) (mk_key kind name);

fun is_registered_under context key entry =
  exists (fn other => same_registration (other, entry)) (stored_registrations context key);

\<comment>\<open>REGISTRATION VIEW. Every client-visible fact is computed from the stored registrations of a
  key, so it does not depend on the order of registrations or of theory merges:
   - an automatic registration is always visible under its own serial (an impl identity for
     \<open>Only_Sources\<close>), also when another registration covers it;
   - it counts as explicit (neither automatic nor method-only) when an explicit registration of
     the key covers it, and then navigates to a maximal covering explicit registration (one that no
     other covering explicit registration strictly covers), the one with the smallest serial;
   - an explicit registration that an automatic one covers adds nothing visible: it only makes
     the automatic entry explicit;
   - of explicit registrations that cover one another, only the preferred one is visible: a
     maximal covering registration with the smallest serial (\<open>preferred_explicit\<close>);
   - dispatch prefers covering schemes among the visible entries (\<open>filtered_candidates\<close>).\<close>
(* Among explicit registrations, the preferred ones are maximal (no other one strictly covers
   them), in serial order. *)
fun preferred_explicit thy explicit =
  let
    fun strictly_covered other =
      exists (fn general => backend_covers thy general other andalso
        not (backend_covers thy other general)) explicit;
  in explicit |> filter_out strictly_covered |> sort (int_ord o apply2 #serial) end;

(* An explicit registration is represented by a preferred one that covers it: a maximal covering
   registration with the smallest serial. *)
fun represented_by thy explicit entry =
  (case preferred_explicit thy (filter (fn other => backend_covers thy other entry) explicit) of
     representative :: _ => #serial representative = #serial entry
   | [] => true);

fun explicit_cover_at context key entry =
  let
    val thy = Context.theory_of context;
    val covering =
      stored_registrations context key
      |> filter (fn other as {serial, ...} =>
           not (is_automatic_serial context serial) andalso backend_covers thy other entry);
  in try hd (preferred_explicit thy covering) end;

fun explicit_cover context (entry as {serial, ...}: entry) =
  if not (is_automatic_serial context serial) then NONE
  else
    (case Option.map fst (Inttab.lookup (Registration_Keys.get context) serial) of
       SOME key =>
         if is_registered_under context key entry then explicit_cover_at context key entry
         else NONE
     | NONE => NONE);

fun is_automatic ctxt (entry as {serial, ...}: entry) =
  is_automatic_serial (Context.Proof ctxt) serial andalso
  is_none (explicit_cover (Context.Proof ctxt) entry);

fun is_method_only ctxt (entry as {serial, ...}: entry) =
  is_method_only_serial (Context.Proof ctxt) serial andalso
  is_none (explicit_cover (Context.Proof ctxt) entry);

(* Navigation of an entry: the covering explicit registration, otherwise the entry itself. *)
fun navigation_target ctxt (entry as {serial, reg_pos, ...}: entry) =
  (case explicit_cover (Context.Proof ctxt) entry of
     SOME {serial = explicit, reg_pos = explicit_pos, ...} => (explicit, explicit_pos)
   | NONE => (serial, reg_pos));

fun visible_entries context key =
  let
    val thy = Context.theory_of context;
    val stored = stored_registrations context key;
    val (automatic, explicit) =
      List.partition (fn {serial, ...} => is_automatic_serial context serial) stored;
    fun visible (entry as {serial, ...}: entry) =
      is_automatic_serial context serial orelse
      (not (exists (fn general => backend_covers thy general entry) automatic) andalso
       represented_by thy explicit entry);
    fun resolve (entry as {hol_term, source_const, serial, ...}: entry) =
      if not (is_automatic_serial context serial) then entry
      else
        (case explicit_cover_at context key entry of
           SOME {reg_pos, ...} =>
             {hol_term = hol_term, source_const = source_const, reg_pos = reg_pos,
              serial = serial}
         | NONE => entry);
  in map resolve (filter visible stored) end;

\<comment>\<open>Register \<open>rust_name\<close> (in context \<open>kind\<close>) as a notation backend for
  \<open>hol_term\<close>, recording \<open>reg_pos\<close>. CONSes onto the name's registration list.

  The caller allocates one \<open>serial\<close> per \<^emph>\<open>declaration\<close> (not per merge-replay).
  This function only updates data: a local-theory declaration is applied to several contexts, so
  the registering command emits its \<open>def\<close>-side entity markup once through
  \<open>report_registration\<close>. Use sites later emit matching \<open>ref\<close>-side markup pointing
  back here, so jEdit's jump-to-definition lands on the registering command.

  Callers of automatic registrations mark the serial before registering it. Every registration
  is stored unless the same registration (serial and backend) already is, as on a replay, and
  nothing is ever removed, so the stored registrations, like the view above, are a function of the
  registration set, and a theory merge loses no scheme.\<close>
fun register_with_source_serial kind name hol_term source_const
    reg_pos s context =
  let
    val ctxt = Context.proof_of context;
    val key = mk_key kind name;
    val hol_term = singleton (Variable.polymorphic ctxt) hol_term;
    val entry =
      {hol_term = hol_term, source_const = source_const,
       reg_pos = reg_pos, serial = s};
    val existing = stored_registrations context key;
    val _ =
      (case Inttab.lookup (Registration_Keys.get context) s of
         SOME (use as (other, _)) =>
           if other = key then () else serial_reuse_error [use, (key, reg_pos)]
       | NONE => ());
    fun store entries =
      Data.map (Symtab.update (key, entries)) #>
      Registration_Keys.map (Inttab.default (s, (key, reg_pos)));
  in
    if exists (fn old => same_registration (old, entry)) existing then context
    else store (entry :: existing) context
  end;

\<comment>\<open>The \<open>def\<close>-side entity markup of one registering command.\<close>
fun report_registration ctxt name reg_pos s =
  Micro_Rust_Semantic_Navigation.defer_report ctxt reg_pos
    (Position.make_entity_markup {def = true} s notationN (name, reg_pos));

(* Registration from inside a declaration callback, reported per application. *)
fun register_with_source kind name hol_term source_const reg_pos context =
  let val s = serial ()
  in
    report_registration (Context.proof_of context) name reg_pos s;
    register_with_source_serial kind name hol_term source_const reg_pos s context
  end;

fun register kind name hol_term reg_pos =
  register_with_source kind name hol_term NONE reg_pos;

\<comment>\<open>All backends visible for a \<open>(kind, name)\<close>, or \<open>[]\<close> if none. An automatic entry that an
  explicit registration covers keeps its serial and reports the explicit registration's position.\<close>
fun lookups ctxt kind name = visible_entries (Context.Proof ctxt) (mk_key kind name);

\<comment>\<open>Which registered backends a use may dispatch to. A dispatch marker carries a set of filters,
  and every filter of the set applies:
   - \<open>Exclude_Generated\<close>: a turbofish payload is applied as leading arguments, which only
     explicit notations accept, since a generated \<open>urust_fn\<close> has no generic parameters;
   - \<open>Exclude_Method_Only\<close>: a direct call does not reach the method entries of impl members;
   - \<open>Only_Sources\<close>: a path call selecting impls keeps only the entries whose source serial is
     listed (the identities of the selected impls); an empty list leaves no eligible entry.\<close>
datatype backend_filter =
    Exclude_Generated
  | Exclude_Method_Only
  | Only_Sources of serial list;

fun eligible_entry ctxt restriction (entry as {serial, ...}: entry) =
  (case restriction of
     Exclude_Generated => not (is_automatic ctxt entry)
   | Exclude_Method_Only => not (is_method_only ctxt entry)
   | Only_Sources serials => member (op =) serials serial);

fun eligible_entries ctxt filters =
  filter (fn entry => forall (fn restriction => eligible_entry ctxt restriction entry) filters);

fun has_eligible_entries ctxt filters kind name =
  not (null (eligible_entries ctxt filters (lookups ctxt kind name)));

\<comment>\<open>All registered entries, as \<open>(kind, rust_name, entry)\<close> triples (for the
  query command). Splits the composite key back into kind and name; one row
  per backend.\<close>
fun dump ctxt =
  Data.get (Context.Proof ctxt)
  |> Symtab.keys
  |> maps (fn key =>
       (case String.fields (fn ch => ch = #"\000") key of
          [k, n] =>
            map (fn e => (string_to_kind k, n, e)) (visible_entries (Context.Proof ctxt) key)
        | _ => error "malformed micro_rust_notation key"));

end
\<close>

(* ===================================================================== *)
(* Type-directed dispatch for multi-backend notations.                    *)
(*                                                                        *)
(* When a uRust name has >1 backend, the parse phase cannot choose       *)
(* (types are not yet known).  Instead it emits a marker                  *)
(* `urust_dispatch (STR ''<kind>:<name>'')`; a `term_check` phase runs   *)
(* AFTER type inference and resolves the marker to the unique backend    *)
(* whose type unifies with the occurrence.                                *)
(*                                                                        *)
(*   0 candidates  \<rightarrow>  "no backend at type"                              *)
(*   1 candidate   \<rightarrow>  splice it                                         *)
(*   \<ge>2 candidates \<rightarrow>  ambiguous (loud, listing all candidates)          *)
(*                                                                        *)
(* Same loud-on-ambiguity discipline as `adhoc_overloading` (never        *)
(* "last wins").  `urust_dispatch` is one global anchor (merge-stable);   *)
(* per-name identities are STRING tags reconciled by the union-merged     *)
(* `Micro_Rust_Names` table.                                              *)
(* ===================================================================== *)

\<comment>\<open>Plain-identifier dispatch carries a \<^emph>\<open>witness\<close> --- the bare \<^verbatim>\<open>Free name\<close>
  that the source identifier would have been if no notation registration
  existed. The witness travels through HOL's normal binding pipeline, so
  by the term-check phase it has been resolved by Isabelle the same way an
  unmarked occurrence would be (\<^verbatim>\<open>Bound\<close> for \<open>\<lambda>\<close>-bound, \<^verbatim>\<open>Const\<close> for an
  in-scope HOL constant of the same name, \<^verbatim>\<open>Free\<close> for a truly-free
  occurrence). The dispatcher's resolver then prefers the witness over
  the table whenever the witness has bound or constant shape --- this is
  what stops a registered \<^verbatim>\<open>("mask")\<close> from hijacking a
  \<^verbatim>\<open>\<lambda>mask. \<dots> mask \<dots>\<close> use site.

  Path identifiers (\<^verbatim>\<open>Foo::Bar\<close>) cannot be HOL binders, so they have
  no useful witness and use a separate marker.\<close>
\<comment>\<open>Bespoke witness wrapper: a private datatype with two constructors,
  used solely to carry the optional witness inside the dispatch marker.
  Going through a dedicated wrapper rather than HOL's \<^typ>\<open>'a option\<close>
  prevents accidental collision with notation registrations of \<open>Some\<close>,
  \<open>None\<close>, etc. (\<open>Some(x)\<close> at function position has the witness
  \<open>Some\<close> --- which would itself be elaborated by HOL to
  \<^const>\<open>Option.Some\<close> if we used \<^typ>\<open>'a option\<close> as the wrapper, and
  HOL's type inference would then conflate the wrapper-\<open>Some\<close> with the
  witness-\<open>Some\<close>.)\<close>
datatype 'a urust_witness = Witness 'a | NoWitness

\<comment>\<open>The dispatch marker carries a payload term \<open>'x\<close> (an opaque
  carrier for kind/name/terminal-and-qualifier position metadata, built in ML by
  \<open>Micro_Rust_Dispatch.mk_payload\<close>) and an optional witness
  \<open>'y urust_witness\<close>. The result type \<open>'z\<close> is independent so
  the marker's elaboration doesn't get pinned by the witness or
  payload types.\<close>
consts urust_dispatch :: \<open>'x \<Rightarrow> 'y urust_witness \<Rightarrow> 'z\<close>

ML\<open>
structure Micro_Rust_Dispatch = struct

\<comment>\<open>Some registered backends are administrative wrappers around the
  source-level HOL identity that editor navigation should expose. Keep that
  policy in merge-stable theory data rather than recognizing wrapper names in
  the generic dispatch algorithm. The internal registration operation is
  intentionally theory-only: wrapper transparency is global semantic metadata,
  not a proof-context notation declaration.\<close>
structure Backend_Identity_Wrappers = Theory_Data
(
  type T = unit Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (op =);
);

fun register_backend_identity_wrapper name =
  Backend_Identity_Wrappers.map (Symtab.update (name, ()));

fun is_backend_identity_wrapper ctxt name =
  Symtab.defined
    (Backend_Identity_Wrappers.get (Proof_Context.theory_of ctxt))
    name;

type generic_arguments =
  {arguments: (typ * Position.T) list, pos: Position.T};

type generic_source_selection =
  {sources: serial list, kinds: bool option list};

type generic_candidate_sources =
  {name: string, eligible: Micro_Rust_Names.entry list,
   maximal: Micro_Rust_Names.entry list};

type generic_candidate_transform =
  Proof.context -> generic_arguments -> generic_source_selection option -> typ ->
    generic_candidate_sources ->
    (Micro_Rust_Names.entry -> term -> term option);

type sparse_generic_instance =
  {source: serial, arguments: (typ option * Position.T) list, identities: string list};
type sparse_generic_arguments =
  {instances: sparse_generic_instance list, pos: Position.T,
   pending: (string * Position.T) list option};
type sparse_generic_transform =
  Proof.context -> sparse_generic_arguments -> typ -> generic_candidate_sources ->
    (Micro_Rust_Names.entry -> term -> (term * (unit -> unit)) option);
type scoped_sparse_instance =
  {source: serial, target: Micro_Rust_Names.target_selection option,
   arguments: (typ option * Position.T) list option, identities: string list};
type scoped_sparse_arguments =
  {instances: scoped_sparse_instance list, pos: Position.T,
   pending: (string * Position.T) list option};
type scoped_sparse_transform =
  Proof.context -> scoped_sparse_arguments -> typ -> generic_candidate_sources ->
    (Micro_Rust_Names.entry -> term -> (term * (unit -> unit)) option);
type generic_registration =
  {identity: serial, binding: binding, transform: generic_candidate_transform,
   sparse_transform: sparse_generic_transform option,
   inference_check: (Proof.context -> Micro_Rust_Names.entry list -> Position.T -> unit) option};
type generic_registration_state =
  {identity: serial, binding: binding, transform: generic_candidate_transform,
   sparse_transform: sparse_generic_transform option,
   scoped_transform: scoped_sparse_transform option,
   inference_check: (Proof.context -> Micro_Rust_Names.entry list -> Position.T -> unit) option};

structure Generic_Transform_Data = Theory_Data
(
  type T = generic_registration_state option;
  val empty = NONE;
  fun merge (NONE, registration) = registration
    | merge (registration, NONE) = registration
    | merge (SOME (left: generic_registration_state), SOME (right: generic_registration_state)) =
        if #identity left = #identity right then SOME left
        else error ("Conflicting uRust generic candidate transformations" ^
          Position.here_list [Binding.pos_of (#binding left), Binding.pos_of (#binding right)]);
);

(* The delivered record/getter stays exact; the scoped extension belongs to the same owner. *)
structure Generic_Transform =
struct
  type T = generic_registration option;
  fun project (state: generic_registration_state) =
    {identity = #identity state, binding = #binding state, transform = #transform state,
      sparse_transform = #sparse_transform state, inference_check = #inference_check state}
      : generic_registration;
  fun get thy = Option.map project (Generic_Transform_Data.get thy);
  fun put NONE = Generic_Transform_Data.put NONE
    | put (SOME (registration: generic_registration)) = Generic_Transform_Data.map (fn active =>
        SOME {identity = #identity registration, binding = #binding registration,
          transform = #transform registration, sparse_transform = #sparse_transform registration,
          inference_check = #inference_check registration,
          scoped_transform = case active of SOME state =>
            if #identity state = #identity registration then #scoped_transform state else NONE
          | NONE => NONE});
  fun map transform thy = put (transform (get thy)) thy;
end;

fun register_generic_candidate_transform binding transform =
  let val registration = {identity = serial (), binding = binding, transform = transform,
    sparse_transform = NONE, scoped_transform = NONE, inference_check = NONE} in
    Generic_Transform_Data.map (fn NONE => SOME registration
      | SOME (active: generic_registration_state) =>
          error ("uRust generic candidate transformation is already registered" ^
            Position.here_list [Binding.pos_of (#binding active), Binding.pos_of binding]))
  end;

fun register_sparse_generic_candidate_transform transform =
  Generic_Transform_Data.map (fn SOME {identity, binding, transform = old, sparse_transform = NONE, scoped_transform, inference_check} =>
      SOME {identity = identity, binding = binding, transform = old,
        sparse_transform = SOME transform, scoped_transform = scoped_transform, inference_check = inference_check}
    | SOME _ => error "uRust sparse generic candidate transformation is already registered"
    | NONE => error "uRust generic candidate transformation must be registered first");

fun register_scoped_sparse_candidate_transform transform =
  Generic_Transform_Data.map (fn SOME {identity, binding, transform = old, sparse_transform,
        scoped_transform = NONE, inference_check} =>
      SOME {identity = identity, binding = binding, transform = old,
        sparse_transform = sparse_transform, scoped_transform = SOME transform,
        inference_check = inference_check}
    | _ => error "uRust scoped generic candidate transformation cannot be registered");

fun register_generic_inference_check check =
  Generic_Transform_Data.map (fn SOME {identity, binding, transform, sparse_transform, scoped_transform, inference_check = NONE} =>
      SOME {identity = identity, binding = binding, transform = transform,
        sparse_transform = sparse_transform, scoped_transform = scoped_transform, inference_check = SOME check}
    | _ => error "uRust generic inference check cannot be registered");

\<comment>\<open>The marker's payload encodes the registration kind and name together
  with the terminal source position and any qualified-path segment positions
  as a bare \<^verbatim>\<open>Free\<close> with the data packed into the variable's name.
  Using a \<^verbatim>\<open>Free\<close> rather than a HOL \<^typ>\<open>String.literal\<close> avoids the
  ~7n nested-constructor blowup of bit-list literal strings; the
  payload is two heap cells regardless of name length. The sentinel
  prefix keeps the encoded name out of any real namespace.\<close>
val payload_prefix = "_urust_dispatch_payload___";
val payload_sep = String.str (Char.chr 0);

\<comment>\<open>A marker's filter set (\<^ML_type>\<open>Micro_Rust_Names.backend_filter\<close>) is an optional fifth
  payload field: comma-separated filters, where a source filter lists its serials after the
  \<open>sources\<close> tag. The tag \<open>empty_sources\<close> represents an empty selection.
  An unfiltered marker keeps the four-field (or bare-tag) encoding.\<close>
fun encode_filter Micro_Rust_Names.Exclude_Generated = "generated"
  | encode_filter Micro_Rust_Names.Exclude_Method_Only = "method_only"
  | encode_filter (Micro_Rust_Names.Only_Sources []) = "empty_sources"
  | encode_filter (Micro_Rust_Names.Only_Sources serials) =
      space_implode " " ("sources" :: map Value.print_int serials);

fun decode_filter "generated" = SOME Micro_Rust_Names.Exclude_Generated
  | decode_filter "method_only" = SOME Micro_Rust_Names.Exclude_Method_Only
  | decode_filter "empty_sources" = SOME (Micro_Rust_Names.Only_Sources [])
  | decode_filter field =
      (case String.fields (fn c => c = #" ") field of
         "sources" :: serials =>
           if null serials then NONE
           else
             let val parsed = map (try Value.parse_nat) serials in
               if exists is_none parsed then NONE
               else
                 SOME (Micro_Rust_Names.Only_Sources (map the parsed))
             end
       | _ => NONE);

fun encode_filters filters = space_implode "," (map encode_filter filters);

fun decode_filters field =
  if field = "" then NONE
  else
    let val parsed = map decode_filter (String.fields (fn c => c = #",") field) in
      if exists is_none parsed then NONE
      else
        let val filters = map the parsed in
          if length (distinct (op =) filters) = length filters then SOME filters else NONE
        end
    end;

type marker_positions =
  {terminal_pos: Position.T,
   qualifier_positions: Position.T list,
   backend_only_positions: Position.T list};

\<comment>\<open>Payload positions use the shared codec of
  \<^ML_structure>\<open>Micro_Rust_Semantic_Navigation\<close>: encoded positions keep every
  property, including the source file that PIDE needs to place a use-site report,
  and decode to exactly themselves, while the escaped payload name stays
  unqualified for \<^ML>\<open>Syntax_Phases.decode_term\<close>. An unrestricted payload
  without any reported position carries only its tag.\<close>
fun encode_payload_positions filters kind name
    ({terminal_pos, qualifier_positions,
      backend_only_positions} : marker_positions) =
  let
    val tag = Micro_Rust_Names.kind_to_string kind ^ payload_sep ^ name
    val positions =
      terminal_pos :: qualifier_positions @ backend_only_positions
    val with_positions =
      tag ^ payload_sep ^
        string_of_int (length qualifier_positions) ^ payload_sep ^
        Micro_Rust_Semantic_Navigation.encode_positions positions
  in
    Micro_Rust_Semantic_Navigation.escape_payload_name
      (if not (null filters) then with_positions ^ payload_sep ^ encode_filters filters
       else if exists Position.is_reported positions then with_positions
       else tag)
  end;

\<comment>\<open>A payload body with a malformed escape, position field or qualifier count is
  rejected with the dispatch marker's diagnostic.\<close>
fun decode_payload s =
  let
    fun malformed () = error "malformed urust_dispatch payload"
    val parts =
      (case Micro_Rust_Semantic_Navigation.unescape_payload_name s of
         SOME body => String.fields (fn ch => ch = Char.chr 0) body
       | NONE => malformed ())
    fun decode_positions enc =
      (case Micro_Rust_Semantic_Navigation.decode_positions enc of
         SOME decoded => decoded
       | NONE => malformed ())
    fun decoded_positions qualifier_count enc =
      (case (try Value.parse_nat qualifier_count, decode_positions enc) of
         (SOME count, terminal_pos :: rest) =>
           if count > length rest then malformed ()
           else
             {terminal_pos = terminal_pos,
              qualifier_positions = take count rest,
              backend_only_positions = drop count rest}
       | (SOME _, []) =>
           {terminal_pos = Position.none,
            qualifier_positions = [],
            backend_only_positions = []}
       | (NONE, _) => malformed ())
    val (kind_str, name, positions) =
      (case parts of
         [k, n] =>
           (k, n,
            {terminal_pos = Position.none,
             qualifier_positions = [],
             backend_only_positions = []})
       | [k, n, enc] =>
           (case decode_positions enc of
              terminal_pos :: qualifier_positions =>
                (k, n,
                 {terminal_pos = terminal_pos,
                  qualifier_positions = qualifier_positions,
                  backend_only_positions = []})
            | [] =>
                (k, n,
                 {terminal_pos = Position.none,
                  qualifier_positions = [],
                  backend_only_positions = []}))
       | [k, n, qualifier_count, enc] =>
           (k, n, decoded_positions qualifier_count enc)
       | [k, n, qualifier_count, enc, _] =>
           (k, n, decoded_positions qualifier_count enc)
       | _ => malformed ())
    val filters =
      (case parts of
         [_, _, _, _, field] =>
           (case decode_filters field of SOME filters => filters | NONE => malformed ())
       | _ => [])
  in (Micro_Rust_Names.string_to_kind kind_str, name, positions, filters) end;

\<comment>\<open>Build the payload \<^verbatim>\<open>Free\<close> with the encoded data in its name.

  Using \<^verbatim>\<open>Free\<close> rather than \<^verbatim>\<open>Const\<close> matters: the preterm decoder runs
  a namespace lookup on \<^verbatim>\<open>Const\<close> names and raises "Undefined constant"
  when the name doesn't resolve. \<^verbatim>\<open>Free\<close> variables aren't subject to
  that lookup; the decoder accepts the free variable verbatim. The
  sentinel prefix is reserved enough that no user identifier could
  collide with it.\<close>
fun mk_filtered_payload_positions filters kind name positions =
  Free
    (payload_prefix ^ encode_payload_positions filters kind name positions,
     dummyT);

fun mk_payload_positions kind name positions =
  mk_filtered_payload_positions [] kind name positions;

\<comment>\<open>Retain the original single-position payload API for the legacy
  frontend and direct clients. Dedicated-parser qualified paths use
  \<open>mk_marker_positions\<close> below to retain every identifier segment.\<close>
fun mk_payload kind name pos =
  mk_payload_positions kind name
    {terminal_pos = pos,
     qualifier_positions = [],
     backend_only_positions = []};

\<comment>\<open>Recognise the payload \<^verbatim>\<open>Free\<close> and recover
  \<open>(kind, name, marker_positions, filters)\<close>.\<close>
fun dest_plain_payload (Free (s, _)) =
      if String.isPrefix payload_prefix s
      then SOME (decode_payload (String.extract (s, size payload_prefix, NONE)))
      else NONE
  | dest_plain_payload _ = NONE;

val generic_payload_prefix = "_urust_generic_arguments_";
val generic_source_prefix = "_urust_generic_sources_";
val sparse_generic_prefix = "_urust_sparse_generic_sources_";
val scoped_sparse_prefix = "_urust_scoped_generic_sources_";

fun malformed_generic_payload () = error "malformed urust_dispatch generic arguments";

fun generic_position_name positions =
  generic_payload_prefix ^ Micro_Rust_Semantic_Navigation.escape_payload_name
    (Micro_Rust_Semantic_Navigation.encode_positions positions);

fun generic_positions name =
  (case Micro_Rust_Semantic_Navigation.unescape_payload_name
      (String.extract (name, size generic_payload_prefix, NONE)) of
     SOME encoded =>
       (case Micro_Rust_Semantic_Navigation.decode_positions encoded of
          SOME positions => positions
        | NONE => malformed_generic_payload ())
   | NONE => malformed_generic_payload ());

fun generic_source_name ({sources, kinds}: generic_source_selection) =
  let
    fun kind (SOME true) = "t"
      | kind (SOME false) = "c"
      | kind NONE = "n";
  in generic_source_prefix ^ Micro_Rust_Semantic_Navigation.escape_payload_name
    (encode_filter (Micro_Rust_Names.Only_Sources sources) ^ payload_sep ^
      implode (map kind kinds)) end;

fun generic_source_selection name =
  let
    fun kind #"t" = SOME true
      | kind #"c" = SOME false
      | kind #"n" = NONE
      | kind _ = malformed_generic_payload ();
    val encoded = String.extract (name, size generic_source_prefix, NONE);
    val fields =
      (case Micro_Rust_Semantic_Navigation.unescape_payload_name encoded of
         SOME decoded => String.fields (fn ch => ch = Char.chr 0) decoded
       | NONE => malformed_generic_payload ());
  in
    (case fields of
       [sources, kinds] =>
         (case decode_filter sources of
            SOME (Micro_Rust_Names.Only_Sources serials) =>
              {sources = serials, kinds = map kind (String.explode kinds)}
          | _ => malformed_generic_payload ())
     | _ => malformed_generic_payload ())
  end;

fun sparse_generic_name instances pending =
  let
    fun instance ({source, arguments, identities}: sparse_generic_instance) =
      XML.Elem (("instance", [("source", string_of_int source)]),
        map2 (fn (typ, pos) => fn identity =>
          XML.Elem (("slot", [("witness", Bool.toString (is_some typ)),
            ("identity", identity)]), XML.Encode.properties (Position.properties_of pos)))
          arguments identities);
    val sources = case pending of NONE => [] | SOME sources =>
      [XML.Elem (("pending", []), map (fn (text, pos) =>
        XML.Elem (("source", [("text", text)]),
          XML.Encode.properties (Position.properties_of pos))) sources)];
  in sparse_generic_prefix ^ Micro_Rust_Semantic_Navigation.escape_payload_name
    (YXML.string_of_body (map instance instances @ sources)) end;

fun sparse_generic_instances name witnesses =
  let
    fun decode () =
    let
    val encoded = String.extract (name, size sparse_generic_prefix, NONE);
    val body = (case Micro_Rust_Semantic_Navigation.unescape_payload_name encoded of
      SOME text => YXML.parse_body text | NONE => malformed_generic_payload ());
    fun slot (XML.Elem (("slot", attrs), position)) pending =
          let
            fun attr name = the (AList.lookup (op =) attrs name);
            val pos = Position.of_properties (XML.Decode.properties position);
            val (typ, remaining) = case attr "witness" of
                "false" => (NONE, pending)
              | "true" => (SOME (hd pending), tl pending)
              | _ => malformed_generic_payload ();
          in (((typ, pos), attr "identity"), remaining) end
      | slot _ _ = malformed_generic_payload ();
    fun instance (XML.Elem (("instance", [("source", source)]), slots)) pending =
          let val (arguments, remaining) = fold_map slot slots pending
          in ({source = Value.parse_nat source, arguments = map fst arguments,
            identities = map snd arguments}, remaining) end
      | instance _ _ = malformed_generic_payload ();
    fun source (XML.Elem (("source", [("text", text)]), position)) =
          (text, Position.of_properties (XML.Decode.properties position))
      | source _ = malformed_generic_payload ();
    val (body, pending) = case rev body of
        XML.Elem (("pending", []), sources) :: rest => (rev rest, SOME (map source sources))
      | _ => (body, NONE);
    val (instances, remaining) = fold_map instance body witnesses;
    val _ = if null remaining andalso not (null instances) then () else malformed_generic_payload ();
    in (instances, pending) end;
  in
    (case Exn.capture0 decode () of Exn.Res result => result
     | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else malformed_generic_payload ())
  end;

(* Structural metadata carries only neutral constructors. HOL types are separate TYPE leaves,
   so Isabelle transports the selected target and its evidence with the occurrence itself. *)
fun scoped_sparse_encoding ({instances, pending, ...}: scoped_sparse_arguments) =
  let
    open Micro_Rust_Names;
    val types = Unsynchronized.ref ([]: (typ * Position.T) list);
    fun witness pos typ =
      let val index = length (!types); val _ = types := !types @ [(typ, pos)]
      in string_of_int index end;
    fun kind Type_Source = "type" | kind Const_Source = "const";
    fun position pos = XML.Encode.properties (Position.properties_of pos);
    fun path indices = XML.Encode.list XML.Encode.int indices;
    fun head (Primitive_Source name) = ("primitive", name)
      | head (Mapped_Source name) = ("mapped", name)
      | head (Numeric_Source value) = ("numeric", string_of_int value)
      | head Tuple_Source = ("tuple", "") | head Slice_Source = ("slice", "")
      | head Array_Source = ("array", "")
      | head (Pointer_Source mutable) = ("pointer", Bool.toString mutable)
      | head (Reference_Source mutable) = ("reference", Bool.toString mutable)
      | head (Opaque_Source _) = ("opaque", "");
    fun tree pos (Source_Variable ((name, index), k)) = XML.Elem
          (("variable", [("name", name), ("index", string_of_int index), ("kind", kind k)]), [])
      | tree _ (Source_Rigid (identity, k)) = XML.Elem
          (("rigid", [("identity", string_of_int identity), ("kind", kind k)]), [])
      | tree pos (Source_HOL (k, typ)) = XML.Elem
          (("hol", [("kind", kind k), ("witness", witness pos typ)]), [])
      | tree pos (Source_Node (constructor, children)) =
          let val (tag, value) = head constructor
              val opaque = case constructor of Opaque_Source symbols =>
                [XML.Elem (("symbols", []), XML.Encode.list
                  (XML.Encode.pair XML.Encode.string XML.Encode.int) symbols)] | _ => []
          in XML.Elem (("node", [("head", tag), ("value", value)]),
            opaque @ map (tree pos) children) end;
    fun target ({self_type, source, source_identity, evidence, inputs, pos}: target_selection) =
      XML.Elem (("target", [("self", witness pos self_type)]),
        [XML.Elem (("position", []), position pos)] @
        (case source of NONE => [] | SOME source => [XML.Elem (("tree", []), [tree pos source])]) @
        (case source_identity of NONE => [] | SOME token =>
          [XML.Elem (("identity", [("value", token)]), [])]) @
        map (fn (indices, typ) => XML.Elem (("evidence", [("witness", witness pos typ)]), path indices)) evidence @
        map (fn (indices, (text, origin)) => XML.Elem (("input", [("text", text)]),
          [XML.Elem (("path", []), path indices), XML.Elem (("position", []), position origin)])) inputs);
    fun slot ((typ, pos), identity) = XML.Elem (("slot",
      [("witness", case typ of NONE => "" | SOME typ => witness pos typ), ("identity", identity)]), position pos);
    fun instance ({source, target = selected, arguments, identities}: scoped_sparse_instance) =
      XML.Elem (("instance", [("source", string_of_int source)]),
        (case selected of NONE => [] | SOME selected => [target selected]) @
        (case arguments of NONE => [] | SOME arguments =>
          [XML.Elem (("arguments", []), map slot (arguments ~~ identities))]));
    val body = map instance instances @ (case pending of NONE => [] | SOME sources =>
      [XML.Elem (("pending", []), map (fn (text, pos) => XML.Elem
        (("source", [("text", text)]), position pos)) sources)]);
  in (scoped_sparse_prefix ^ Micro_Rust_Semantic_Navigation.escape_payload_name
    (YXML.string_of_body body), !types) end;

fun scoped_sparse_instances name witnesses =
  let
    open Micro_Rust_Names;
    fun decode () =
      let
        fun attr attrs name = the (AList.lookup (op =) attrs name);
        fun natural attrs name = Value.parse_nat (attr attrs name);
        fun witness attrs name = nth witnesses (natural attrs name);
        fun kind attrs = case attr attrs "kind" of "type" => Type_Source
          | "const" => Const_Source | _ => malformed_generic_payload ();
        fun position body = Position.of_properties (XML.Decode.properties body);
        fun path body = XML.Decode.list XML.Decode.int body;
        fun tree (XML.Elem (("variable", attrs), [])) =
              Source_Variable ((attr attrs "name", natural attrs "index"), kind attrs)
          | tree (XML.Elem (("rigid", attrs), [])) = Source_Rigid (natural attrs "identity", kind attrs)
          | tree (XML.Elem (("hol", attrs), [])) = Source_HOL (kind attrs, witness attrs "witness")
          | tree (XML.Elem (("node", attrs), body)) =
              let
                val value = attr attrs "value";
                val (head, children) = case attr attrs "head" of
                    "primitive" => (Primitive_Source value, body)
                  | "mapped" => (Mapped_Source value, body)
                  | "numeric" => (Numeric_Source (Value.parse_int value), body)
                  | "tuple" => (Tuple_Source, body) | "slice" => (Slice_Source, body)
                  | "array" => (Array_Source, body)
                  | "pointer" => (Pointer_Source (Value.parse_bool value), body)
                  | "reference" => (Reference_Source (Value.parse_bool value), body)
                  | "opaque" => (case body of XML.Elem (("symbols", []), symbols) :: rest =>
                      (Opaque_Source (XML.Decode.list
                        (XML.Decode.pair XML.Decode.string XML.Decode.int) symbols), rest)
                    | _ => malformed_generic_payload ())
                  | _ => malformed_generic_payload ()
              in Source_Node (head, map tree children) end
          | tree _ = malformed_generic_payload ();
        fun target (XML.Elem (("target", attrs), body)) =
              let
                fun part tag = map_filter (fn XML.Elem ((name, attributes), content) =>
                  if name = tag then SOME (attributes, content) else NONE | _ => NONE) body;
                val pos = position (#2 (the_single (part "position")));
                val source = case part "tree" of [] => NONE
                  | [(_, [source])] => SOME (tree source) | _ => malformed_generic_payload ();
                val identity = case part "identity" of [] => NONE
                  | [(attrs, [])] => SOME (attr attrs "value") | _ => malformed_generic_payload ();
                val evidence = map (fn (attrs, content) => (path content, witness attrs "witness")) (part "evidence");
                fun input (attrs, [XML.Elem (("path", []), indices), XML.Elem (("position", []), origin)]) =
                      (path indices, (attr attrs "text", position origin))
                  | input _ = malformed_generic_payload ();
              in {self_type = witness attrs "self", source = source, source_identity = identity,
                evidence = evidence, inputs = map input (part "input"), pos = pos}: target_selection end
          | target _ = malformed_generic_payload ();
        fun slot (XML.Elem (("slot", attrs), pos)) =
              ((case attr attrs "witness" of "" => NONE | _ => SOME (witness attrs "witness"),
                position pos), attr attrs "identity")
          | slot _ = malformed_generic_payload ();
        fun instance (XML.Elem (("instance", attrs), body)) =
              let
                val (selected, body) = case body of (t as XML.Elem (("target", _), _)) :: rest =>
                    (SOME (target t), rest) | _ => (NONE, body);
                val (arguments, identities) = case body of [] => (NONE, [])
                  | [XML.Elem (("arguments", []), slots)] =>
                      let val slots = map slot slots in (SOME (map fst slots), map snd slots) end
                  | _ => malformed_generic_payload ();
              in {source = natural attrs "source", target = selected,
                arguments = arguments, identities = identities}: scoped_sparse_instance end
          | instance _ = malformed_generic_payload ();
        fun pending_source (XML.Elem (("source", attrs), pos)) = (attr attrs "text", position pos)
          | pending_source _ = malformed_generic_payload ();
        val body = (case Micro_Rust_Semantic_Navigation.unescape_payload_name
            (String.extract (name, size scoped_sparse_prefix, NONE)) of
              SOME text => YXML.parse_body text | NONE => malformed_generic_payload ());
        val (body, pending) = case rev body of XML.Elem (("pending", []), sources) :: rest =>
            (rev rest, SOME (map pending_source sources)) | _ => (body, NONE);
        val instances = map instance body;
        val _ = if not (null instances) andalso null (duplicates (op =) (map #source instances))
          then () else malformed_generic_payload ();
      in (instances, pending) end;
  in case Exn.capture0 decode () of Exn.Res result => result
    | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else malformed_generic_payload () end;

fun read_scoped_generic_payload payload =
  let
    fun witnesses (Const (\<^const_name>\<open>Pair\<close>, _) $ witness $ rest) =
          Logic.dest_type witness :: witnesses rest
      | witnesses (Const (\<^const_name>\<open>Unity\<close>, _)) = []
      | witnesses _ = malformed_generic_payload ();
    fun tagged term =
      Term.exists_subterm (fn Free (name, _) =>
        String.isPrefix generic_payload_prefix name orelse
          String.isPrefix generic_source_prefix name orelse
          String.isPrefix sparse_generic_prefix name orelse
          String.isPrefix scoped_sparse_prefix name | _ => false) term;
    fun selection (term as Const (\<^const_name>\<open>Pair\<close>, _) $ Free (name, _) $ types) =
          if String.isPrefix generic_source_prefix name
          then (SOME (generic_source_selection name), NONE, NONE, types)
          else if String.isPrefix sparse_generic_prefix name then (NONE, SOME name, NONE, types)
          else if String.isPrefix scoped_sparse_prefix name then (NONE, NONE, SOME name, types)
          else (NONE, NONE, NONE, term)
      | selection types = (NONE, NONE, NONE, types);
  in
    (case payload of
       Const (\<^const_name>\<open>Pair\<close>, _) $ base $
         (Const (\<^const_name>\<open>Pair\<close>, _) $ Free (name, _) $ types) =>
           if String.isPrefix generic_payload_prefix name then
             let
               val _ = if is_some (dest_plain_payload base) then ()
                 else malformed_generic_payload ();
               val positions = generic_positions name;
               val (sources0, sparse_name, scoped_name, witnesses_term) = selection types;
               val arguments = witnesses witnesses_term handle TERM _ => malformed_generic_payload ();
               val instances = Option.map (fn name => sparse_generic_instances name arguments) sparse_name;
               val scoped = Option.map (fn name => scoped_sparse_instances name arguments) scoped_name;
               val sources0 = case scoped of NONE => sources0
                 | SOME (instances, _) => SOME {sources = map #source instances,
                     kinds = replicate (length arguments) NONE};
               val sources = case instances of NONE => sources0
                 | SOME (instances, _) => SOME {sources = map #source instances,
                     kinds = replicate (length arguments) NONE};
               val _ =
                 (case sources of
                    SOME {kinds, ...} =>
                      if length kinds = length arguments then () else malformed_generic_payload ()
                  | NONE => ());
             in
               (case positions of
                  pos :: argument_positions =>
                    if length arguments = length argument_positions then
                      SOME {base = base,
                        arguments = {pos = pos, arguments = arguments ~~ argument_positions},
                        sources = sources,
                        sparse = Option.map (fn (instances, pending) =>
                          {instances = instances, pos = pos, pending = pending}) instances,
                        scoped = Option.map (fn (instances, pending) =>
                          {instances = instances, pos = pos, pending = pending}) scoped}
                    else malformed_generic_payload ()
                | [] => malformed_generic_payload ())
             end
           else if tagged payload then malformed_generic_payload () else NONE
     | _ => if tagged payload then malformed_generic_payload () else NONE)
  end;

fun read_generic_payload payload =
  Option.map (fn {base, arguments, sources, sparse, ...} =>
    {base = base, arguments = arguments, sources = sources, sparse = sparse})
      (read_scoped_generic_payload payload);

fun dest_generic_payload payload =
  Option.map (fn {base, arguments, ...} => (base, arguments)) (read_scoped_generic_payload payload);

fun dest_payload payload =
  dest_plain_payload
    (case dest_generic_payload payload of SOME (base, _) => base | NONE => payload);

fun map_payload_base transform payload =
  (case dest_generic_payload payload of
     SOME _ =>
       (case payload of
          pair $ base $ metadata => pair $ transform base $ metadata
        | _ => malformed_generic_payload ())
   | NONE => transform payload);

\<comment>\<open>Construct a marker \<open>urust_dispatch (STR ''<tag>'') opt\<close>:

   - Plain id: \<open>opt = SOME witness\<close>, where \<open>witness\<close> is the bare
     \<open>Free name\<close> the source identifier would have parsed to. HOL
     elaboration resolves the witness through normal binding (so a
     lambda-bound \<open>name\<close> becomes \<open>Bound n\<close>, an in-scope HOL constant becomes
     \<open>Const\<close>, etc.); the term-check resolver inspects the elaborated
     witness and prefers it over a table lookup whenever the witness
     resolved to a binder or a HOL constant.

   - Path id: \<open>opt = NONE\<close>. Path names cannot be HOL binders, so there
     is no useful witness to carry.

  The two type variables \<open>'a\<close> (witness) and \<open>'b\<close> (result) are
  independent --- this is essential. If they were collapsed, the
  witness's elaborated type would force the marker's result type, and a
  registered name like \<open>Some\<close> (which HOL elaborates to
  \<^const>\<open>Option.Some\<close>) at function position would fail type unification
  before the term-check resolver had a chance to pick the registered
  function-kind backend.\<close>
fun mk_marker_term opt_witness =
  let
    val opt_term =
      (case opt_witness of
         SOME w => Const (\<^const_name>\<open>Witness\<close>, dummyT) $ w
       | NONE => Const (\<^const_name>\<open>NoWitness\<close>, dummyT))
  in fn payload =>
       Const (\<^const_name>\<open>urust_dispatch\<close>, dummyT) $ payload $ opt_term
  end;

\<comment>\<open>Build the marker with the witness term unmodified --- positions
  on the witness are preserved. After \<^ML>\<open>Syntax_Trans.abs_tr\<close>
  binds an enclosing same-named binder, the witness becomes
  \<^verbatim>\<open>_constrain $ Bound n $ <pos>\<close>, and \<^verbatim>\<open>decode_term\<close> emits paired
  binder def/use markup automatically.

  The trade-off: when the witness elaborates to a HOL constant
  (e.g. \<^verbatim>\<open>Free "Some"\<close> becomes \<^const>\<open>Option.Some\<close>), the decoder ALSO
  emits \<^verbatim>\<open>Markup.const\<close> at the user's source token, which can stack
  visibly with the \<open>micro_rust_notation\<close> entity ref \<open>resolve\<close> emits.\<close>
fun mk_marker_positions kind name terminal_pos qualifier_positions witness =
  mk_marker_term (SOME witness)
    (mk_payload_positions kind name
      {terminal_pos = terminal_pos,
       qualifier_positions = qualifier_positions,
       backend_only_positions = []});

\<comment>\<open>Registered macro markers keep source identifiers on notation
  declaration navigation while retaining a distinct punctuation position for
  the selected backend constant. Backends without a named constant identity
  leave those backend-only positions unlinked.\<close>
fun mk_marker_positions_with_backend_targets
    kind name terminal_pos qualifier_positions
    backend_only_positions witness =
  mk_marker_term (SOME witness)
    (mk_payload_positions kind name
      {terminal_pos = terminal_pos,
       qualifier_positions = qualifier_positions,
       backend_only_positions = backend_only_positions});

fun mk_marker kind name pos witness =
  mk_marker_positions kind name pos [] witness;

fun with_generic_arguments ({arguments, pos}: generic_arguments) =
  let
    val metadata = Free (generic_position_name (pos :: map snd arguments), dummyT);
    val witnesses = fold_rev (fn (typ, _) => fn rest =>
      HOLogic.mk_prod (Logic.mk_type typ, rest)) arguments HOLogic.unit;
    fun wrap (Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ opt) =
          (case dest_payload payload of
             SOME (Micro_Rust_Names.NFunction, _, _, _) =>
               if is_some (dest_generic_payload payload) then malformed_generic_payload ()
               else Const (\<^const_name>\<open>urust_dispatch\<close>, T) $
                 HOLogic.mk_prod (payload, HOLogic.mk_prod (metadata, witnesses)) $ opt
           | SOME _ => malformed_generic_payload ()
           | NONE => Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ wrap opt)
      | wrap (t $ u) = wrap t $ wrap u
      | wrap (Abs (name, T, body)) = Abs (name, T, wrap body)
      | wrap term = term;
  in wrap end;

fun marker_generic_arguments (Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ payload $ _) =
      Option.mapPartial (fn {arguments, sparse, scoped, ...} =>
        if is_some sparse orelse is_some scoped then NONE else SOME arguments) (read_scoped_generic_payload payload)
  | marker_generic_arguments _ = NONE;

fun marker_sparse_generic_arguments (Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ payload $ _) =
      Option.mapPartial #sparse (read_scoped_generic_payload payload)
  | marker_sparse_generic_arguments _ = NONE;

fun with_sparse_generic_arguments ({instances, pos, pending}: sparse_generic_arguments) term =
  let
    val _ = if not (null instances) andalso
      null (duplicates (op =) (map #source instances)) andalso
      forall (fn {arguments, identities, ...} => length arguments = length identities) instances
      then () else malformed_generic_payload ();
    val arguments = maps (map_filter (fn (typ, position) =>
      Option.map (fn typ => (typ, position)) typ) o #arguments) instances;
    val metadata = Free (sparse_generic_name instances pending, dummyT);
    fun wrap (Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ witness) =
          (case read_scoped_generic_payload payload of
             SOME _ => (case payload of _ $ base $ (_ $ positions $ types) =>
                 Const (\<^const_name>\<open>urust_dispatch\<close>, T) $
                   HOLogic.mk_prod (base, HOLogic.mk_prod (positions,
                     HOLogic.mk_prod (metadata, types))) $ witness
               | _ => malformed_generic_payload ())
           | NONE => Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ wrap witness)
      | wrap (left $ right) = wrap left $ wrap right
      | wrap (Abs (name, T, body)) = Abs (name, T, wrap body)
      | wrap term = term;
  in wrap (with_generic_arguments {arguments = arguments, pos = pos} term) end;

fun marker_scoped_sparse_arguments (Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ payload $ _) =
      Option.mapPartial #scoped (read_scoped_generic_payload payload)
  | marker_scoped_sparse_arguments _ = NONE;

fun with_scoped_sparse_arguments (arguments as {instances, pos, ...}: scoped_sparse_arguments) term =
  let
    val _ = if not (null instances) andalso null (duplicates (op =) (map #source instances)) andalso
      forall (fn {arguments, identities, ...} => case arguments of NONE => null identities
        | SOME arguments => length arguments = length identities) instances
      then () else malformed_generic_payload ();
    val (name, types) = scoped_sparse_encoding arguments;
    val metadata = Free (name, dummyT);
    fun wrap (Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ witness) =
          (case read_scoped_generic_payload payload of
             SOME _ => (case payload of _ $ base $ (_ $ positions $ types) =>
                 Const (\<^const_name>\<open>urust_dispatch\<close>, T) $
                   HOLogic.mk_prod (base, HOLogic.mk_prod (positions,
                     HOLogic.mk_prod (metadata, types))) $ witness
               | _ => malformed_generic_payload ())
           | NONE => Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ wrap witness)
      | wrap (left $ right) = wrap left $ wrap right
      | wrap (Abs (name, T, body)) = Abs (name, T, wrap body)
      | wrap term = term;
  in wrap (with_generic_arguments {arguments = types, pos = pos} term) end;

fun marker_generic_source_selection (Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ payload $ _) =
      Option.mapPartial #sources (read_scoped_generic_payload payload)
  | marker_generic_source_selection _ = NONE;

fun with_generic_source_arguments selection (arguments: generic_arguments) term =
  let
    val _ = if length (#kinds selection) = length (#arguments arguments) then ()
      else malformed_generic_payload ();
    val metadata = Free (generic_source_name selection, dummyT);
    fun wrap (Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ witness) =
          (case read_scoped_generic_payload payload of
             SOME _ =>
               (case payload of
                  _ $ base $ (_ $ positions $ types) =>
                    Const (\<^const_name>\<open>urust_dispatch\<close>, T) $
                      HOLogic.mk_prod (base,
                        HOLogic.mk_prod (positions, HOLogic.mk_prod (metadata, types))) $
                      witness
                | _ => malformed_generic_payload ())
           | NONE => Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ wrap witness)
      | wrap (left $ right) = wrap left $ wrap right
      | wrap (Abs (name, T, body)) = Abs (name, T, wrap body)
      | wrap term = term;
  in wrap (with_generic_arguments arguments term) end;

\<comment>\<open>Recognise a marker. Returns \<open>SOME ((kind, name, positions),
  opt_witness, T)\<close> where \<open>opt_witness\<close> is \<open>SOME witness\<close> for plain ids
  (the elaborated witness term) and \<open>NONE\<close> for paths, and \<open>T\<close> is the
  marker's inferred result type at this occurrence.\<close>
\<comment>\<open>Type-aware destructure: requires the marker's outer type to be a
  proper function chain so we can extract the result type. Returns
  \<open>NONE\<close> on a malformed payload, on a non-witness opt-payload, or
  when the marker's type is still \<open>dummyT\<close>-shaped (i.e. before type
  inference); callers in early phases should use
  \<^verbatim>\<open>dest_marker_untyped\<close> instead.\<close>
fun dest_marker (Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ opt) =
      ((case dest_payload payload of
          NONE => NONE
        | SOME tag =>
            let
              val result_T = Term.range_type (Term.range_type T)
              val witness =
                (case opt of
                   Const (\<^const_name>\<open>Witness\<close>, _) $ w => SOME w
                 | Const (\<^const_name>\<open>NoWitness\<close>, _) => NONE
                 | _ => raise Match)
            in SOME (tag, witness, result_T) end)
       handle Match => NONE | TYPE _ => NONE)
  | dest_marker _ = NONE;

\<comment>\<open>Type-blind destructure: only inspects the term skeleton (payload
  and witness shape). Used in the early \<^verbatim>\<open>~1\<close> phase, before type
  inference, where the marker's type is still \<open>dummyT\<close> and
  \<^verbatim>\<open>dest_marker\<close> would bail out.\<close>
fun dest_marker_untyped (Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ payload $ opt) =
      ((case dest_payload payload of
          NONE => NONE
        | SOME tag =>
            let
              val witness =
                (case opt of
                   Const (\<^const_name>\<open>Witness\<close>, _) $ w => SOME w
                 | Const (\<^const_name>\<open>NoWitness\<close>, _) => NONE
                 | _ => raise Match)
            in SOME (tag, witness) end)
       handle Match => NONE)
  | dest_marker_untyped _ = NONE;

\<comment>\<open>Add a filter set to every marker in a call head. Filters accumulate: a marker that is
  already restricted keeps its filters, so restrictions from different call forms compose.\<close>
fun restrict_backends filters =
  let
    fun add_filter restriction existing =
      if member (op =) existing restriction then existing else existing @ [restriction];
    fun restrict (Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ opt) =
          (case dest_payload payload of
             SOME (kind, name, positions, existing) =>
               Const (\<^const_name>\<open>urust_dispatch\<close>, T) $
                  map_payload_base
                    (K (mk_filtered_payload_positions (fold add_filter filters existing)
                      kind name positions)) payload $ opt
           | NONE =>
               Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ restrict opt)
      | restrict (t $ u) = restrict t $ restrict u
      | restrict (Abs (x, T, body)) = Abs (x, T, restrict body)
      | restrict t = t;
  in restrict end;

\<comment>\<open>Restrict every marker in a call head to explicit backends, before a turbofish
  payload is applied to it.\<close>
val exclude_generated_backends = restrict_backends [Micro_Rust_Names.Exclude_Generated];

\<comment>\<open>Can backend type \<open>T'\<close> serve an occurrence of type \<open>T\<close>?
  (Mirrors \<open>adhoc_overloading.ML\<close>: rename the backend's tvars away
  from the occurrence and try \<open>typ_unify\<close>.)\<close>
fun unifiable_types ctxt (T, T') =
  let
    val thy = Proof_Context.theory_of ctxt;
    val maxidx1 = Term.maxidx_of_typ T;
    val T'' = Logic.incr_tvar (maxidx1 + 1) T';
    val maxidx2 = Term.maxidx_typ T'' maxidx1;
  in can (Sign.typ_unify thy (T, T'')) (Vartab.empty, maxidx2) end;

\<comment>\<open>Try to unify a backend term against an occurrence type \<open>T\<close>; on
  success, return the backend term with its schematic TVars
  instantiated by the unifier. Mirrors the shift-and-unify dance of
  \<open>unifiable_types\<close> but also \<^emph>\<open>applies the substitution\<close> so the
  resulting term has no orphan schematics --- otherwise \<open>check_term\<close>'s
  later "Illegal schematic type variable" guard fires.\<close>
fun unify_fresh_and_instantiate ctxt T t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val T' = fastype_of t;
    val maxidx = Term.maxidx_typ T' (Term.maxidx_of_typ T);
  in
    case try (Sign.typ_unify thy (T, T')) (Vartab.empty, maxidx) of
      NONE => NONE
    | SOME (tyenv, _) =>
        let
          val subst = Term.map_types (Envir.subst_type tyenv)
         in SOME (subst t) end
  end;

fun unify_and_instantiate ctxt T t =
  unify_fresh_and_instantiate ctxt T
    (Term.map_types (Logic.incr_tvar (Term.maxidx_of_typ T + 1)) t);

\<comment>\<open>Candidate backends retain their complete types: interpreted concrete types and
  ambient fixed type variables constrain dispatch. Only unfixed variables are generalized; each
  occurrence imports fresh inference parameters, so signature and effect variables remain independent
  across calls. Erasing every internal type would discard a locale interpretation's specialization.\<close>
type dispatch_candidate =
  {entry: Micro_Rust_Names.entry, term: term};

fun fresh_backend ctxt term =
  singleton (Variable.polymorphic ctxt) term
  |> Term_Subst.zero_var_indexes
  |> Term.map_types (Logic.incr_tvar (serial ()) #> Type_Infer.paramify_vars);

fun eligible_entries ctxt filters kind name =
  Micro_Rust_Names.eligible_entries ctxt filters (Micro_Rust_Names.lookups ctxt kind name);

fun generic_source_filters NONE filters = filters
  | generic_source_filters (SOME {sources, ...}: generic_source_selection option) filters =
      filters @ [Micro_Rust_Names.Only_Sources sources];

fun filtered_candidates_with_scoped_generic_effects ctxt filters kind name T generic_arguments selection sparse scoped =
  let
    val entries = eligible_entries ctxt filters kind name;
    val selected = Micro_Rust_Names.eligible_entries ctxt
      (generic_source_filters selection []) entries;
    (* Theory union may bring together a generic backend and its specialization. Prefer the
       covering scheme before instantiation, including when effect channels remain unconstrained. *)
    val maximal = filter (fn entry => not (exists (fn other =>
      not (Micro_Rust_Names.reg_eq (other, entry)) andalso
      Micro_Rust_Names.backend_covers (Proof_Context.theory_of ctxt) other entry) selected)) selected;
    val transform =
      (case scoped of
         SOME arguments => (case Generic_Transform_Data.get (Proof_Context.theory_of ctxt) of
           SOME {scoped_transform = SOME transform, ...} =>
             SOME (transform ctxt arguments T {name = name, eligible = entries, maximal = maximal})
         | _ => error "uRust scoped generic candidate transformation is not registered")
       | NONE => (case sparse of
         SOME arguments => (case Generic_Transform_Data.get (Proof_Context.theory_of ctxt) of
           SOME {sparse_transform = SOME transform, ...} =>
             SOME (transform ctxt arguments T {name = name, eligible = entries, maximal = maximal})
         | _ => error "uRust sparse generic candidate transformation is not registered")
       | NONE => (case generic_arguments of
         NONE => NONE
       | SOME arguments =>
           (case Generic_Transform_Data.get (Proof_Context.theory_of ctxt) of
              SOME {transform, ...} =>
                let val apply = transform ctxt arguments selection T
                  {name = name, eligible = entries, maximal = maximal}
                in SOME (fn entry => fn candidate =>
                  Option.map (fn term => (term, fn () => ())) (apply entry candidate)) end
            | NONE => error "uRust generic candidate transformation is not registered"))));
    fun instantiate entry hol_term =
      (case transform of
         NONE => Option.map (fn term => (term, fn () => ()))
           (unify_and_instantiate ctxt T (fresh_backend ctxt hol_term))
       | SOME apply =>
           let
             val arguments = case scoped of
                 SOME arguments => #2 (scoped_sparse_encoding arguments)
               | NONE => (case sparse of
                 SOME {instances, ...} => maps (map_filter (fn (typ, pos) =>
                   Option.map (fn typ => (typ, pos)) typ) o #arguments) instances
               | NONE => #arguments (the generic_arguments));
             val caller_max = fold (Term.maxidx_typ o fst) arguments
               (Int.max (Variable.maxidx_of ctxt, Term.maxidx_of_typ T));
             val candidate = fresh_backend ctxt hol_term
               |> Term.map_types (Logic.incr_tvar (caller_max + 1));
           in Option.mapPartial (fn (term, commit) =>
             Option.map (fn term => (term, commit))
               (unify_fresh_and_instantiate ctxt T term)) (apply entry candidate) end);
  in
    maximal
    |> sort (int_ord o apply2 #serial)
    |> map_filter (fn entry as {hol_term, ...} =>
         Option.map (fn (backend, commit) =>
           ({entry = entry, term = Type.constraint T backend}, commit))
            (instantiate entry hol_term))
    |> distinct (fn ((left: dispatch_candidate, _), (right: dispatch_candidate, _)) =>
         Term.aconv (apply2 Micro_Rust_Names.normalized_backend (#term left, #term right)))
  end;

fun filtered_candidates_with_all_generic_effects ctxt filters kind name T arguments selection sparse =
  filtered_candidates_with_scoped_generic_effects ctxt filters kind name T arguments selection sparse NONE;

fun filtered_candidates_with_all_generics ctxt filters kind name T arguments selection sparse =
  map fst (filtered_candidates_with_all_generic_effects ctxt filters kind name T arguments selection sparse);

fun filtered_candidates_with_source_generics ctxt filters kind name T arguments selection =
  filtered_candidates_with_all_generics ctxt filters kind name T arguments selection NONE;

fun filtered_candidates_with_generics ctxt filters kind name T generic_arguments =
  filtered_candidates_with_source_generics ctxt filters kind name T generic_arguments NONE;

fun filtered_candidates ctxt filters kind name T =
  filtered_candidates_with_generics ctxt filters kind name T NONE;

fun candidates ctxt kind name T = filtered_candidates ctxt [] kind name T;

\<comment>\<open>Look up a HOL constant by user-visible name. Returns
  \<open>SOME (full_name, declared_type)\<close> if the name resolves to a constant in \<open>ctxt\<close>,
  including an abbreviation such as a locale's local abbreviation of its constant, and
  \<open>NONE\<close> otherwise (free variable, unknown name, etc.). Used by \<open>shadow_check\<close>
  below.\<close>
fun lookup_hol_const ctxt name =
  (case try (Proof_Context.read_const {proper = true, strict = false} ctxt) name of
     SOME (Const (full_name, T)) => SOME (full_name, T)
   | _ => NONE);

\<comment>\<open>If a \<^emph>\<open>registered\<close> uRust notation \<open>name\<close> shares its name with an
  \<^emph>\<open>unregistered\<close> HOL constant in scope whose type has matching kind
  (call-position vs \<open>_ \<Rightarrow> _ function_body\<close>, or field-position vs
  \<open>_ lens\<close>), surface it as a shadow:

   - by default, errors are suppressed (\<open>suppress_error\<close>) and the
     shadow is reported at warning level only;
   - per-name \<open>[shadow_err]\<close> re-enables the error;
   - per-name \<open>[shadow_no_warn]\<close> silences the warning too.

  Literal-position uses are never shadow-checked --- shadowing on bare
  values produces too much noise (e.g. \<^const>\<open>Some\<close> at \<open>'a \<Rightarrow> 'a option\<close>
  would shadow every uRust \<^verbatim>\<open>Some\<close> use without any real ambiguity).
  Cross-kind clashes are likewise ignored (a call-shaped HOL constant
  is unrelated to a field-position uRust use of the same name, and
  vice versa).

  Only fires when there is at least one registered backend that unifies;
  if dispatch has nothing to say, shadowing is irrelevant. A constant that denotes a registered
  backend is not a shadow: an automatically registered function, an explicit registration of a
  constant under its own name, a locale's local abbreviation of either, or an abbreviation whose
  expansion is the backend (\<open>is_registered_backend\<close>).\<close>
fun shadow_check ctxt kind name T pos have_backend is_registered_backend =
  if not have_backend then () else
  if kind = Micro_Rust_Names.NLiteral then () else
  let val { suppress_warning, suppress_error } =
        Micro_Rust_Names.shadow_opts ctxt kind name
  in
  (case lookup_hol_const ctxt name of
    NONE => ()
  | SOME (full_name, const_T) =>
      if Micro_Rust_Names.infer_kind_of_type const_T <> kind then ()
      else if is_registered_backend (full_name, const_T) then ()
      else
        let
          \<comment>\<open>Render the constant via \<^ML>\<open>Syntax.pretty_term\<close> so name-space markup
            (\<^verbatim>\<open>Name_Space.markup\<close> + \<^verbatim>\<open>Markup.const\<close>) is attached and ctrl-click
            jumps to the defining \<^verbatim>\<open>definition\<close>/\<^verbatim>\<open>fun\<close>/\<^verbatim>\<open>primrec\<close> command.\<close>
          val pretty_const = Syntax.pretty_term ctxt (Const (full_name, const_T))
          val msg = Pretty.string_of (Pretty.chunks
            [Pretty.str ("Ambiguous uRust notation \<open>" ^ name ^
               "\<close>: a registered backend matches type"),
             Pretty.block [Pretty.str "  ", Syntax.pretty_typ ctxt T],
             Pretty.block
               [Pretty.str "but the HOL constant ", pretty_const,
                Pretty.str " of type"],
             Pretty.block [Pretty.str "  ", Syntax.pretty_typ ctxt const_T],
             Pretty.str "also matches.",
             Pretty.str ("Either rename the registered backend or pick a different rust_name,"),
             Pretty.str ((if suppress_error then
                            "or run \<open>micro_rust_notation (config) [shadow_no_warn] \""
                              ^ name ^ "\"\<close> to silence."
                          else
                            "or run \<open>micro_rust_notation (config) [shadow_no_err] \""
                              ^ name ^ "\"\<close>.")
                         ^ Position.here pos)])
        in
          if not suppress_error then error msg
          else if not suppress_warning then warning msg
          else ()
        end)
  end;

\<comment>\<open>Should the elaborated witness shadow the table registration? Only in
  one case: a \<^bold>\<open>literal\<close>-position occurrence (bare \<open>x\<close>) whose witness is a
  \<^verbatim>\<open>Bound\<close> --- i.e. a \<open>let\<close>/lambda-bound local, which correctly wins, mirroring
  Rust's lexical scoping (\<open>let x = \<dots>; x\<close>).

  In \<^bold>\<open>field\<close> (\<open>x.f\<close>) and \<^bold>\<open>function\<close> (\<open>f(\<dots>)\<close> / \<open>x.f(\<dots>)\<close>) positions a
  marker's registered notation \<^emph>\<open>always\<close> wins over its witness: e.g. the field
  selector \<open>.f\<close> in \<open>x.f\<close> must not be shadowed by a same-named closure parameter
  \<open>|f| \<dots>\<close>, and a method call \<open>x.f(f)\<close> must invoke the \<open>.f\<close> method even when the
  argument \<open>f\<close> is a same-named local binder. This is the marker's own policy, inherited from
  the removed legacy frontend, where a locally bound callable \<open>let f = \<dots>; f(\<dots>)\<close> could not
  shadow a registered function notation. The dedicated parser resolves lexical names itself:
  after block-import shadowing it selects a local in literal and direct single-segment call
  positions before constructing any marker, and never consults locals for method heads or
  fields. Its binders are fresh internal Frees, so they never capture a source-spelled witness.

  \<^verbatim>\<open>Const\<close> witnesses never win either, since a backend is often registered
  precisely to override a same-named HOL constant (e.g. \<^verbatim>\<open>("Some")\<close> for
  \<^verbatim>\<open>lift_fun1 Some\<close>, where the witness \<^verbatim>\<open>Free "Some"\<close> elaborates to
  \<^const>\<open>Option.Some\<close>).\<close>
fun witness_takes_precedence Micro_Rust_Names.NLiteral (Bound _) = true
  | witness_takes_precedence _ _ = false;

\<comment>\<open>Resolve all dispatch markers in a term, in the typed check phase.
  The marker has shape \<open>urust_dispatch (STR ''<tag>'') opt\<close> where \<open>opt\<close>
  is either \<open>Some witness\<close> (plain id; HOL elaboration has resolved the
  witness to \<open>Bound\<close>/\<open>Const\<close>/\<open>Free\<close> through normal binding) or \<open>None\<close>
  (path id; no witness available).

  Resolution rules (lambda binders already consumed at stage \<^verbatim>\<open>~1\<close> by
  \<open>resolve_bound\<close>, so any surviving witness here is \<open>Free\<close>/\<open>Const\<close>):
   - exactly one type-compatible candidate: splice it in, report backend
     information first, then report every notation declaration once with the
     selected registration last on the terminal and all retained qualifiers;
   - multiple candidates: leave the ambiguous marker for \<open>reject_unresolved\<close>;
   - no candidates: the name IS registered (a marker would not exist
     otherwise) but no backend type-unifies with the occurrence, so call
     \<open>no_match_error\<close> (a hard error; see there). We do NOT silently demote
     to the witness free variable --- that would mask genuine arity/type
     mismatches like \<open>Foo::mk()\<close> against a binary backend.\<close>
\<comment>\<open>Early phase, runs at stage \<^verbatim>\<open>~1\<close> before type inference. Replaces a
  marker with its witness ONLY if the witness is a \<^verbatim>\<open>Bound\<close> --- meaning
  the surrounding \<open>_abs\<close> machinery has already resolved a lambda binder of
  the same name. This must happen before \<open>adhoc_overloading\<close> runs (at
  stage 0), so that lambda-bound uses do not leave a polymorphic marker
  behind that breaks operator resolution.

  Uses \<^verbatim>\<open>dest_marker_untyped\<close> --- at this stage the marker's outer
  type is still \<open>dummyT\<close>, so \<^verbatim>\<open>dest_marker\<close> would silently fail.\<close>
\<comment>\<open>When the witness wins (the marker resolves to a \<^verbatim>\<open>Bound\<close>), we
  also need to emit \<^verbatim>\<open>Markup.bound\<close> at the user's source position.
  Without this the use site has no markup at all --- the position
  carried by the user's source token went into the marker's payload
  string (not into a \<open>_constrain\<close> wrapper around the witness, because
  we strip those to suppress the const-promotion leak), so the
  decoder never sees a position-tagged \<open>Bound\<close> to attach binder-use
  markup to. We emit it ourselves from the recovered tag position.\<close>
fun resolve_bound ctxt =
  let
    fun go t =
      (case dest_marker_untyped t of
         SOME ((kind, _, positions, _), SOME w) =>
           if witness_takes_precedence kind w then
             let
               val _ =
                 Context_Position.report ctxt
                   (#terminal_pos positions) Markup.bound
             in w end
           else t
       | _ =>
           (case t of
              u $ v => go u $ go v
            | Abs (x, S, b) => Abs (x, S, go b)
            | _ => t));
  in map go end;

\<comment>\<open>Late phase, runs at stage \<^verbatim>\<open>1\<close> after type inference. Markers that
  survived \<^verbatim>\<open>resolve_bound\<close> here have a witness that is NOT a lambda binder
  (so \<^verbatim>\<open>Free\<close> or \<^verbatim>\<open>Const\<close>), or are path markers (no witness). Now we
  have full types and can do the typed table lookup.\<close>
fun emit_notation_entries_at_pos
    (ctxt : Proof.context) (name : string)
    (entries : Micro_Rust_Names.entry list)
    (pos : Position.T) : unit =
  if not (Position.is_reported pos) then ()
  else
    app
        (fn entry =>
          let val (serial, reg_pos) = Micro_Rust_Names.navigation_target ctxt entry
          in
            Micro_Rust_Semantic_Navigation.defer_report ctxt pos
              (Position.make_entity_markup {def = false} serial
                Micro_Rust_Names.notationN (name, reg_pos))
          end)
        entries;

fun selected_entry_last
    (selected : Micro_Rust_Names.entry)
    (entries : Micro_Rust_Names.entry list) =
  filter
    (fn (entry : Micro_Rust_Names.entry) =>
      #serial entry <> #serial selected)
    entries @ [selected];

\<comment>\<open>Emit only ref-side notation entities at \<open>pos\<close>, one for every
  registered backend under \<open>(kind, name)\<close>. This is the compatibility
  primitive for clients that do not yet have a typed selected entry.\<close>
fun emit_notation_entity_at_pos
    (ctxt : Proof.context)
    (kind : Micro_Rust_Names.ctxt_kind)
    (name : string)
    (pos : Position.T) : unit =
  emit_notation_entries_at_pos ctxt name
    (Micro_Rust_Names.lookups ctxt kind name) pos;

\<comment>\<open>Typed dispatch and validated constructor patterns use the selected
  variant: every declaration reference is retained exactly once, while the
  selected declaration is reported last so it is the ordinary jEdit
  navigation destination.\<close>
fun emit_selected_notation_entities_at_pos ctxt kind name selected pos =
  emit_notation_entries_at_pos ctxt name
    (selected_entry_last selected
      (Micro_Rust_Names.lookups ctxt kind name))
    pos;

\<comment>\<open>Emit terminal backend markup at \<open>pos\<close> for every registered
  backend under \<open>(kind, name)\<close>: \<^verbatim>\<open>Markup.keyword3\<close> styling and,
  when available, a
  \<^verbatim>\<open>Name_Space.markup\<close> target for the backend's source-level
  identity. Applied wrappers registered through
  \<open>register_backend_identity_wrapper\<close> are transparent for that target: the
  wrapped term's head constant is used, while a wrapped lambda, free term, or
  other unnamed expression emits no misleading constant entity. Styling
  remains attached to the notation occurrence. Selected notation references
  are emitted separately after these backend reports. The selected-use path is
  called by \<open>resolve\<close> when a marker is actually replaced by a registered
  backend, and by constructor-pattern resolution only after exact
  registration, constructor identity, and arity or field validation have
  succeeded. It is never called when the witness wins. This stops markup from
  leaking onto an identifier whose witness ends up being a lambda binder
  (e.g. \<open>let x = \<dots>; x\<close> where \<open>x\<close> is also a registered notation).\<close>
fun backend_identity_constant ctxt
    ({hol_term, source_const, ...} : Micro_Rust_Names.entry) =
  let
    fun head_const t =
      (case Term.strip_comb t of
         (Const (c, _), wrapped :: _) =>
           if is_backend_identity_wrapper ctxt c
           then head_const wrapped
           else SOME c
       | (Const (c, _), []) => SOME c
       | _ => NONE)
  in
    (case source_const of
       SOME source =>
         (case Term_Position.strip_positions source of
            Const (c, _) => SOME c
          | _ => NONE)
     | NONE =>
         head_const (Term_Position.strip_positions hol_term))
  end;

\<comment>\<open>Does a same-named HOL constant denote one of the registered backends? Abbreviations,
  including a locale's local abbreviation of its constant, are compared after expansion, and the
  whole term must match: a partial application or a wrapper of the constant remains a shadow.\<close>
fun denotes_registered_backend entries ctxt (full_name, const_T) =
  let
    val expanded = Proof_Context.expand_abbrevs ctxt (Const (full_name, const_T))
  in
    exists (fn ({hol_term, ...} : Micro_Rust_Names.entry) =>
        Term.aconv_untyped (Term_Position.strip_positions hol_term, expanded))
      entries
  end;

fun emit_backend_markup_at_pos ctxt kind name pos =
  if not (Position.is_reported pos) then ()
  else
    let
      val entries = Micro_Rust_Names.lookups ctxt kind name
      fun report_one
          (entry as {hol_term, source_const, ...} :
            Micro_Rust_Names.entry) =
        let
          val had_named_head =
            (case source_const of
               SOME (Const _) => true
             | _ =>
                 (case
                     Term.strip_comb
                       (Term_Position.strip_positions hol_term) of
                    (Const _, _) => true
                  | _ => false))
          val constant_markup =
            (case backend_identity_constant ctxt entry of
               SOME c =>
                 [Name_Space.markup
                    (Consts.space_of (Proof_Context.consts_of ctxt)) c]
             | NONE => [])
          val style_markup =
            if had_named_head then [Markup.keyword3] else []
        in
          app
            (Micro_Rust_Semantic_Navigation.defer_report ctxt pos)
            (constant_markup @ style_markup)
        end
    in
      app report_one entries
    end;

\<comment>\<open>Backend-only source positions, currently the separate \<open>!\<close>
  of a registered macro, receive native navigation to only the backend chosen
  by typed dispatch. The ordinary lexical role markup remains in place, and an
  arbitrary or lambda backend deliberately adds no constant target.\<close>
fun emit_selected_backend_target_at_pos ctxt
    (entry : Micro_Rust_Names.entry) pos =
  if not (Position.is_reported pos) then ()
  else
    (case backend_identity_constant ctxt entry of
       SOME c =>
         List.app
           (Micro_Rust_Semantic_Navigation.defer_report ctxt pos)
           [Name_Space.markup
              (Consts.space_of (Proof_Context.consts_of ctxt)) c,
            Markup.const]
     | NONE => ());

\<comment>\<open>Compatibility single-position reporter. Backend identities and
  styling precede notation references, but no typed declaration is
  prioritized because this API does not receive one.\<close>
fun emit_use_markup_at_pos ctxt kind name pos =
  (emit_backend_markup_at_pos ctxt kind name pos;
   emit_notation_entity_at_pos ctxt kind name pos);

\<comment>\<open>Complete selected-use reporter for dedicated-parser dispatch markers.
  The terminal first receives every existing backend identity and style.
  Every terminal and qualifier token then receives all declaration
  references exactly once with the selected declaration last.\<close>
fun emit_selected_use_markup_at_positions ctxt kind name selected
    ({terminal_pos, qualifier_positions,
      backend_only_positions} : marker_positions) =
  (emit_backend_markup_at_pos ctxt kind name terminal_pos;
   emit_selected_notation_entities_at_pos
     ctxt kind name selected terminal_pos;
   List.app
     (emit_selected_notation_entities_at_pos
       ctxt kind name selected)
     qualifier_positions;
   List.app
     (emit_selected_backend_target_at_pos ctxt selected)
     backend_only_positions);

\<comment>\<open>A marker only exists because \<open>lookup_id_tr\<close> found a registration for
  \<open>(kind, name)\<close> (it emits nothing otherwise). So by the time \<open>resolve\<close>
  runs --- with lambda binders already consumed by \<open>resolve_bound\<close> at stage
  \<^verbatim>\<open>~1\<close> --- an empty candidate set means the name \<^emph>\<open>is\<close> registered but
  \<^bold>\<open>no backend's type unifies\<close> with the occurrence type \<open>T\<close>. That is a
  genuine error (e.g. \<open>Foo::mk()\<close> --- a no-arg call ---
  against a backend of type \<open>'a \<Rightarrow> 'b \<Rightarrow> _ function_body\<close>),
  not a reason to silently demote the name to a free variable. We report
  it loudly, showing the occurrence type and every registered backend
  with its type, so the arity/type mismatch is obvious.\<close>
fun filter_notes filters =
  if member (op =) filters Micro_Rust_Names.Exclude_Generated
  then [Pretty.str "Generic arguments exclude generated functions, which take none."]
  else [];

fun no_match_error ctxt filters kind name pos T =
  error (Pretty.string_of (Pretty.chunks
    ([Pretty.block [Pretty.str ("uRust notation \<open>" ^ name ^
       "\<close> is registered, but no backend matches the use-site type "),
       Syntax.pretty_typ ctxt T, Pretty.str (Position.here pos)],
      Pretty.big_list "registered backends (none type-compatible here):"
       (map (fn { hol_term, ... } : Micro_Rust_Names.entry =>
               Pretty.block [Syntax.pretty_term ctxt hol_term, Pretty.str " :: ",
                             Syntax.pretty_typ ctxt (fastype_of hol_term)])
          (eligible_entries ctxt filters kind name))] @
     filter_notes filters)));

fun resolve ctxt =
  let
    fun go t =
      (case dest_marker t of
         SOME ((kind, name, positions, filters), opt_witness, T) =>
           let
             val pos = #terminal_pos positions
             val selection = marker_generic_source_selection t
             val actual_filters = generic_source_filters selection filters
             val effects = filtered_candidates_with_scoped_generic_effects ctxt filters kind name T
               (marker_generic_arguments t) selection (marker_sparse_generic_arguments t)
               (marker_scoped_sparse_arguments t)
             val cands = map fst effects
             val _ = if exists (fn {entry, ...}: dispatch_candidate =>
                 Micro_Rust_Names.method_requires_source_identity ctxt (#serial entry)) cands then
               error ("urust: method receiver has no source identity; use an explicit associated path" ^
                 Position.here pos) else ();
             val _ = if kind = Micro_Rust_Names.NFunction andalso
                 is_none (marker_generic_arguments t) andalso
                 is_none (marker_sparse_generic_arguments t) andalso
                 is_none (marker_scoped_sparse_arguments t) then
               (case Generic_Transform_Data.get (Proof_Context.theory_of ctxt) of
                  SOME {inference_check = SOME check, ...} => check ctxt (map #entry cands) pos
                | _ => ()) else ();
             val _ =
               shadow_check ctxt kind name T pos (not (null cands))
                 (denotes_registered_backend (Micro_Rust_Names.lookups ctxt kind name) ctxt)
             fun select ({entry, term} : dispatch_candidate) =
               (let val commit = #2 (the (find_first
                  (fn ({entry = selected, term = selected_term}, _) =>
                    #serial selected = #serial entry andalso selected_term aconv term) effects))
                in commit () end;
                emit_selected_use_markup_at_positions ctxt kind name entry positions;
                term)
           in
             (case (opt_witness, cands) of
                (SOME w, _) =>
                  if witness_takes_precedence kind w then w \<comment>\<open>binder wins, no markup\<close>
                  else
                    (case cands of
                       [single] => select single
                     | [] => no_match_error ctxt actual_filters kind name pos T
                     | _ => t \<comment>\<open>ambiguous: leave for \<open>reject_unresolved\<close>\<close>)
              | (NONE, [single]) => select single
              | (NONE, []) => no_match_error ctxt actual_filters kind name pos T
              | (NONE, _) => t)
           end
       | NONE =>
           (case t of
              u $ v => go u $ go v
            | Abs (x, S, b) => Abs (x, S, go b)
            | _ => t));
  in map go end;

\<comment>\<open>After resolution, any surviving marker is genuinely ambiguous (two or more
  unifying backends); report it loudly, listing the candidates.\<close>
fun reject_unresolved ctxt =
  let
    fun check t =
      (case dest_marker t of
         SOME ((kind, name, positions, filters), _, T) =>
           let val pos = #terminal_pos positions
           in
           error (Pretty.string_of (Pretty.chunks
             [Pretty.block [Pretty.str ("Ambiguous uRust notation \<open>" ^ name ^
                "\<close> at type "), Syntax.pretty_typ ctxt T,
                Pretty.str (Position.here pos)],
              Pretty.big_list "candidate backends:"
                (map (Syntax.pretty_term ctxt o #hol_term)
                   (eligible_entries ctxt
                     (generic_source_filters (marker_generic_source_selection t) filters)
                     kind name))]))
           end
       | NONE =>
           (case t of u $ v => (check u; check v) | Abs (_, _, b) => check b | _ => ()));
  in app check end;

\<comment>\<open>Install the two check phases (only fire when at least one marker is
  present, so this is free for marker-less terms). Phase 0 resolves; phase
  1 rejects leftover/ambiguous.\<close>
\<comment>\<open>Run at negative priority so we resolve markers \<^emph>\<open>before\<close>
  \<^verbatim>\<open>adhoc_overloading\<close>'s check (which lives at priority 0). Otherwise
  a use site like \<open>shdw + mask\<close> --- where \<open>+\<close> is adhoc-overloaded
  \<^verbatim>\<open>urust_add\<close> --- would fail adhoc resolution before our marker had a
  chance to splice in the registered backend (or fall back to the
  lambda-bound witness), because the marker carries a polymorphic result
  type that adhoc-overloading cannot disambiguate.\<close>
val _ = Context.>>
  (Syntax_Phases.term_check ~1 "urust_dispatch_bind"
     (fn ctxt => resolve_bound ctxt)
   #> Syntax_Phases.term_check 0 "urust_dispatch"
        (fn ctxt => resolve ctxt)
   #> Syntax_Phases.term_check 1 "urust_dispatch_unresolved"
        (fn ctxt => fn ts => (reject_unresolved ctxt ts; ts)));

end
\<close>

(* ===================================================================== *)
(* Outer-syntax command for registering and configuring uRust notations.  *)
(*                                                                        *)
(* Single command, three modifier flavours:                               *)
(*                                                                        *)
(*   micro_rust_notation                <hol_term> ("<rust_name>")        *)
(*     -- kind auto-inferred from the HOL term's type                     *)
(*                                                                        *)
(*   micro_rust_notation (literal)      <hol_term> ("<rust_name>")        *)
(*   micro_rust_notation (call)         <hol_term> ("<rust_name>")        *)
(*   micro_rust_notation (field)        <hol_term> ("<rust_name>")        *)
(*     -- forces the kind; validates the HOL term's type and errors      *)
(*        out if it doesn't fit (call: needs `_ \<Rightarrow> _ function_body`,     *)
(*        field: needs `_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ focus`).                            *)
(*                                                                        *)
(*   micro_rust_notation (config) [<mode>] "name1" "name2" ...            *)
(*     -- shadow-check configuration. Modes:                              *)
(*          shadow_warn / shadow_no_warn / shadow_err / shadow_no_err     *)
(*        (each toggles one bit; the orthogonal bit is preserved.)       *)
(*        Empty name list applies to the global default.                  *)
(*                                                                        *)
(* `print_micro_rust_notations` (separate diag command) lists every       *)
(* registered notation.                                                   *)
(* ===================================================================== *)

ML\<open>
structure Micro_Rust_Notation_Cmd = struct

\<comment>\<open>Validate that a forced kind is consistent with the term's type. Fail
  loudly if not. (Auto-inferred kind never fails this check by
  construction.)\<close>
fun check_forced_kind kind ctxt t =
  let
    val T = fastype_of t
    val inferred = Micro_Rust_Names.infer_kind_of_type T
  in
    if kind = Micro_Rust_Names.NLiteral
      orelse kind = inferred
    then ()
    else
      error (Pretty.string_of (Pretty.chunks
        [Pretty.block [Pretty.str ("micro_rust_notation (" ^
           Micro_Rust_Names.kind_to_string kind ^ "): forced kind does not match\
           \ the registered term's type."),
         Pretty.brk 1, Pretty.str "Term: ", Syntax.pretty_term ctxt t],
         Pretty.block [Pretty.str "Type: ", Syntax.pretty_typ ctxt T]]))
  end;

\<comment>\<open>A Rust notation name is an identifier path when it consists of one or
  more identifier segments separated by exactly \<open>::\<close>. Parser-aware commands
  may use this shared predicate when validating names before registration.\<close>
fun is_identifier_path name =
  let
    val segments = String.tokens (fn c => c = #":") name
  in
    not (null segments)
      andalso space_implode "::" segments = name
      andalso forall Symbol_Pos.is_identifier segments
  end;

fun do_register kind_opt (hol_src, (rust_name, rust_pos)) lthy =
  let
    val t0 = Syntax.read_term lthy hol_src
    val source_const =
      (case
          try
            (Proof_Context.read_const
              {proper = true, strict = false} lthy)
            hol_src of
         SOME (constant as Const _) => SOME constant
       | _ => NONE)
    val registration_serial = serial ();
    val kind =
      case kind_opt of
        SOME k => (check_forced_kind k lthy t0; k)
      | NONE => Micro_Rust_Names.infer_kind_of_type (fastype_of t0)
    (* A bare key self stays available for a literal, an ordinary HOL value. *)
    val _ =
      (case Micro_Rust_Names.reserved_key_segment
          {bare_self = kind = Micro_Rust_Names.NLiteral} rust_name of
         SOME segment =>
           error ("micro_rust_notation: " ^ Micro_Rust_Names.reserved_key_message segment ^
             Position.here rust_pos)
       | NONE => ())
  in
    lthy
    |> Local_Theory.declaration {pervasive=false, syntax=true, pos=Position.none}
      (fn phi =>
        Micro_Rust_Names.register_with_source_serial kind rust_name
          (Morphism.term phi t0)
          (Option.map (Morphism.term phi) source_const)
          rust_pos registration_serial)
    |> tap (fn completed =>
      Micro_Rust_Names.report_registration completed rust_name rust_pos registration_serial)
  end;

\<comment>\<open>Config sub-command: parse \<open>[mode] "name"+\<close> and update the
  shadow-opt-out table. An empty name list updates the default.\<close>
val parse_shadow_mode : Micro_Rust_Names.shadow_bit parser =
  Parse.$$$ "[" |--
    (   Args.$$$ "shadow_warn"    >> K (Micro_Rust_Names.Set_Suppress_Warning false)
     || Args.$$$ "shadow_no_warn" >> K (Micro_Rust_Names.Set_Suppress_Warning true)
     || Args.$$$ "shadow_err"     >> K (Micro_Rust_Names.Set_Suppress_Error false)
     || Args.$$$ "shadow_no_err"  >> K (Micro_Rust_Names.Set_Suppress_Error true))
    --| Parse.$$$ "]";

val parse_names : string list parser =
  Scan.repeat (Parse.position Parse.string >> #1);

val all_kinds =
  [Micro_Rust_Names.NLiteral, Micro_Rust_Names.NFunction, Micro_Rust_Names.NField];

fun do_config (bit, names) lthy =
  lthy |> Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none}
    (fn _ => fold (fn k => Micro_Rust_Names.set_shadow_bit k names bit) all_kinds);

\<comment>\<open>Payload for the registration sub-commands: a HOL term followed by
  the rust-side name (positional, for markup).\<close>
val parse_payload =
  Parse.term -- Parse.position (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")");

\<comment>\<open>Top-level dispatch on the optional \<open>(\<dots>)\<close> modifier:
     absent selects auto-inferred registration;
     \<open>(literal)\<close> selects a forced literal;
     \<open>(call)\<close> selects a forced function (the keyword \<open>function\<close> is taken
                    by HOL globally, so we use \<open>call\<close>)
     \<open>(field)\<close> selects a forced field;
     \<open>(config)\<close> selects the shadow-check configuration sub-command.
  Each branch parses its own remainder of the line.\<close>
val parse_cmd : (local_theory -> local_theory) parser =
  let
    val parse_register_with_kind =
      parse_payload >> (fn p => fn k => do_register (SOME k) p)
  in
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
          |-- parse_shadow_mode -- parse_names
          >> do_config)
    || (parse_payload >> do_register NONE)
  end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>micro_rust_notation\<close>
    "register a uRust notation (auto / forced kind) or configure shadow checks"
    parse_cmd;

end
\<close>


ML\<open>
\<comment>\<open>Query command: prints every registered notation as
  \<open><rust> \<longmapsto> <hol> (context[, tags])\<close>, with the HOL term printed via
  \<open>Syntax.pretty_term\<close>. The tags mark automatic registrations as \<open>generated\<close> and method
  entries of impl members as \<open>method-only\<close>.\<close>
structure Micro_Rust_Notation_Print =
struct

fun entry_tags ctxt entry =
  (if Micro_Rust_Names.is_automatic ctxt entry then ["generated"] else []) @
  (if Micro_Rust_Names.is_method_only ctxt entry then ["method-only"] else []);

fun pretty_entry ctxt (kind, rust, entry as { hol_term, ... } : Micro_Rust_Names.entry) =
  Pretty.block
    [Pretty.str rust, Pretty.str " \<longmapsto> ",
     Syntax.pretty_term ctxt hol_term,
     Pretty.str ("  (" ^
       commas (Micro_Rust_Names.kind_to_string kind :: entry_tags ctxt entry) ^ ")")];

fun pretty_notations ctxt =
  (case Micro_Rust_Names.dump ctxt of
     [] => Pretty.str "no uRust name notations registered"
   | entries => Pretty.big_list "uRust name notations:" (map (pretty_entry ctxt) entries));

end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_micro_rust_notations\<close>
    "list all registered uRust name notations"
    (Scan.succeed (Toplevel.keep (fn st =>
      Pretty.writeln (Micro_Rust_Notation_Print.pretty_notations (Toplevel.context_of st)))));
\<close>


(* ===================================================================== *)
(* Smoke tests                                                            *)
(* ===================================================================== *)

experiment
begin

definition test_my_some_a :: \<open>nat \<Rightarrow> nat option\<close> where
  \<open>test_my_some_a x = Some x\<close>

definition test_my_some_b :: \<open>bool \<Rightarrow> bool option\<close> where
  \<open>test_my_some_b b = Some b\<close>

\<comment>\<open>Single backend, kind forced via \<open>(literal)\<close>. The HOL constant's
  type is \<open>nat \<Rightarrow> nat option\<close> (no \<open>function_body\<close>, no \<open>lens\<close>) so the
  auto-inferred kind would also be \<open>literal\<close>; the modifier here is
  purely to exercise the parser branch.\<close>
micro_rust_notation (literal) test_my_some_a ("MySome")

\<comment>\<open>Multi-backend, no modifier: kind auto-inferred from the term's
  type. Same name as above; the typed term-check phase picks exactly
  one per occurrence (or reports ambiguity if both unify).\<close>
micro_rust_notation test_my_some_b ("MySome")

\<comment>\<open>Field-position registration: as a smoke test we don't have a real
  lens fixture in this experiment, so we register the same
  \<open>literal\<close>-shaped \<open>test_my_some_a\<close> under a field name with no kind
  modifier (auto-infer falls back to \<open>literal\<close>). For a real
  field-typed backend, see \<^verbatim>\<open>register_lens_with_micro_rust_from\<close> in
  \<^file>\<open>Micro_Rust_Parser_Target.thy\<close>.\<close>
micro_rust_notation test_my_some_a ("a_field")

print_micro_rust_notations

\<comment>\<open>Direct exercise of the dispatch term-check phase: a marker constrained
  at type \<open>nat \<Rightarrow> nat option\<close> resolves to \<open>test_my_some_a\<close>; constrained
  at \<open>bool \<Rightarrow> bool option\<close> resolves to \<open>test_my_some_b\<close>. The check fires
  only when the marker survives type inference, so we use \<open>typ\<close>
  ascriptions.\<close>
term \<open>(urust_dispatch (STR ''literal:MySome'') NoWitness :: nat \<Rightarrow> nat option)\<close>
term \<open>(urust_dispatch (STR ''literal:MySome'') NoWitness :: bool \<Rightarrow> bool option)\<close>

\<comment>\<open>Ambiguity: register two same-typed backends under the same name and
  show the loud error.  We use a comment-only assertion --- attempting
  the lookup at \<open>id\<close>'s shared schematic type would unify with both.\<close>
definition test_id_a :: \<open>nat \<Rightarrow> nat\<close> where \<open>test_id_a x = x\<close>
definition test_id_b :: \<open>nat \<Rightarrow> nat\<close> where \<open>test_id_b x = x\<close>

micro_rust_notation test_id_a ("Ambig")
micro_rust_notation test_id_b ("Ambig")

\<comment>\<open>Both backends have type \<open>nat \<Rightarrow> nat\<close>; an occurrence at \<open>nat \<Rightarrow> nat\<close>
  unifies with both, so resolution errors loudly listing candidates:

    Ambiguous uRust notation \<open>Ambig\<close> at the shared function type
    candidate backends:
      \<open>test_id_b\<close>
      \<open>test_id_a\<close>

  Uncomment the line below to reproduce; left commented so the file
  builds clean.\<close>
\<comment>\<open>term \<open>(urust_dispatch (STR ''function:Ambig'') :: nat \<Rightarrow> nat)\<close>\<close>

end

end
