theory Parser_Impl_Case_Compiler
  imports Parser_Impl_Resolution
begin

section\<open> Case compilation \<close>

ML\<open>
signature URUST_CASE_COMPILER =
sig
  type binding_signature = string * Position.T
  val signature_name: binding_signature -> string
  val signature_position: binding_signature -> Position.T

  datatype case_pattern =
      Case_Wild
    | Case_Bind of binding_signature
    | Case_Value of term * Position.T
    | Case_Node of
        {head: term, family_hint: (string * term list) option, arguments: case_pattern list}
    | Case_Tuple of case_pattern list
    | Case_Alias of binding_signature * (term -> term) * case_pattern * Position.T
    | Case_Constraint of typ * Position.T * case_pattern
    | Case_Range of URust_AST.range_kind * term * term * Position.T
    | Case_Slice_Suffix of case_pattern
    | Case_Navigated of Position.T list * case_pattern

  datatype case_compilation_mode =
      Ordinary_Case_Compilation
    | Source_Match_Compilation

  type case_arm =
    {patterns: case_pattern list,
     environment: URust_Resolution.environment,
     binders: term list,
     source_guard: (term * Position.T) option,
     body: term}

  val constrain_pattern_abstraction: typ -> Position.T -> term -> term
  val compile_case:
    case_compilation_mode ->
      Proof.context ->
      Position.T list ->
      term option ->
      term ->
      case_arm list ->
      term
end
\<close>

ML\<open>
(*
  URust_Case_Compiler turns prepared case patterns into the established shallow case terms.
  URust_Patterns resolves source patterns, validates and allocates their binders, and builds one
  case_arm per source arm; everything after that point lives here: the case_pattern IR, clause
  patterns, structural analysis, the ordered decision compiler, case-term emission, and the
  stage-99 urust_pattern_typing check phase that erases the pattern typing witnesses.

  A binding_signature is a source binder name with its position; URust_Patterns shares this type
  and its two projections. A case_pattern is one prepared or-alternative. Its binders are already
  allocated in the arm environment, and every Case_Node head is the exact term supplied by
  preparation. constrain_pattern_abstraction constrains a pattern abstraction to a scrutinee type
  at a source position; URust_Patterns also uses it for direct bindings.

  compile_case takes the compilation mode, the source positions that scope the match navigation,
  an optional explicit fallback, the scrutinee, and the source-ordered case arms. The contract is
  the one URust_Patterns.compile_case documents, which delegates here.
*)
structure URust_Case_Compiler :> URUST_CASE_COMPILER =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure R = URust_Resolution
  structure Navigation = Micro_Rust_Semantic_Navigation

  datatype case_compilation_mode =
      Ordinary_Case_Compilation
    | Source_Match_Compilation

  type binding_signature = string * Position.T

  fun signature_name (name, _) = name
  fun signature_position (_, pos) = pos

  fun constrain_pattern_abstraction typ pos abstraction =
    Type.constraint (typ --> dummyT) (T.source_position pos abstraction)

  (* A Case_Node head is used exactly as given: R.constructor_term of a resolved constructor (it
     can be a type-instantiated Const shared with the typing witness) or a list constructor of a
     slice. family_hint is the resolver's family, if any. Tuples stay Case_Tuple at this level. *)
  datatype case_pattern =
      Case_Wild
    | Case_Bind of binding_signature
    | Case_Value of term * Position.T
    | Case_Node of
        {head: term, family_hint: (string * term list) option, arguments: case_pattern list}
    | Case_Tuple of case_pattern list
    | Case_Alias of binding_signature * (term -> term) * case_pattern * Position.T
    | Case_Constraint of typ * Position.T * case_pattern
    | Case_Range of range_kind * term * term * Position.T
    | Case_Slice_Suffix of case_pattern
    | Case_Navigated of Position.T list * case_pattern

  (* The pattern of one case clause. Tuples are expanded into Pair/TNil chains, and Clause_Generated
     names the temporary of a nested match or of an opened region leaf. *)
  datatype clause_pattern =
      Clause_Wild
    | Clause_Binder of binding_signature
    | Clause_Generated of term
    | Clause_Node of
        {head: term, family_hint: (string * term list) option, arguments: clause_pattern list}

  datatype case_pattern_tree =
      Pattern_Slot of int
    | Pattern_Application of term * case_pattern_tree list

  (* One source arm: its or-alternatives, the arm environment, the Frees allocated for the arm's
     binders (the typing witness captures them in this order), and the guard and body already
     lowered in that environment. *)
  type case_arm =
    {patterns: case_pattern list,
     environment: R.environment,
     binders: term list,
     source_guard: (term * Position.T) option,
     body: term}

  fun tuple_clause [] =
        Clause_Node {head = T.tuple_nil_constructor, family_hint = NONE, arguments = []}
    | tuple_clause (argument :: rest) =
        Clause_Node
          {head = T.pair_constructor, family_hint = NONE, arguments = [argument, tuple_clause rest]}

  (* The clause form of a case pattern: navigation is dropped and tuples become Pair/TNil chains.
     Values, ranges, slice suffixes, aliases and type constraints have no clause form; normalization
     replaces them by generated tests and scopes first, and case_pattern_structurally_total strips
     or rejects them before converting its spine. *)
  fun clause_of_case_pattern pattern =
    (case pattern of
       Case_Wild => Clause_Wild
     | Case_Bind binder_sig => Clause_Binder binder_sig
     | Case_Value (_, pos) =>
         error ("urust_expr: internal unnormalized value pattern" ^ Position.here pos)
     | Case_Node {head, family_hint, arguments} =>
         Clause_Node
           {head = head, family_hint = family_hint,
            arguments = map clause_of_case_pattern arguments}
     | Case_Tuple arguments => tuple_clause (map clause_of_case_pattern arguments)
     | Case_Alias (binder_sig, _, _, _) =>
         error ("urust_expr: internal unnormalized alias pattern" ^
           Position.here (signature_position binder_sig))
     | Case_Constraint (_, pos, _) =>
         error ("urust_expr: internal unnormalized pattern type constraint" ^ Position.here pos)
     | Case_Range (_, _, _, pos) =>
         error ("urust_expr: internal unnormalized range pattern" ^ Position.here pos)
     | Case_Slice_Suffix _ => error "urust_expr: internal unnormalized slice suffix pattern"
     | Case_Navigated (_, inner) => clause_of_case_pattern inner)

  fun instantiate_pattern arguments tree =
    (case tree of
       Pattern_Slot index => nth arguments index
     | Pattern_Application (constructor, nested) =>
         Term.list_comb (constructor, map (instantiate_pattern arguments) nested))

  fun abstract_slots wrap slots make_inner =
    let
      val count = length slots
      val arguments =
        map_index (fn (_, SOME free) => free | (index, NONE) => Bound (count - 1 - index)) slots
    in
      fold_rev (fn slot => fn term =>
          wrap
            (case slot of
               SOME free => Term.lambda free term
             | NONE => R.anonymous_abstraction term))
        slots (make_inner arguments)
    end

  fun bind_clause_pattern ctxt environment pattern =
    let
      fun add_slot slot (slots_rev, count) = (Pattern_Slot count, (slot :: slots_rev, count + 1))

      fun walk Clause_Wild state = add_slot NONE state
        | walk (Clause_Binder binder_sig) state =
            let
              val name = signature_name binder_sig
              val pos = signature_position binder_sig
            in
              (case R.use_pattern_binder ctxt environment (name, pos) of
                 SOME free => add_slot (SOME free) state
               | NONE =>
                   error ("urust_expr: internal unregistered case binder " ^ quote name ^
                     Position.here pos))
            end
        | walk (Clause_Generated free) state = add_slot (SOME free) state
        | walk (Clause_Node {head, arguments, ...}) state =
            let val (trees, state') = fold_map walk arguments state
            in (Pattern_Application (head, trees), state') end

      val (tree, (slots_rev, _)) = walk pattern ([], 0)
    in
      fn body =>
        abstract_slots Case_Term_Backend.case_abstraction (rev slots_rev)
          (fn arguments =>
            Case_Term_Backend.case_element (instantiate_pattern arguments tree) body)
    end

  fun requires_nested_match pattern =
    (case pattern of
       Case_Value _ => true
     | Case_Alias _ => true
     | Case_Constraint _ => true
     | Case_Range _ => true
     | Case_Slice_Suffix _ => true
     | Case_Navigated (_, inner) => requires_nested_match inner
     | Case_Node {arguments, ...} => List.exists requires_nested_match arguments
     | Case_Tuple arguments => List.exists requires_nested_match arguments
     | _ => false)

  type structural_constructor = {term: term, arity: int}

  type structural_family = {name: string, members: structural_constructor list}

  datatype structural_pattern =
      Structural_Any of term option
    | Structural_Node of
        {head: structural_constructor,
         family: structural_family option,
         arguments: structural_pattern list}

  datatype structural_subject =
    Structural_Subject of {value: term, children: structural_subject list}

  type source_position = {arm_index: int, alternative_index: int}

  datatype scope_kind =
      Direct_Scope
    | Alias_Scope
    | Nested_Scope
    | Transformed_Scope

  type clause_scope = {kind: scope_kind, close: term -> term}

  (* A normalized alternative: its clause pattern, its generated tests and scopes in evaluation
     order, and the navigation wrappers of its body. *)
  type normalized_pattern =
    {pattern: clause_pattern,
     tests: term list,
     scopes: clause_scope list,
     navigation: (term -> term) list}

  type case_clause =
    {structural_pattern: structural_pattern,
     generated_test: term option,
     scope: clause_scope,
     navigation: (term -> term) list,
     direct_branch: (term -> term) option}

  type decision_row =
    {position: source_position,
     clause: case_clause,
     source_guard: (term * Position.T) option,
     body: term}

  type structural_exclusion = {position: source_position, pattern: structural_pattern}

  type decision_state =
    {region: structural_pattern,
     subject: structural_subject,
     exclusions: structural_exclusion list}

  datatype structural_selection_witness =
      Selected_Any of {binder: term option, subject: structural_subject}
    | Selected_Node of {subject: structural_subject, arguments: structural_selection_witness list}

  (* covers_region: the opened shape subsumes the enclosing region, so no fallback branch
     follows it. *)
  datatype clause_selection =
      Reused_Clause_Selection of structural_selection_witness
    | Opened_Clause_Selection of
        {covers_region: bool,
         region: structural_pattern,
         abstraction: term -> term,
         witness: structural_selection_witness}

  datatype root_context =
      Match_Root
    | Failure_Root

  type opened_pattern = {abstraction: term -> term, subject: structural_subject}

  type structural_group = {pattern: structural_pattern, members: decision_row list}

  type outer_group_plan = {groups: structural_group list, catchall: structural_group option}

  (* One clause of a root case over the bound scrutinee. Decide_Clause opens its pattern and
     decides over all rows in that region. Catchall_Clause is the outer catchall: _ decides on the
     scrutinee itself, and a binder opens a fresh leaf. Redispatch_Clause opens its pattern and
     emits the failure-root case of its suffix rows there. *)
  datatype root_clause =
      Decide_Clause of {pattern: structural_pattern, exclusions: structural_exclusion list}
    | Catchall_Clause of {pattern: structural_pattern, exclusions: structural_exclusion list}
    | Redispatch_Clause of {pattern: structural_pattern, suffix: decision_row list}

  (* Where a failed generated test or source guard continues: in the selected region, or in a
     failure-root case over the remaining rows. *)
  datatype failure_target =
      Continue_In_Region
    | Redispatch_From_Root

  type decision_source_arm =
    {patterns: case_pattern list,
     environment: R.environment,
     source_guard: (term * Position.T) option,
     body: term}

  (*
    The ordered decision IR deliberately stays in ML until final case emission.

    - structural_pattern is a typed algebraic pattern. Structural_Any optionally records the exact
      Free that the source alternative binds at that point; constructor identity, arity, and
      complete native family order remain explicit in Structural_Node.
    - case_clause owns one structural pattern, its alternative-local generated test, one
      clause_scope, and an optional renderer for direct structural lowering. A clause_scope pairs
      its scope_kind with its closing operation, which binds aliases and recursively extracted
      nested binders around the source guard and body together; a direct scope closes with the
      identity. The direct renderer is derived from the normalized clause pattern and is only
      selected when every row in the matrix has the same structural capability. Both direct and
      recursive case emission use the backend constructors owned by Case_Term_Backend.
    - source_position is stable source order. Each decision_row records its arm and alternative
      index, which preserves the distinction between alternative failure and source-guard failure: a
      generated-test miss advances to the next alternative, while a false source guard advances to
      the next arm.
    - decision_state describes the structural region already selected by enclosing cases. exclusions
      record preceding case clauses that failed in that region. A structural_selection_witness
      certifies recursively that the selected region and subject decomposition conform before
      binders are extracted. Semantic totality never creates this witness: a singleton constructor
      or tuple over Structural_Any is opened to obtain its children. A selection that reuses the
      enclosing region fails back into its input decision state; an opened selection fails into the
      opened region over the witness's subject. When an opened selection does not cover the region,
      a wildcard branch after it continues in the input state with the row's shape excluded.
      Generated-test failure tries the next alternative; source-guard failure skips the source arm
      without sharing the selected alternative's binders. A structural_exclusion suppresses only
      its exact source position.
    - plan_root lists the clauses of one root case as root_clause values: the decided groups, then
      the redispatched groups and the outer catchall, each with its exclusions or suffix rows.
      Structural grouping and coverage still determine when a total group is opened directly.
      Root-suffix reconstruction preserves the established term shape for direct guards,
      nested/transformed generated-test misses and outer catchalls. Planning is pure and runs
      afresh for every root case; emitted terms are never reused, because binder reports and
      nested compiles fire once per emission. Each clause and selector constructs one term;
      planning never changes decision-state selection.

    One compiler below handles ordinary, guarded, overlapping, and recursive nested cases. It never
    packs compiler metadata into HOL terms, never decodes generated terms, and never has separate
    guarded/unguarded compilation paths.
  *)

  fun same_constructor (left : structural_constructor, right : structural_constructor) =
    Term.aconv_untyped (#term left, #term right)

  fun declared_constructor ctxt term : structural_constructor =
    (case term of
       Const (name, _) =>
         {term = Const (name, dummyT),
          arity = length (binder_types (Sign.the_const_type (Proof_Context.theory_of ctxt) name))}
     | _ => error "urust_expr: internal non-constant structural constructor")

  fun constructor_family_from_terms ctxt name members : structural_family =
    {name = name, members = map (declared_constructor ctxt) members}

  fun constructor_head ctxt constructor family_hint =
    let
      val (name, typ) =
        (case constructor of
           Const (constructor_name, _) =>
             (constructor_name, Sign.the_const_type (Proof_Context.theory_of ctxt) constructor_name)
         | _ => error "urust_expr: internal non-constant structural constructor")
      val head = declared_constructor ctxt constructor
      val family =
        (case Case_Translation.lookup_by_constr_permissive ctxt (name, typ) of
           SOME (_, members) =>
             SOME
               (constructor_family_from_terms ctxt
                 (the_default name (try dest_Type_name (body_type typ))) members)
         | NONE =>
             Option.map
               (fn (family_name, members) =>
                 constructor_family_from_terms ctxt family_name members)
               family_hint)
    in (head, family) end

  fun make_structural_node ctxt constructor family_hint arguments =
    let val (head, family) = constructor_head ctxt constructor family_hint
    in Structural_Node {head = head, family = family, arguments = arguments} end

  fun structural_pattern_of_clause ctxt environment pattern =
    let
      fun local_free binder_sig =
        let
          val name = signature_name binder_sig
          val pos = signature_position binder_sig
        in
          (case R.lookup_local environment name of
             SOME free => free
           | NONE =>
               error ("urust_expr: internal unregistered case binder " ^ quote name ^
                 Position.here pos))
        end

      fun convert Clause_Wild = Structural_Any NONE
        | convert (Clause_Binder binder_sig) = Structural_Any (SOME (local_free binder_sig))
        | convert (Clause_Generated free) = Structural_Any (SOME free)
        | convert (Clause_Node {head, family_hint, arguments}) =
            make_structural_node ctxt head family_hint (map convert arguments)
    in convert pattern end

  fun erase_structural_bindings (Structural_Any _) = Structural_Any NONE
    | erase_structural_bindings (Structural_Node {head, family, arguments}) =
        Structural_Node
          {head = head, family = family, arguments = map erase_structural_bindings arguments}

  fun structural_is_any (Structural_Any _) = true
    | structural_is_any _ = false

  fun structural_same_shape (Structural_Any _, Structural_Any _) = true
    | structural_same_shape
        (Structural_Node {head = left_head, arguments = left_arguments, ...},
         Structural_Node {head = right_head, arguments = right_arguments, ...}) =
        same_constructor (left_head, right_head) andalso
          eq_list structural_same_shape (left_arguments, right_arguments)
    | structural_same_shape _ = false

  fun structural_subsumes (Structural_Any _, _) = true
    | structural_subsumes
        (Structural_Node {head = left_head, arguments = left_arguments, ...},
         Structural_Node {head = right_head, arguments = right_arguments, ...}) =
        same_constructor (left_head, right_head) andalso
          eq_list structural_subsumes (left_arguments, right_arguments)
    | structural_subsumes _ = false

  fun structural_intersection (Structural_Any _, right) = SOME (erase_structural_bindings right)
    | structural_intersection (left, Structural_Any _) = SOME (erase_structural_bindings left)
    | structural_intersection
        (Structural_Node {head = left_head, family = left_family, arguments = left_arguments},
         Structural_Node {head = right_head, family = _, arguments = right_arguments}) =
        if same_constructor (left_head, right_head)
        then
          (case map2 (fn left => fn right => structural_intersection (left, right))
              left_arguments right_arguments of
             intersections =>
               if List.all is_some intersections
               then
                 SOME
                   (Structural_Node
                     {head = left_head, family = left_family, arguments = map the intersections})
               else NONE)
        else NONE

  fun same_family (left : structural_family, right : structural_family) =
    #name left = #name right andalso eq_list same_constructor (#members left, #members right)

  fun structural_is_total (Structural_Any _) = true
    | structural_is_total (Structural_Node {head, family = SOME family, arguments}) =
        (case #members family of
           [only] => same_constructor (head, only) andalso List.all structural_is_total arguments
         | _ => false)
    | structural_is_total _ = false

  (* Structural totality ignores binders, aliases, type constraints and navigation. A value, range
     or slice suffix makes the pattern not structurally total, so its spine is NONE. try turns a
     failure to resolve a constructor head of the spine into false. *)
  fun case_pattern_structurally_total ctxt pattern =
    let
      fun spine Case_Wild = SOME Case_Wild
        | spine (Case_Bind _) = SOME Case_Wild
        | spine (Case_Value _) = NONE
        | spine (Case_Node {head, family_hint, arguments}) =
            Option.map
              (fn arguments' =>
                Case_Node {head = head, family_hint = family_hint, arguments = arguments'})
              (spine_arguments arguments)
        | spine (Case_Tuple arguments) = Option.map Case_Tuple (spine_arguments arguments)
        | spine (Case_Alias (_, _, inner, _)) = spine inner
        | spine (Case_Constraint (_, _, inner)) = spine inner
        | spine (Case_Range _) = NONE
        | spine (Case_Slice_Suffix _) = NONE
        | spine (Case_Navigated (_, inner)) = spine inner
      and spine_arguments arguments =
        let val spines = map spine arguments
        in if List.all is_some spines then SOME (map the spines) else NONE end
      fun check candidate =
        structural_is_total
          (structural_pattern_of_clause ctxt R.empty_environment (clause_of_case_pattern candidate))
    in
      (case spine pattern of
         NONE => false
       | SOME candidate => the_default false (try check candidate))
    end

  fun structural_root_region (Structural_Any _) = Structural_Any NONE
    | structural_root_region (Structural_Node {head, family, arguments}) =
        (case family of
           SOME known =>
             (case #members known of
                [only] =>
                  if same_constructor (head, only)
                  then
                    Structural_Node
                      {head = head, family = family,
                       arguments = map structural_root_region arguments}
                  else Structural_Any NONE
              | _ => Structural_Any NONE)
         | NONE => Structural_Any NONE)

  fun structural_root_group_pattern pattern =
    (case structural_root_region pattern of
       Structural_Any _ => pattern
     | region => region)

  fun structural_semantically_subsumes (Structural_Any _, _) = true
    | structural_semantically_subsumes (left, Structural_Any _) = structural_is_total left
    | structural_semantically_subsumes
        (Structural_Node {head = left_head, arguments = left_arguments, ...},
         Structural_Node {head = right_head, arguments = right_arguments, ...}) =
        same_constructor (left_head, right_head) andalso
          eq_list structural_semantically_subsumes (left_arguments, right_arguments)
    | structural_semantically_subsumes _ = false

  fun replace_column index replacements row =
    take index row @ replacements @ drop (index + 1) row

  fun first_structural_column rows =
    let
      val width = (case rows of [] => 0 | row :: _ => length row)
      fun has_node index =
        List.exists
          (fn row =>
            (case nth row index of
               Structural_Node _ => true
             | Structural_Any _ => false))
          rows
      fun seek index =
        if index >= width then NONE
        else if has_node index then SOME index
        else seek (index + 1)
    in seek 0 end

  fun matrix_covers_all rows =
    if null rows then false
    else if List.exists (List.all structural_is_total) rows
    then true
    else
      (case first_structural_column rows of
         NONE => false
       | SOME column =>
           let
             val heads =
               map_filter
                 (fn row =>
                   (case nth row column of
                      Structural_Node {head, family, ...} => SOME (head, family)
                    | Structural_Any _ => NONE))
                 rows
             val family =
               (case heads of
                  [] => NONE
                | (_, NONE) :: _ => NONE
                | (_, SOME candidate) :: rest =>
                    if List.all
                        (fn (_, SOME other) => same_family (candidate, other)
                          | _ => false)
                        rest
                    then SOME candidate
                    else NONE)

             fun specialize member row =
               (case nth row column of
                  Structural_Any _ =>
                    SOME
                      (replace_column column
                        (replicate (#arity member) (Structural_Any NONE)) row)
                | Structural_Node {head, arguments, ...} =>
                    if same_constructor (head, member)
                    then SOME (replace_column column arguments row)
                    else NONE)
           in
             (case family of
                NONE => false
              | SOME known =>
                  List.all
                    (fn member => matrix_covers_all (map_filter (specialize member) rows))
                    (#members known))
           end)

  fun patterns_cover_all patterns =
    matrix_covers_all (map (fn pattern => [erase_structural_bindings pattern]) patterns)

  fun subject_value (Structural_Subject {value, ...}) = value

  fun subject_children (Structural_Subject {children, ...}) = children

  fun fresh_pattern_subject ctxt pattern : opened_pattern =
    let
      fun fresh_leaf () = Free ("_urust_region_" ^ string_of_int (serial ()), dummyT)

      fun open_pattern (Structural_Any _) =
            let
              val free = fresh_leaf ()
            in
              (Clause_Generated free, Structural_Subject {value = free, children = []})
            end
        | open_pattern (Structural_Node {head, arguments, ...}) =
            let
              val opened = map open_pattern arguments
              val clauses = map fst opened
              val subjects = map snd opened
              val value = Term.list_comb (#term head, map subject_value subjects)
            in
              (Clause_Node {head = #term head, family_hint = NONE, arguments = clauses},
               Structural_Subject {value = value, children = subjects})
            end

      val (clause, subject) = open_pattern pattern
    in {abstraction = bind_clause_pattern ctxt R.empty_environment clause, subject = subject} end

  fun selection_subject (Selected_Any {subject, ...}) = subject
    | selection_subject (Selected_Node {subject, ...}) = subject

  fun make_structural_selection_witness pattern region subject =
    let
      fun refine_arguments [] [] [] = SOME []
        | refine_arguments (pattern :: patterns) (region :: regions) (subject :: subjects) =
            (case refine pattern region subject of
               NONE => NONE
             | SOME selected =>
                 Option.map (fn rest => selected :: rest)
                   (refine_arguments patterns regions subjects))
        | refine_arguments _ _ _ = NONE
      and refine (Structural_Any binder) _ subject =
            SOME (Selected_Any {binder = binder, subject = subject})
        | refine
            (Structural_Node {head = pattern_head, arguments = pattern_arguments, ...})
            (Structural_Node {head = region_head, arguments = region_arguments, ...})
            subject =
            if same_constructor (pattern_head, region_head)
            then
              Option.map
                (fn selected_arguments =>
                  Selected_Node {subject = subject, arguments = selected_arguments})
                (refine_arguments pattern_arguments region_arguments (subject_children subject))
            else NONE
        | refine (Structural_Node _) (Structural_Any _) _ = NONE
    in refine pattern region subject end

  fun select_structural_clause ctxt pattern ({region, subject, ...} : decision_state) =
    (case make_structural_selection_witness pattern region subject of
       SOME witness => Reused_Clause_Selection witness
     | NONE =>
         let
           val shape = erase_structural_bindings pattern
           val {abstraction, subject = opened_subject} = fresh_pattern_subject ctxt shape
           val witness =
             (case make_structural_selection_witness pattern shape opened_subject of
                SOME selected => selected
              | NONE => error "urust_expr: internal invalid opened structural selection")
         in
           Opened_Clause_Selection
             {covers_region = structural_semantically_subsumes (shape, region), region = shape,
              abstraction = abstraction, witness = witness}
         end)

  fun structural_bindings (Selected_Any {binder = NONE, ...}) = []
    | structural_bindings (Selected_Any {binder = SOME free, subject}) =
        [(free, subject_value subject)]
    | structural_bindings (Selected_Node {arguments, ...}) = maps structural_bindings arguments

  fun specialize_term bindings = if null bindings then I else Term.subst_free bindings

  val direct_scope : clause_scope = {kind = Direct_Scope, close = I}

  fun scope_kind_rank Direct_Scope = 0
    | scope_kind_rank Alias_Scope = 1
    | scope_kind_rank Nested_Scope = 2
    | scope_kind_rank Transformed_Scope = 3

  fun stronger_scope_kind kind other =
    if scope_kind_rank kind > scope_kind_rank other then kind else other

  (* The combined scope closes with the first wrapper outermost. Its kind is the strongest kind
     among the wrappers: Transformed over Nested over Alias. No wrapper has kind Direct_Scope, so
     the scope is direct exactly when there are no wrappers. *)
  fun combine_scopes [] = direct_scope
    | combine_scopes (scopes : clause_scope list) =
        {kind = fold (fn {kind, ...} => stronger_scope_kind kind) scopes Direct_Scope,
         close = fn rhs => fold_rev (fn {close, ...} => close) scopes rhs}

  fun extend_generated_test generated NONE = SOME generated
    | extend_generated_test generated (SOME prior) = SOME (T.binary And prior generated)

  fun alias_wrapper transform environment expression binder_sig rhs =
    let
      val name = signature_name binder_sig
      val pos = signature_position binder_sig
    in
      (case R.lookup_local environment name of
         SOME free => T.bind (transform expression) (Term.lambda free rhs)
       | NONE =>
           error ("urust_expr: internal unregistered alias binder " ^ quote name ^
             Position.here pos))
    end

  fun compile_nested_case compiler ctxt environment expression pattern success fallback =
    compiler ctxt expression
      ([(pattern, environment, NONE, success)] @
       (if case_pattern_structurally_total ctxt pattern
        then []
        else [(Case_Wild, environment, NONE, fallback)]))

  (*
    Slice punctuation denotes the generated list case even when the list pattern is nested inside
    another constructor. Keep this probe in the branch body: wrapping case_abs/case_elem itself
    would make Ctr_Sugar reject the clause.
  *)
  fun slice_navigation_wrapper positions rhs =
    Navigation.with_source positions (fn () =>
      Navigation.probe
        (Navigation.mark Navigation.Primary
          (Const (\<^const_name>\<open>List.case_list\<close>, dummyT)))
        rhs)

  fun apply_navigation wrappers rhs =
    fold_rev (fn wrapper => fn body => wrapper body) wrappers rhs

  fun strip_case_navigation (Case_Navigated (positions, inner)) =
        let val (nested, core) = strip_case_navigation inner
        in (positions :: nested, core) end
    | strip_case_navigation pattern = ([], pattern)

  fun clause_only pattern : normalized_pattern =
    {pattern = pattern, tests = [], scopes = [], navigation = []}

  fun add_scope scope ({pattern, tests, scopes, navigation} : normalized_pattern)
      : normalized_pattern =
    {pattern = pattern, tests = tests, scopes = scopes @ [scope], navigation = navigation}

  fun add_slice_navigation positions ({pattern, tests, scopes, navigation} : normalized_pattern)
      : normalized_pattern =
    {pattern = pattern, tests = tests, scopes = scopes,
     navigation = navigation @ map slice_navigation_wrapper positions}

  (* Normalizes a pattern whose own head needs no generated test. Each argument that needs a
     nested match becomes a generated temporary: its test is compiled here, its scope when the
     clause is closed. *)
  fun normalize_pattern_for_nested compiler ctxt environment pattern : normalized_pattern =
    let
      fun normalize_argument argument =
        let val (navigation_positions, bare_argument) = strip_case_navigation argument
        in
          if requires_nested_match bare_argument
          then
            let
              val temporary = Free ("_urust_pat_" ^ string_of_int (serial ()), dummyT)
              val temporary_expression = T.literal temporary
              val (matched_expression, matched_pattern) =
                (case bare_argument of
                   Case_Slice_Suffix reversed_suffix =>
                     (T.reverse_list temporary_expression, reversed_suffix)
                 | _ => (temporary_expression, bare_argument))
              val structurally_total = case_pattern_structurally_total ctxt matched_pattern
              val tests =
                if structurally_total
                then []
                else
                  [compile_nested_case compiler ctxt environment matched_expression
                    matched_pattern (T.literal T.true_value) (T.literal T.false_value)]
              fun wrapper rhs =
                compile_nested_case compiler ctxt environment matched_expression matched_pattern
                  rhs T.undefined_value
              val kind =
                (case bare_argument of
                   Case_Slice_Suffix _ => Transformed_Scope
                 | _ => Nested_Scope)
            in
              add_slice_navigation navigation_positions
                {pattern = Clause_Generated temporary, tests = tests,
                 scopes = [{kind = kind, close = wrapper}], navigation = []}
            end
          else normalize_pattern_for_nested compiler ctxt environment argument
        end

      (* Node and tuple arguments are normalized left to right, so their tests are compiled in
         that order. *)
      fun normalize_arguments make_pattern arguments : normalized_pattern =
        let val normalized = map normalize_argument arguments
        in
          {pattern = make_pattern (map #pattern normalized), tests = maps #tests normalized,
           scopes = maps #scopes normalized, navigation = maps #navigation normalized}
        end

      val (navigation_positions, bare_pattern) = strip_case_navigation pattern
    in
      add_slice_navigation navigation_positions
        (case bare_pattern of
           Case_Node {head, family_hint, arguments} =>
             normalize_arguments
               (fn arguments' =>
                 Clause_Node {head = head, family_hint = family_hint, arguments = arguments'})
               arguments
         | Case_Tuple arguments => normalize_arguments tuple_clause arguments
         | _ => clause_only (clause_of_case_pattern bare_pattern))
    end

  fun normalize_extended_pattern compiler ctxt environment expression pattern
      : normalized_pattern =
    let val (navigation_positions, bare_pattern) = strip_case_navigation pattern
    in
      add_slice_navigation navigation_positions
        (case bare_pattern of
           Case_Alias (binder_sig, transform, inner, at_pos) =>
             let
               val normalized =
                 normalize_extended_pattern compiler ctxt environment expression inner
               fun wrap rhs =
                 Navigation.with_source_position at_pos (fn () =>
                   alias_wrapper transform environment expression binder_sig rhs)
             in
               add_scope {kind = Alias_Scope, close = wrap} normalized
             end
         | Case_Constraint (typ, pos, inner) =>
             let
               val normalized =
                 normalize_extended_pattern compiler ctxt environment expression inner
               fun wrap rhs =
                 T.bind expression
                   (constrain_pattern_abstraction typ pos (R.anonymous_abstraction rhs))
             in
               add_scope {kind = Nested_Scope, close = wrap} normalized
             end
         | Case_Value (literal, _) =>
             {pattern = Clause_Wild, tests = [T.binary Eq expression (T.literal literal)],
              scopes = [], navigation = []}
         | Case_Range (kind, lower, upper, _) =>
             let
               val upper_guard =
                 T.binary
                   (case kind of
                      RK_Exclusive => Lt
                    | RK_Inclusive => Le)
                   expression upper
               val test = T.binary And (T.binary Ge expression lower) upper_guard
             in
               {pattern = Clause_Wild, tests = [test], scopes = [], navigation = []}
             end
         | Case_Slice_Suffix reversed_suffix =>
             let
               val reversed_expression = T.reverse_list expression
               val test =
                 compile_nested_case compiler ctxt environment reversed_expression reversed_suffix
                   (T.literal T.true_value) (T.literal T.false_value)
               fun wrap rhs =
                 compile_nested_case compiler ctxt environment reversed_expression reversed_suffix
                   rhs T.undefined_value
             in
               {pattern = Clause_Wild, tests = [test],
                scopes = [{kind = Transformed_Scope, close = wrap}], navigation = []}
             end
         | _ => normalize_pattern_for_nested compiler ctxt environment bare_pattern)
    end

  fun normalize_case_alternative compiler ctxt value (pattern, environment) : case_clause =
    let
      val {pattern = clause_pattern, tests, scopes, navigation} =
        normalize_extended_pattern compiler ctxt environment (T.literal value) pattern
      val generated_test = fold extend_generated_test tests NONE
      val scope = combine_scopes scopes
      val direct_branch = try (bind_clause_pattern ctxt environment) clause_pattern
    in
      {structural_pattern = structural_pattern_of_clause ctxt environment clause_pattern,
       generated_test = generated_test, scope = scope, navigation = navigation,
       direct_branch = direct_branch}
    end

  fun case_term_on subject branches =
    let
      val raw = Case_Term_Backend.make_case T.true_value subject branches
      (* Keep clause heads raw for native case translation. The complete selector resolves to its
         datatype case constant before navigation erasure; auxiliary case constructors remain
         secondary targets. *)
    in
      fold_rev
        (fn name => fn body => Navigation.annotate Navigation.Secondary (Const (name, dummyT)) body)
        [\<^const_name>\<open>case_nil\<close>,
         \<^const_name>\<open>case_cons\<close>,
         \<^const_name>\<open>case_elem\<close>,
         \<^const_name>\<open>case_abs\<close>,
         \<^const_name>\<open>case_guard\<close>]
        (Navigation.mark Navigation.Primary raw)
    end

  fun generated_wild ctxt rhs = bind_clause_pattern ctxt R.empty_environment Clause_Wild rhs

  fun outer_clause_pattern (Const (name, _) $ Abs (_, _, body)) =
        if name = \<^const_name>\<open>case_abs\<close>
        then outer_clause_pattern body
        else NONE
    | outer_clause_pattern (Const (name, _) $ pattern $ _) =
        if name = \<^const_name>\<open>case_elem\<close>
        then SOME pattern
        else NONE
    | outer_clause_pattern _ = NONE

  fun constructor_clause branch =
    (case outer_clause_pattern branch of
       SOME pattern =>
         (case Term.head_of (Term_Position.strip_positions pattern) of
            Const _ => true
          | _ => false)
     | NONE => false)

  fun direct_structural_branch
      ({clause = {generated_test, scope = {kind, ...}, navigation, direct_branch, ...},
        source_guard, body, ...} : decision_row) =
    (case (source_guard, generated_test, kind, direct_branch) of
       (NONE, NONE, Direct_Scope, SOME render) => SOME (render (apply_navigation navigation body))
     | _ => NONE)

  fun unconditional_total_row
      ({clause = {structural_pattern, generated_test, ...}, source_guard, ...} : decision_row) =
    is_none generated_test andalso is_none source_guard andalso
      structural_is_total structural_pattern

  fun validate_row_reachability [] = ()
    | validate_row_reachability [_] = ()
    | validate_row_reachability (row :: rest) =
        if unconditional_total_row row
        then error "clauses are redundant"
        else validate_row_reachability rest

  fun row_arm (row : decision_row) = #arm_index (#position row)

  fun row_pattern (row : decision_row) = #structural_pattern (#clause row)

  fun row_has_generated_test (row : decision_row) = is_some (#generated_test (#clause row))

  fun row_has_source_guard (row : decision_row) = is_some (#source_guard row)

  fun row_shape row = erase_structural_bindings (row_pattern row)

  datatype match_root_kind =
      Structural_Match_Root
    | Conditional_Match_Root
    | Binding_Match_Root

  fun drop_source_arm arm_index rows =
    drop_prefix (fn row => row_arm row = arm_index) rows

  fun row_exclusion (row : decision_row) pattern : structural_exclusion =
    {position = #position row, pattern = pattern}

  fun same_outer_group (left, right) =
    structural_same_shape (left, right) orelse
      (structural_is_total left andalso structural_is_total right)

  fun add_group_row (row : decision_row) group_pattern [] : structural_group list =
        [{pattern = group_pattern, members = [row]}]
    | add_group_row row group_pattern ((group as {pattern, members}) :: rest) =
        if same_outer_group (pattern, group_pattern)
        then {pattern = pattern, members = members @ [row]} :: rest
        else group :: add_group_row row group_pattern rest

  fun install_source_catchall row NONE : structural_group option =
        SOME {pattern = row_pattern row, members = [row]}
    | install_source_catchall row (SOME (group as {pattern, ...} : structural_group)) =
        (case (pattern, row_pattern row) of
           (Structural_Any NONE, bound as Structural_Any (SOME _)) =>
             SOME {pattern = bound, members = [row]}
         | _ => SOME group)

  fun add_root_group row ({groups, catchall} : outer_group_plan) : outer_group_plan =
    let
      val shape = row_shape row
      val group_pattern = structural_root_group_pattern shape
      val (groups', catchall') =
        if structural_is_any shape
        then (groups, install_source_catchall row catchall)
        else (add_group_row row group_pattern groups, catchall)
    in
      {groups = groups', catchall = catchall'}
    end

  fun transformed_root_tail
      ({clause = {scope = {kind = Transformed_Scope, ...}, ...}, ...} : decision_row) = true
    | transformed_root_tail _ = false

  fun prefix_has_structural_group prefix =
    List.exists (not o structural_is_any o row_shape) prefix

  fun emission_root_prefix _ prefix [] = (rev prefix, false)
    | emission_root_prefix guarded_arm prefix (row :: rest) =
        if transformed_root_tail row
        then (rev prefix, true)
        else
          (case guarded_arm of
             SOME active_arm =>
               if row_arm row = active_arm
               then emission_root_prefix guarded_arm (row :: prefix) rest
               else (rev prefix, true)
           | NONE =>
               let
                 val shape = row_shape row
                 val guarded_arm' =
                   if row_has_source_guard row andalso
                      (not (structural_is_any shape) orelse
                       not (prefix_has_structural_group prefix))
                   then SOME (row_arm row)
                   else NONE
               in
                 emission_root_prefix guarded_arm' (row :: prefix) rest
               end)

  fun exact_shape_groups rows =
    fold (fn row => fn groups => add_group_row row (row_shape row) groups) rows []

  fun emission_group_exclusions ({members, ...} : structural_group) =
    (case members of
       [] => error "urust_expr: internal empty structural group"
     | first :: rest =>
         row_exclusion first (row_shape first) ::
           map (fn row => row_exclusion row (row_shape row)) (filter row_has_generated_test rest))

  fun group_starts_with_generated_test ({members, ...} : structural_group) =
    (case members of
       first :: _ => row_has_generated_test first
     | [] => error "urust_expr: internal empty structural group")

  fun remove_subsumed_emission_groups groups =
    let
      fun covered prior (candidate : structural_group) =
        List.exists
          (fn group =>
            group_starts_with_generated_test group andalso
              structural_subsumes (#pattern group, #pattern candidate))
          prior
      fun retain _ [] = []
        | retain prior (group :: rest) =
            if covered prior group
            then retain prior rest
            else group :: retain (prior @ [group]) rest
    in retain [] groups end

  (* A single structurally total group containing a total source row is coverage-complete. Root
     emission opens that group directly instead of reconstructing a redundant root tail. This rule
     depends only on typed structural coverage, not on any particular constructor or tuple
     shape. *)
  fun group_is_coverage_complete ({pattern, members} : structural_group) =
    structural_is_total pattern andalso List.exists (structural_is_total o row_shape) members

  fun following_group_exclusion ({members, ...} : structural_group) =
    (case members of
       [] => error "urust_expr: internal empty structural group"
     | first :: _ =>
         if row_has_generated_test first
         then NONE
         else SOME (row_exclusion first (row_shape first)))

  fun nested_failure_scope
      ({clause = {scope = {kind = Nested_Scope, ...}, generated_test = SOME _, ...}, ...}
        : decision_row) = true
    | nested_failure_scope _ = false

  fun rows_after_position _ [] = error "urust_expr: internal missing suffix row"
    | rows_after_position position ((row : decision_row) :: rest) =
        if position = #position row
        then rest
        else rows_after_position position rest

  fun nested_failure_suffix planned_rows ({members, ...} : structural_group) =
    (case members of
       first :: _ =>
         if nested_failure_scope first
         then SOME (rows_after_position (#position first) planned_rows)
         else NONE
     | [] => error "urust_expr: internal empty structural group")

  (* The groups up to and including the first one whose first row has a nested generated test,
     and, if there is such a group, the groups after it together with the rows after that row. *)
  fun split_at_nested_failure rows groups =
    let
      fun split decided [] = (rev decided, NONE)
        | split decided (group :: rest) =
            (case nested_failure_suffix rows group of
               NONE => split (group :: decided) rest
             | SOME suffix => (rev (group :: decided), SOME (rest, suffix)))
    in split [] groups end

  (*
    The clauses of one root case over the rows, in emission order. A coverage-complete single
    group gives its one clause. Otherwise Match_Root emits the exact shapes within each root
    group, or those of the non-wild rows of a cut prefix. Failure_Root cuts before the first row,
    which leaves only the catchall, and plans nothing for no rows. A shape covered by an earlier
    shape whose first row has a generated test is dropped. The catchall is omitted when the
    shapes cover the type; a cut without a source catchall uses a synthetic _. A decided group
    excludes the first row of each earlier group whose first row has no generated test. The
    catchall excludes the first row and the later generated-test rows of every emitted group.
    After the first group whose first row has a nested generated test, the later groups and the
    catchall redispatch into the failure-root case of the rows after that row.
  *)
  fun plan_root context rows =
    let
      val {groups, catchall = catchall_group} =
        fold add_root_group rows {groups = [], catchall = NONE}
      val complete =
        (case groups of
           [group] => group_is_coverage_complete group
         | _ => false)
      val (prefix, cut) =
        if complete then (rows, false)
        else
          (case context of
             Match_Root => emission_root_prefix NONE [] rows
           | Failure_Root => ([], not (null rows)))
      val emitted =
        remove_subsumed_emission_groups
          (if complete then groups
           else if cut
           then exact_shape_groups (filter_out (structural_is_any o row_shape) prefix)
           else maps (exact_shape_groups o #members) groups)
      fun uncovered pattern =
        if patterns_cover_all (map #pattern emitted) then NONE else SOME pattern
      val source_catchall = Option.map #pattern catchall_group
      val catchall =
        if cut then uncovered (the_default (Structural_Any NONE) source_catchall)
        else Option.mapPartial uncovered source_catchall
      val (decided, redispatched) = split_at_nested_failure rows emitted
      val (decide_clauses, _) =
        fold_map
          (fn group => fn exclusions =>
            (Decide_Clause {pattern = #pattern group, exclusions = exclusions},
             the_list (following_group_exclusion group) @ exclusions))
          decided []
      val tail_clauses =
        (case redispatched of
           NONE =>
             map
               (fn pattern =>
                 Catchall_Clause
                   {pattern = pattern, exclusions = maps emission_group_exclusions emitted})
               (the_list catchall)
         | SOME (groups_after, suffix) =>
             map (fn pattern => Redispatch_Clause {pattern = pattern, suffix = suffix})
               (map #pattern groups_after @ the_list catchall))
    in decide_clauses @ tail_clauses end

  (* A generated-test miss in a nested or transformed scope redispatches from the root. *)
  fun test_failure_target Nested_Scope = Redispatch_From_Root
    | test_failure_target Transformed_Scope = Redispatch_From_Root
    | test_failure_target _ = Continue_In_Region

  (* A false source guard in a direct scope with a constructor shape redispatches from the root. *)
  fun guard_failure_target (Direct_Scope, Structural_Node _) = Redispatch_From_Root
    | guard_failure_target _ = Continue_In_Region

  fun excluded_region (exclusions : structural_exclusion list) position region =
    List.exists
      (fn exclusion =>
        #position exclusion = position andalso
          structural_semantically_subsumes (#pattern exclusion, region))
      exclusions

  (* Whether the row can match inside the state's region: its shape intersects the region and no
     exclusion for its position subsumes that intersection. *)
  fun row_applicable ({region, exclusions, ...} : decision_state) row =
    (case structural_intersection (region, row_shape row) of
       NONE => false
     | SOME matched => not (excluded_region exclusions (#position row) matched))

  fun first_applicable _ [] = NONE
    | first_applicable state (row :: rest) =
        if row_applicable state row
        then SOME (row, rest)
        else first_applicable state rest

  fun add_exclusion ({region, subject, exclusions} : decision_state) position pattern
      : decision_state =
    {region = region, subject = subject,
     exclusions = {position = position, pattern = pattern} :: exclusions}

  fun close_selected_clause ({generated_test, scope, navigation, ...} : case_clause) selection
      source_guard body alternative_failure arm_failure =
    let
      val specialize = specialize_term (structural_bindings selection)
      val navigated_body = apply_navigation navigation body
      val guarded_body =
        (case source_guard of
           NONE => navigated_body
         | SOME (guard, guard_pos) =>
             Navigation.with_source_position guard_pos (fn () =>
               T.conditional guard navigated_body (the arm_failure)))
      val scoped_body = specialize (#close scope guarded_body)
    in
      (case generated_test of
         NONE => scoped_body
       | SOME test => T.conditional (specialize test) scoped_body (the alternative_failure))
    end

  fun retain_witness witness body =
    Abs ("_urust_pattern_type_probe_" ^ string_of_int (serial ()),
      dummyT, Term.incr_boundvars 1 body) $ witness

  fun compile_pattern_case ctxt scrutinee arms =
    compile_decision_case Ordinary_Case_Compilation [] ctxt [] NONE scrutinee
      (map
        (fn (pattern, environment, source_guard, body) =>
          {patterns = [pattern], environment = environment, source_guard = source_guard,
           body = body})
        arms)

  and compile_decision_case compilation_mode typing_arms ctxt source_positions explicit_fallback
      scrutinee source_arms =
    let
      val value = Free ("_urust_case_value_" ^ string_of_int (serial ()), dummyT)

      val terminal_fallback = the_default T.undefined_value explicit_fallback

      (*
        Generated value/range tests also create root-subject selectors, but wildcard-only clauses
        type-check directly to their branch body. Scope the match token only over genuine
        constructor selectors so those generated operations cannot become match navigation targets.
      *)
      fun selector_of [] = terminal_fallback
        | selector_of branches =
            if List.exists constructor_clause branches
            then Navigation.with_source source_positions (fn () => case_term_on value branches)
            else case_term_on value branches

      val source_arms_with_fallback =
        source_arms @
          (case explicit_fallback of
             NONE => []
           | SOME body =>
               [{patterns = [Case_Wild], environment = R.empty_environment, source_guard = NONE,
                 body = body}])

      (* One row per source alternative, arm-major and alternative-minor. Each alternative is
         normalized exactly once, left to right. *)
      fun normalize_arm
          (arm_index, {patterns, environment, source_guard, body} : decision_source_arm) =
        map_index
          (fn (alternative_index, pattern) =>
            {position = {arm_index = arm_index, alternative_index = alternative_index},
             clause =
               normalize_case_alternative compile_pattern_case ctxt value (pattern, environment),
             source_guard = source_guard,
             body = body} : decision_row)
          patterns

      val rows = flat (map_index normalize_arm source_arms_with_fallback)

      fun direct_structural_matrix () =
        let val branches = map direct_structural_branch rows
        in
          if List.all is_some branches
          then SOME (map the branches)
          else NONE
        end

      (* The explicit false branch used by matches! is a real final decision row. Keeping this
         elementary usefulness check in the typed matrix preserves the legacy redundancy diagnostic
         for `_` and binder patterns instead of optimizing the unreachable row away. *)
      val _ = validate_row_reachability rows

      val root_subject = Structural_Subject {value = value, children = []}

      val match_root_decision =
        (case compilation_mode of
           Ordinary_Case_Compilation => NONE
         | Source_Match_Compilation =>
             SOME
               (if List.exists (not o structural_is_any o row_shape) rows
                then Structural_Match_Root
                else if List.exists
                    (fn row => row_has_generated_test row orelse row_has_source_guard row) rows
                then Conditional_Match_Root
                else Binding_Match_Root))

      fun compile_rows state remaining =
        (case first_applicable state remaining of
           NONE => terminal_fallback
         | SOME
             ({clause = (clause as {structural_pattern, generated_test, scope, ...}),
               source_guard, body, position = (position as {arm_index, ...})},
              rest) =>
             let
               val shape = erase_structural_bindings structural_pattern

               fun compile_matched selection failure_state =
                 let
                   (* A generated-test miss tries the next alternative. A false source guard skips
                      the entire source arm. Choose the one emitted destination before closing the
                      clause; an absent test or guard constructs no failure term. *)
                   fun failure_term Redispatch_From_Root remaining =
                         emit_root Failure_Root remaining
                     | failure_term Continue_In_Region remaining =
                         compile_rows failure_state remaining
                   val alternative_failure =
                     Option.map
                       (fn _ => failure_term (test_failure_target (#kind scope)) rest)
                       generated_test
                   val arm_failure =
                     Option.map
                       (fn _ =>
                         failure_term (guard_failure_target (#kind scope, shape))
                           (drop_source_arm arm_index rest))
                       source_guard
                 in
                   close_selected_clause clause selection source_guard body
                     alternative_failure arm_failure
                 end
               val {subject, exclusions, ...} : decision_state = state
             in
               (case select_structural_clause ctxt structural_pattern state of
                  Reused_Clause_Selection witness => compile_matched witness state
                | Opened_Clause_Selection {covers_region, region, abstraction, witness} =>
                    let
                      val success =
                        compile_matched witness
                          {region = region, subject = selection_subject witness,
                           exclusions = exclusions}
                      (* A covering selection is the only branch. Otherwise a wildcard branch
                         continues in the input state with this row's shape excluded. *)
                      val branches =
                        if covers_region then [abstraction success]
                        else
                          let val fallback = compile_rows (add_exclusion state position shape) rest
                          in [abstraction success, generated_wild ctxt fallback] end
                    in
                      case_term_on (subject_value subject) branches
                    end)
             end)

      (* Each clause opens its pattern before its body is compiled. *)
      and emit_root context remaining =
        let
          fun decide_in exclusions pattern =
            let
              val {abstraction, subject} = fresh_pattern_subject ctxt pattern
              val state : decision_state =
                {region = pattern, subject = subject, exclusions = exclusions}
            in
              abstraction (compile_rows state remaining)
            end
          fun emit (Decide_Clause {pattern, exclusions}) = decide_in exclusions pattern
            | emit (Catchall_Clause {pattern = pattern as Structural_Any NONE, exclusions}) =
                let
                  val state : decision_state =
                    {region = pattern, subject = root_subject, exclusions = exclusions}
                in generated_wild ctxt (compile_rows state remaining) end
            | emit (Catchall_Clause {pattern = pattern as Structural_Any (SOME _), exclusions}) =
                decide_in exclusions pattern
            | emit (Catchall_Clause {pattern = Structural_Node _, ...}) =
                error "urust_expr: internal non-wild outer catchall"
            | emit (Redispatch_Clause {pattern, suffix}) =
                let val {abstraction, ...} = fresh_pattern_subject ctxt pattern
                in abstraction (emit_root Failure_Root suffix) end
        in selector_of (map emit (plan_root context remaining)) end

      val selector =
        (case direct_structural_matrix () of
           SOME branches => selector_of branches
         | NONE => emit_root Match_Root rows)
      val navigated_selector =
        (case match_root_decision of
           SOME Conditional_Match_Root =>
             Navigation.with_source source_positions (fn () =>
               Navigation.annotate Navigation.Primary
                 (Const (\<^const_name>\<open>two_armed_conditional\<close>, dummyT))
                 selector)
         | SOME Binding_Match_Root =>
             Navigation.with_source source_positions (fn () =>
               Navigation.annotate Navigation.Primary
                 (Const (\<^const_name>\<open>Core_Expression.bind\<close>, dummyT))
                 selector)
         | _ => selector)
      (* Reachability can discard an arm or alternative before the completed term is checked. Retain
         independent pattern-only typing witnesses for every source pattern. They use the selected
         value, never the source scrutinee, guard, or body. A late native term-check phase removes
         these unused beta redexes after all witnesses are inferred. Canonical captures share one
         result type per source arm, including unused binders. Internal matcher calls receive no
         typing arms, preventing recursive witness generation. *)
      fun typing_witnesses (patterns, environment, binders) =
        let
          val capture_type = Type_Infer.mk_param (serial ()) []
          val expression_type =
            Type (\<^type_name>\<open>expression\<close>,
              [dummyT, capture_type, dummyT, dummyT, dummyT, dummyT])
          val captures = fold_rev T.pair binders T.tuple_nil_constructor
          val success = T.literal captures
        in
          map (fn pattern =>
            Type.constraint expression_type
              (compile_nested_case compile_pattern_case ctxt environment
                (T.literal value) pattern success T.undefined_value))
            patterns
        end
      val checked_selector =
        fold_rev retain_witness (maps typing_witnesses typing_arms) navigated_selector
    in
      T.bind scrutinee (Term.lambda value checked_selector)
    end

  fun compile_case compilation_mode ctxt source_positions explicit_fallback scrutinee
      (arms : case_arm list) =
    let
      fun source_arm ({patterns, environment, source_guard, body, ...} : case_arm) =
        {patterns = patterns, environment = environment, source_guard = source_guard, body = body}
      fun typing_arm ({patterns, environment, binders, ...} : case_arm) =
        (patterns, environment, binders)
    in
      compile_decision_case compilation_mode (map typing_arm arms) ctxt source_positions
        explicit_fallback scrutinee (map source_arm arms)
    end

  fun is_typing_witness
      (Abs (name, _, body) $ (Const (bind_name, _) $ _ $ Abs (value_name, _, _))) =
        String.isPrefix "_urust_pattern_type_probe_" name andalso
        String.isPrefix "_urust_case_value_" value_name andalso
        bind_name = \<^const_name>\<open>Core_Expression.bind\<close> andalso
        not (Term.loose_bvar1 (body, 0))
    | is_typing_witness _ = false

  fun erase_typing_witnesses (term as Abs (name, typ, body) $ witness) =
        if is_typing_witness term
        then erase_typing_witnesses (Term.betapply (Abs (name, typ, body), witness))
        else erase_typing_witnesses (Abs (name, typ, body)) $ erase_typing_witnesses witness
    | erase_typing_witnesses (function $ argument) =
        erase_typing_witnesses function $ erase_typing_witnesses argument
    | erase_typing_witnesses (Abs (name, typ, body)) =
        Abs (name, typ, erase_typing_witnesses body)
    | erase_typing_witnesses atomic = atomic

  val _ = Context.>>
    (Syntax_Phases.term_check 99 "urust_pattern_typing"
      (fn _ => map (fn term =>
        if Term.exists_subterm is_typing_witness term
        then erase_typing_witnesses term else term)))
end
\<close>

end
