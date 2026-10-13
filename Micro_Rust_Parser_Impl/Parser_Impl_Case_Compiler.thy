theory Parser_Impl_Case_Compiler
  imports Parser_Impl_Resolution
begin

section\<open> Case compilation \<close>

ML\<open>
signature URUST_CASE_COMPILER =
sig
  datatype case_pattern =
      Case_Wild
    | Case_Bind of string * Position.T
    | Case_Value of term * Position.T
    | Case_Node of
        {head: term, family_hint: (string * term list) option, arguments: case_pattern list}
    | Case_Tuple of case_pattern list
    | Case_Alias of (string * Position.T) * (term -> term) * case_pattern * Position.T
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

  A case_pattern is one prepared or-alternative. Its binders are already allocated in the arm
  environment, and every Case_Node head is the exact term supplied by preparation.
  constrain_pattern_abstraction constrains a pattern abstraction to a scrutinee type at a source
  position; URust_Patterns also uses it for direct bindings.

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

  (* The head of one case clause. Tuples are expanded into Pair/TNil chains, and Clause_Generated
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
     replaces them by generated tests and scopes first. *)
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

  datatype structural_constructor = Structural_Constructor of {term: term, arity: int}

  datatype structural_family =
    Structural_Family of {name: string, members: structural_constructor list}

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

  datatype case_clause =
    Case_Clause of
      {structural_pattern: structural_pattern,
       generated_test: term option,
       scope: clause_scope,
       navigation: (term -> term) list,
       direct_branch: (term -> term) option}

  datatype decision_row =
    Decision_Row of
      {position: source_position,
       clause: case_clause,
       source_guard: (term * Position.T) option,
       body: term}

  datatype structural_exclusion =
    Decision_Exclusion of {position: source_position, pattern: structural_pattern}

  datatype decision_state =
    Decision_State of
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

  datatype root_plan_context =
      Match_Root
    | Failure_Root

  datatype opened_pattern =
    Opened_Pattern of {abstraction: term -> term, subject: structural_subject}

  datatype structural_group =
    Structural_Group of {pattern: structural_pattern, members: decision_row list}

  datatype outer_group_plan =
    Outer_Group_Plan of {groups: structural_group list, catchall: structural_group option}

  datatype root_suffix_plan =
    Root_Suffix_Plan of
      {rows: decision_row list,
       groups: structural_group list,
       outer_catchall: structural_group option,
       catchall_exclusions: structural_exclusion list}

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
      opened region over the witness's subject. Generated-test failure tries the next alternative;
      source-guard failure skips the source arm without sharing the selected alternative's binders.
      Decision_Exclusion suppresses only its exact source position.
    - root_suffix_plan contains only emission rows, groups, catchall and exclusions. Structural
      grouping and coverage still determine when a total group is opened directly. Root-suffix
      reconstruction preserves the established term shape for direct guards, nested/transformed
      generated-test misses and outer catchalls. Planning is pure and runs afresh for every root
      suffix; emitted terms are never reused, because binder reports and nested compiles fire once
      per emission. Each clause and selector constructs one term; planning never changes
      decision-state selection.

    One compiler below handles ordinary, guarded, overlapping, and recursive nested cases. It never
    packs compiler metadata into HOL terms, never decodes generated terms, and never has separate
    guarded/unguarded compilation paths.
  *)

  fun constructor_term (Structural_Constructor {term, ...}) = term

  fun constructor_arity (Structural_Constructor {arity, ...}) = arity

  fun same_constructor (left, right) =
    Term.aconv_untyped (constructor_term left, constructor_term right)

  fun declared_constructor ctxt term =
    (case term of
       Const (name, _) =>
         Structural_Constructor
           {term = Const (name, dummyT),
            arity =
              length (binder_types (Sign.the_const_type (Proof_Context.theory_of ctxt) name))}
     | _ => error "urust_expr: internal non-constant structural constructor")

  fun constructor_family_from_terms ctxt name members =
    Structural_Family {name = name, members = map (declared_constructor ctxt) members}

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

  fun family_members (Structural_Family {members, ...}) = members

  fun same_family
      (Structural_Family {name = left_name, members = left_members},
       Structural_Family {name = right_name, members = right_members}) =
    left_name = right_name andalso eq_list same_constructor (left_members, right_members)

  fun structural_is_total (Structural_Any _) = true
    | structural_is_total (Structural_Node {head, family = SOME family, arguments}) =
        (case family_members family of
           [only] => same_constructor (head, only) andalso List.all structural_is_total arguments
         | _ => false)
    | structural_is_total _ = false

  (* Structural totality ignores binders, aliases and type constraints. A value, range or slice
     suffix has no clause form, so clause_of_case_pattern fails on it; try turns that failure, and
     any failure to resolve a constructor head, into false. *)
  fun case_pattern_structurally_total ctxt pattern =
    let
      fun spine (Case_Bind _) = Case_Wild
        | spine (Case_Node {head, family_hint, arguments}) =
            Case_Node {head = head, family_hint = family_hint, arguments = map spine arguments}
        | spine (Case_Tuple arguments) = Case_Tuple (map spine arguments)
        | spine (Case_Alias (_, _, inner, _)) = spine inner
        | spine (Case_Constraint (_, _, inner)) = spine inner
        | spine (Case_Navigated (_, inner)) = spine inner
        | spine other = other
      fun check candidate =
        structural_is_total
          (structural_pattern_of_clause ctxt R.empty_environment
            (clause_of_case_pattern (spine candidate)))
    in the_default false (try check pattern) end

  fun structural_root_region (Structural_Any _) = Structural_Any NONE
    | structural_root_region (Structural_Node {head, family, arguments}) =
        (case family of
           SOME known =>
             (case family_members known of
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
                        (replicate (constructor_arity member) (Structural_Any NONE)) row)
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
                    (family_members known))
           end)

  fun patterns_cover_all patterns =
    matrix_covers_all (map (fn pattern => [erase_structural_bindings pattern]) patterns)

  fun subject_value (Structural_Subject {value, ...}) = value

  fun subject_children (Structural_Subject {children, ...}) = children

  fun fresh_pattern_subject ctxt pattern =
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
              val value = Term.list_comb (constructor_term head, map subject_value subjects)
            in
              (Clause_Node {head = constructor_term head, family_hint = NONE, arguments = clauses},
               Structural_Subject {value = value, children = subjects})
            end

      val (clause, subject) = open_pattern pattern
    in
      Opened_Pattern
        {abstraction = bind_clause_pattern ctxt R.empty_environment clause, subject = subject}
    end

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

  fun select_structural_clause ctxt pattern (Decision_State {region, subject, ...}) =
    (case make_structural_selection_witness pattern region subject of
       SOME witness => Reused_Clause_Selection witness
     | NONE =>
         let
           val shape = erase_structural_bindings pattern
           val Opened_Pattern {abstraction, subject = opened_subject} =
             fresh_pattern_subject ctxt shape
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
     among the wrappers: Transformed over Nested over Alias. *)
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

  fun normalize_pattern_for_nested compiler ctxt environment pattern =
    let
      fun normalize_arguments [] = ([], [], [], [])
        | normalize_arguments (argument :: rest) =
            let
              val (navigation_positions, bare_argument) = strip_case_navigation argument
              val (argument', guards0, wrappers0, navigation0) =
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
                    val guards =
                      if structurally_total
                      then []
                      else
                        [compile_nested_case compiler ctxt environment matched_expression
                          matched_pattern (T.literal T.true_value) (T.literal T.false_value)]
                    fun wrapper rhs =
                      compile_nested_case compiler ctxt environment matched_expression
                        matched_pattern rhs T.undefined_value
                  in
                    (Clause_Generated temporary, guards,
                     [{kind =
                         (case bare_argument of
                            Case_Slice_Suffix _ => Transformed_Scope
                          | _ => Nested_Scope),
                       close = wrapper}],
                     map slice_navigation_wrapper navigation_positions)
                  end
                else normalize_pattern_for_nested compiler ctxt environment argument
              val (rest', guards1, wrappers1, navigation1) = normalize_arguments rest
            in
              (argument' :: rest', guards0 @ guards1, wrappers0 @ wrappers1,
               navigation0 @ navigation1)
            end
      val (navigation_positions, bare_pattern) = strip_case_navigation pattern
      val (clause, guards, wrappers, navigation) =
        (case bare_pattern of
           Case_Node {head, family_hint, arguments} =>
             let
               val (arguments', guards, wrappers, navigation) = normalize_arguments arguments
             in
               (Clause_Node {head = head, family_hint = family_hint, arguments = arguments'},
                guards, wrappers, navigation)
             end
         | Case_Tuple arguments =>
             let
               val (arguments', guards, wrappers, navigation) = normalize_arguments arguments
             in
               (tuple_clause arguments', guards, wrappers, navigation)
             end
         | _ => (clause_of_case_pattern bare_pattern, [], [], []))
    in
      (clause, guards, wrappers, navigation @ map slice_navigation_wrapper navigation_positions)
    end

  fun normalize_extended_pattern compiler ctxt environment expression pattern =
    let
      val (navigation_positions, bare_pattern) = strip_case_navigation pattern
      val (clause, guards, wrappers, navigation) =
        (case bare_pattern of
           Case_Alias (binder_sig, transform, inner, at_pos) =>
             let
               val (clause, guards, wrappers, navigation) =
                 normalize_extended_pattern compiler ctxt environment expression inner
               fun wrap rhs =
                 Navigation.with_source_position at_pos (fn () =>
                   alias_wrapper transform environment expression binder_sig rhs)
             in
               (clause, guards, wrappers @ [{kind = Alias_Scope, close = wrap}], navigation)
             end
         | Case_Constraint (typ, pos, inner) =>
             let
               val (clause, guards, wrappers, navigation) =
                 normalize_extended_pattern compiler ctxt environment expression inner
               fun wrap rhs =
                 T.bind expression
                   (constrain_pattern_abstraction typ pos (R.anonymous_abstraction rhs))
             in
               (clause, guards, wrappers @ [{kind = Nested_Scope, close = wrap}], navigation)
             end
         | Case_Value (literal, _) =>
             (Clause_Wild, [T.binary Eq expression (T.literal literal)], [], [])
         | Case_Range (kind, lower, upper, _) =>
             let
               val upper_guard =
                 T.binary
                   (case kind of
                      RK_Exclusive => Lt
                    | RK_Inclusive => Le)
                   expression upper
             in
               (Clause_Wild, [T.binary And (T.binary Ge expression lower) upper_guard], [], [])
             end
         | Case_Slice_Suffix reversed_suffix =>
             let
               val reversed_expression = T.reverse_list expression
               val guard =
                 compile_nested_case compiler ctxt environment reversed_expression reversed_suffix
                   (T.literal T.true_value) (T.literal T.false_value)
               fun wrap rhs =
                 compile_nested_case compiler ctxt environment reversed_expression reversed_suffix
                   rhs T.undefined_value
             in
               (Clause_Wild, [guard], [{kind = Transformed_Scope, close = wrap}], [])
             end
         | _ => normalize_pattern_for_nested compiler ctxt environment bare_pattern)
    in
      (clause, guards, wrappers, navigation @ map slice_navigation_wrapper navigation_positions)
    end

  fun normalize_case_alternative compiler ctxt value (pattern, environment) =
    let
      val (clause_pattern, generated_guards, wrappers, navigation) =
        normalize_extended_pattern compiler ctxt environment (T.literal value) pattern
      val generated_test = fold extend_generated_test generated_guards NONE
      val scope = combine_scopes wrappers
      val direct_branch = try (bind_clause_pattern ctxt environment) clause_pattern
    in
      Case_Clause
        {structural_pattern = structural_pattern_of_clause ctxt environment clause_pattern,
         generated_test = generated_test,
         scope = scope,
         navigation = navigation,
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
      (Decision_Row
        {clause = Case_Clause {generated_test, scope = {kind, ...}, navigation, direct_branch, ...},
         source_guard, body, ...}) =
    (case (source_guard, generated_test, kind, direct_branch) of
       (NONE, NONE, Direct_Scope, SOME render) => SOME (render (apply_navigation navigation body))
     | _ => NONE)

  fun unconditional_total_row
      (Decision_Row
        {clause = Case_Clause {structural_pattern, generated_test, ...}, source_guard, ...}) =
    is_none generated_test andalso is_none source_guard andalso
      structural_is_total structural_pattern

  fun validate_row_reachability [] = ()
    | validate_row_reachability [_] = ()
    | validate_row_reachability (row :: rest) =
        if unconditional_total_row row
        then error "clauses are redundant"
        else validate_row_reachability rest

  fun row_arm (Decision_Row {position = {arm_index, ...}, ...}) = arm_index

  fun row_position (Decision_Row {position, ...}) = position

  fun row_pattern (Decision_Row {clause = Case_Clause {structural_pattern, ...}, ...}) =
    structural_pattern

  fun row_has_generated_test (Decision_Row {clause = Case_Clause {generated_test, ...}, ...}) =
    is_some generated_test

  fun row_has_source_guard (Decision_Row {source_guard, ...}) = is_some source_guard

  fun row_shape row = erase_structural_bindings (row_pattern row)

  datatype match_root_decision =
      Structural_Match_Root
    | Conditional_Match_Root
    | Binding_Match_Root

  fun drop_source_arm arm_index rows =
    drop_prefix (fn row => row_arm row = arm_index) rows

  fun row_exclusion row pattern =
    Decision_Exclusion {position = row_position row, pattern = pattern}

  fun same_outer_group (left, right) =
    structural_same_shape (left, right) orelse
      (structural_is_total left andalso structural_is_total right)

  fun add_group_row row group_pattern [] =
        [Structural_Group {pattern = group_pattern, members = [row]}]
    | add_group_row row group_pattern (Structural_Group {pattern, members} :: rest) =
        if same_outer_group (pattern, group_pattern)
        then Structural_Group {pattern = pattern, members = members @ [row]} :: rest
        else
          Structural_Group {pattern = pattern, members = members} ::
            add_group_row row group_pattern rest

  fun install_source_catchall row NONE =
        SOME (Structural_Group {pattern = row_pattern row, members = [row]})
    | install_source_catchall row (SOME (group as Structural_Group {pattern, ...})) =
        (case (pattern, row_pattern row) of
           (Structural_Any NONE, bound as Structural_Any (SOME _)) =>
             SOME (Structural_Group {pattern = bound, members = [row]})
         | _ => SOME group)

  fun add_root_group row (Outer_Group_Plan {groups, catchall}) =
    let
      val shape = row_shape row
      val group_pattern = structural_root_group_pattern shape
      val (groups', catchall') =
        if structural_is_any shape
        then (groups, install_source_catchall row catchall)
        else (add_group_row row group_pattern groups, catchall)
    in
      Outer_Group_Plan {groups = groups', catchall = catchall'}
    end

  fun transformed_root_tail
      (Decision_Row {clause = Case_Clause {scope = {kind = Transformed_Scope, ...}, ...}, ...}) =
        true
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

  fun emission_groups_of (Structural_Group {members, ...}) =
    fold (fn row => fn groups => add_group_row row (row_shape row) groups) members []

  fun emission_group_exclusions (Structural_Group {members, ...}) =
    (case members of
       [] => error "urust_expr: internal empty structural group"
     | first :: rest =>
         row_exclusion first (row_shape first) ::
           map (fn row => row_exclusion row (row_shape row)) (filter row_has_generated_test rest))

  fun group_starts_with_generated_test (Structural_Group {members, ...}) =
    (case members of
       first :: _ => row_has_generated_test first
     | [] => error "urust_expr: internal empty structural group")

  fun group_pattern (Structural_Group {pattern, ...}) = pattern

  fun remove_subsumed_emission_groups groups =
    let
      fun covered prior candidate =
        List.exists
          (fn group =>
            group_starts_with_generated_test group andalso
              structural_subsumes (group_pattern group, group_pattern candidate))
          prior
      fun retain _ [] = []
        | retain prior (group :: rest) =
            if covered prior group
            then retain prior rest
            else group :: retain (prior @ [group]) rest
    in retain [] groups end

  fun plan_root_suffix context planned_rows =
    let
      val Outer_Group_Plan {groups, catchall = source_catchall} =
        fold add_root_group planned_rows (Outer_Group_Plan {groups = [], catchall = NONE})
      fun group_is_coverage_complete (Structural_Group {pattern, members, ...}) =
        structural_is_total pattern andalso List.exists (structural_is_total o row_shape) members
      val coverage_complete_group =
        (case groups of
           [group] => if group_is_coverage_complete group then SOME group else NONE
         | _ => NONE)
      (*
        A single structurally total group containing a total source row is coverage-complete. Root
        emission must open that planned group directly instead of reconstructing a redundant root
        tail. This rule depends only on typed structural coverage, not on any particular constructor
        or tuple shape.
      *)
      val (prefix_rows, reconstruct_root_tail) =
        (case coverage_complete_group of
           SOME _ => (planned_rows, false)
         | NONE =>
             (case context of
                Match_Root => emission_root_prefix NONE [] planned_rows
              | Failure_Root => ([], not (null planned_rows))))
      val emission_groups =
        remove_subsumed_emission_groups
          (case coverage_complete_group of
             SOME group => [group]
           | NONE =>
               if reconstruct_root_tail
               then
                 fold
                   (fn row => fn planned_groups =>
                     if structural_is_any (row_shape row)
                     then planned_groups
                     else add_group_row row (row_shape row) planned_groups)
                   prefix_rows []
               else maps emission_groups_of groups)
      val emission_patterns = map (fn Structural_Group {pattern, ...} => pattern) emission_groups
      val emission_exclusions = maps emission_group_exclusions emission_groups
      val emission_catchall =
        if reconstruct_root_tail
        then
          if patterns_cover_all emission_patterns
          then NONE
          else
            SOME
              (the_default (Structural_Group {pattern = Structural_Any NONE, members = []})
                source_catchall)
        else
          (case source_catchall of
             NONE => NONE
           | SOME group => if patterns_cover_all emission_patterns then NONE else SOME group)
    in
      Root_Suffix_Plan
        {rows = planned_rows,
         groups = emission_groups,
         outer_catchall = emission_catchall,
         catchall_exclusions = emission_exclusions}
    end

  fun following_group_exclusion (Structural_Group {members, ...}) =
    (case members of
       [] => error "urust_expr: internal empty structural group"
     | first :: _ =>
         if row_has_generated_test first
         then NONE
         else SOME (row_exclusion first (row_shape first)))

  fun nested_failure_scope
      (Decision_Row
        {clause = Case_Clause {scope = {kind = Nested_Scope, ...}, generated_test = SOME _, ...},
         ...}) = true
    | nested_failure_scope _ = false

  fun rows_after_position _ [] = error "urust_expr: internal missing suffix row"
    | rows_after_position position (row :: rest) =
        if position = row_position row
        then rest
        else rows_after_position position rest

  fun nested_failure_suffix planned_rows (Structural_Group {members, ...}) =
    (case members of
       first :: _ =>
         if nested_failure_scope first
         then SOME (rows_after_position (row_position first) planned_rows)
         else NONE
     | [] => error "urust_expr: internal empty structural group")

  fun exclusion_position (Decision_Exclusion {position, ...}) = position

  fun exclusion_pattern (Decision_Exclusion {pattern, ...}) = pattern

  fun excluded_region exclusions position region =
    List.exists
      (fn exclusion =>
        exclusion_position exclusion = position andalso
          structural_semantically_subsumes (exclusion_pattern exclusion, region))
      exclusions

  fun row_intersection (Decision_State {region, exclusions, ...}) row =
    (case structural_intersection (region, row_shape row) of
       NONE => false
     | SOME matched => not (excluded_region exclusions (row_position row) matched))

  fun first_applicable _ [] = NONE
    | first_applicable state (row :: rest) =
        if row_intersection state row
        then SOME (row, rest)
        else first_applicable state rest

  fun add_exclusion (Decision_State {region, subject, exclusions}) position pattern =
    Decision_State
      {region = region, subject = subject,
       exclusions = Decision_Exclusion {position = position, pattern = pattern} :: exclusions}

  fun close_selected_clause (Case_Clause {generated_test, scope, navigation, ...}) selection
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
            Decision_Row
              {position = {arm_index = arm_index, alternative_index = alternative_index},
               clause =
                 normalize_case_alternative compile_pattern_case ctxt value (pattern, environment),
               source_guard = source_guard,
               body = body})
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

      val root_state =
        Decision_State
          {region = Structural_Any NONE,
           subject = Structural_Subject {value = value, children = []},
           exclusions = []}

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
             (Decision_Row
                {clause = (clause as Case_Clause {structural_pattern, generated_test, scope, ...}),
                 source_guard, body, position = (position as {arm_index, ...})},
              rest) =>
             let
               val shape = erase_structural_bindings structural_pattern

               fun compile_matched selection failure_state =
                 let
                   (* A generated-test miss tries the next alternative. A false source guard skips
                      the entire source arm. Choose the one emitted destination before closing the
                      clause; an absent test or guard constructs no failure term. *)
                   val alternative_failure =
                     Option.map
                       (fn _ =>
                         (case #kind scope of
                            Nested_Scope => compile_root_suffix Failure_Root rest
                          | Transformed_Scope => compile_root_suffix Failure_Root rest
                          | _ => compile_rows failure_state rest))
                       generated_test
                   val arm_failure =
                     Option.map
                       (fn _ =>
                         let val following = drop_source_arm arm_index rest in
                           (case (#kind scope, shape) of
                              (Direct_Scope, Structural_Node _) =>
                                compile_root_suffix Failure_Root following
                            | _ => compile_rows failure_state following)
                         end)
                       source_guard
                 in
                   close_selected_clause clause selection source_guard body
                     alternative_failure arm_failure
                 end
               val Decision_State {subject, exclusions, ...} = state
             in
               (case select_structural_clause ctxt structural_pattern state of
                  Reused_Clause_Selection witness => compile_matched witness state
                | Opened_Clause_Selection {covers_region, region, abstraction, witness} =>
                    let
                      val success =
                        compile_matched witness
                          (Decision_State
                            {region = region, subject = selection_subject witness,
                             exclusions = exclusions})
                      val failure =
                        if covers_region then []
                        else [compile_rows (add_exclusion state position shape) rest]
                    in
                      case_term_on (subject_value subject)
                        (abstraction success :: map (generated_wild ctxt) failure)
                    end)
             end)

      and compile_outer_pattern planned_rows exclusions pattern =
        let
          val Opened_Pattern {abstraction, subject} = fresh_pattern_subject ctxt pattern
          val state = Decision_State {region = pattern, subject = subject, exclusions = exclusions}
          val compiled = compile_rows state planned_rows
        in
          abstraction compiled
        end

      and compile_outer_group planned_rows exclusions (Structural_Group {pattern, ...}) =
        compile_outer_pattern planned_rows exclusions pattern

      and compile_outer_catchall planned_rows exclusions (Structural_Group {pattern, ...}) =
        (case pattern of
           Structural_Any NONE =>
             let
               val Decision_State {subject, ...} = root_state
               val state =
                 Decision_State {region = pattern, subject = subject, exclusions = exclusions}
             in
               generated_wild ctxt (compile_rows state planned_rows)
             end
         | Structural_Any (SOME _) => compile_outer_pattern planned_rows exclusions pattern
         | Structural_Node _ => error "urust_expr: internal non-wild outer catchall")

      and compile_reconstructed_branch (Structural_Group {pattern, ...}) remaining =
        let
          val Opened_Pattern {abstraction, ...} = fresh_pattern_subject ctxt pattern
        in
          abstraction (compile_root_suffix Failure_Root remaining)
        end

      and compile_emission_groups _ [] _ root_suffix = ([], root_suffix)
        | compile_emission_groups planned_rows (group :: rest) exclusions root_suffix =
            let
              val branch =
                (case root_suffix of
                   SOME remaining => compile_reconstructed_branch group remaining
                 | NONE => compile_outer_group planned_rows exclusions group)
              val exclusions' =
                (case root_suffix of
                   SOME _ => exclusions
                 | NONE =>
                     (case following_group_exclusion group of
                        NONE => exclusions
                      | SOME exclusion => exclusion :: exclusions))
              val root_suffix' =
                (case root_suffix of
                   SOME _ => root_suffix
                 | NONE => nested_failure_suffix planned_rows group)
              val (following, final_root_suffix) =
                compile_emission_groups planned_rows rest exclusions' root_suffix'
            in
              (branch :: following, final_root_suffix)
            end

      and emit_root_suffix
          (Root_Suffix_Plan {rows = planned_rows, groups, outer_catchall, catchall_exclusions}) =
        let
          val (group_branches, root_suffix) = compile_emission_groups planned_rows groups [] NONE
          val branches =
            group_branches @
              (case outer_catchall of
                 NONE => []
               | SOME group =>
                   [(case root_suffix of
                       SOME remaining => compile_reconstructed_branch group remaining
                     | NONE => compile_outer_catchall planned_rows catchall_exclusions group)])
        in selector_of branches end

      and compile_root_suffix context remaining =
        emit_root_suffix (plan_root_suffix context remaining)

      val selector =
        (case direct_structural_matrix () of
           SOME branches => selector_of branches
         | NONE => emit_root_suffix (plan_root_suffix Match_Root rows))
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
