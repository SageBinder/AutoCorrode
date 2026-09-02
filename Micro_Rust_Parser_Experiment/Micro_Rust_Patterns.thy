theory Micro_Rust_Patterns
  imports Micro_Rust_Resolution
begin

section\<open> Resolved patterns and case compilation \<close>

ML\<open>
signature URUST_PATTERNS =
sig
  type prepared_binding
  type prepared_case_arm
  type prepared_switch_arm

  datatype binder_site =
      Let_Const_Binder
    | Mutable_Let_Binder
    | For_Binder

  datatype mutable_rhs_mode =
      Plain_Rhs
    | Allocate_Rhs

  val position: URust_AST.ur_pat -> Position.T

  val prepare_binding:
    binder_site ->
      Proof.context ->
      URust_Resolution.environment ->
      URust_AST.ur_pat ->
      prepared_binding
  val binding_environment:
    prepared_binding -> URust_Resolution.environment
  val binding_abstraction:
    prepared_binding -> term -> term
  val mutable_rhs_mode: prepared_binding -> mutable_rhs_mode

  val select_match_flavour:
    URust_AST.match_flavour ->
      URust_AST.ur_arm list ->
      Position.T ->
      URust_AST.match_flavour

  val prepare_switch_arm:
    Proof.context -> URust_AST.ur_arm -> prepared_switch_arm
  val prepared_switch_keys: prepared_switch_arm -> term list
  val prepared_switch_body: prepared_switch_arm -> URust_AST.ur_expr

  val prepare_case_arm:
    Proof.context ->
      URust_Resolution.environment ->
      URust_AST.ur_arm ->
      prepared_case_arm
  val prepared_environment:
    prepared_case_arm -> URust_Resolution.environment
  val prepared_guard:
    prepared_case_arm -> (URust_AST.ur_expr * Position.T) option
  val prepared_body: prepared_case_arm -> URust_AST.ur_expr
  val prepared_direct_abstraction:
    prepared_case_arm -> (term -> term) option
  val prepared_is_total: prepared_case_arm -> bool
  val prepared_pattern_position: prepared_case_arm -> Position.T
  val prepared_legacy_linear_nodes: prepared_case_arm -> int
  val prepared_legacy_copies: prepared_case_arm -> int
  val prepared_legacy_expanded_nodes: prepared_case_arm -> int
  val compile_case:
    Proof.context ->
      term ->
      (prepared_case_arm * term option * term) list ->
      term
  val compile_case_with_fallback:
    Proof.context ->
      term ->
      term ->
      (prepared_case_arm * term option * term) list ->
      term
end
\<close>

text\<open>
For C1-I1 through C1-I4, constructor identities are resolved before allocation, a complete
pattern-local binder set is validated atomically, and all alternatives of one source or-pattern receive
one shared environment. The compiler consumes only prepared arms; it does not inspect or classify
source patterns again.
\<close>

ML\<open>
structure URust_Patterns : URUST_PATTERNS =
struct
  open URust_AST
  structure T = URust_Elab_Terms
  structure R = URust_Resolution

  datatype binder_site =
      Let_Const_Binder
    | Mutable_Let_Binder
    | For_Binder

  datatype mutable_rhs_mode =
      Plain_Rhs
    | Allocate_Rhs

  fun position (P_Wild pos) = pos
    | position (P_Ident (_, pos)) = pos
    | position (P_Literal payload) = literal_position payload
    | position (P_Constr (_, pos, _)) = pos
    | position (P_Tuple (_, pos)) = pos
    | position (P_Group pattern) = position pattern
    | position (P_Borrow (_, _, pos)) = pos
    | position (P_Alias (_, _, _, pos)) = pos
    | position (P_Range (_, _, _, pos)) = pos
    | position (P_Slice (_, pos)) = pos
    | position (P_Struct (_, pos, _)) = pos
    | position (P_Or (_, pos)) = pos

  fun reject_reference_patterns pattern =
    let
      fun reject (P_Borrow (_, _, pos)) =
            error ("urust_expr: reference patterns are not implemented" ^
              Position.here pos)
        | reject (P_Constr (_, _, arguments)) = List.app reject arguments
        | reject (P_Tuple (arguments, _)) = List.app reject arguments
        | reject (P_Group inner) = reject inner
        | reject (P_Alias (_, _, inner, _)) = reject inner
        | reject (P_Range (_, lower, upper, _)) =
            (reject lower; reject upper)
        | reject (P_Slice (items, _)) =
            List.app
              (fn SI_Pat nested => reject nested | SI_Rest _ => ()) items
        | reject (P_Struct (_, _, fields)) =
            List.app
              (fn SF_Field (_, _, nested) => reject nested
                | SF_Shorthand _ => ()
                | SF_Rest _ => ()) fields
        | reject (P_Or (alternatives, _)) = List.app reject alternatives
        | reject _ = ()
    in reject pattern end

  fun strip_groups (P_Group pattern) = strip_groups pattern
    | strip_groups pattern = pattern

  fun arm_pattern (UR_Arm (pattern, _, _)) = pattern
  fun arm_guard (UR_Arm (_, guard, _)) = guard

  fun classify_match arms pos =
    let
      fun case_compatible pattern =
        (case strip_groups pattern of
           P_Literal (LP_Integer _) => false
         | _ => true)
      fun switch_compatible pattern =
        (case strip_groups pattern of
           P_Literal (LP_Integer _) => true
         | P_Ident _ => true
         | P_Wild _ => true
         | _ => false)
      val patterns = map arm_pattern arms
    in
      if List.exists (is_some o arm_guard) arms then MF_Case
      else if List.all case_compatible patterns then MF_Case
      else if List.all switch_compatible patterns then MF_Switch
      else
        error ("urust_expr: mixed numeral and constructor patterns in bare `match`" ^
          Position.here pos)
    end

  fun first_guard_position [] = NONE
    | first_guard_position (UR_Arm (_, SOME (_, pos), _) :: _) = SOME pos
    | first_guard_position (_ :: rest) = first_guard_position rest

  fun select_match_flavour flavour arms pos =
    let
      val selected =
        (case flavour of
           MF_Auto => classify_match arms pos
         | explicit => explicit)
      val _ =
        (case (selected, first_guard_position arms) of
           (MF_Switch, SOME guard_pos) =>
             error ("urust_expr: guards are not supported in explicit `match_switch`" ^
               Position.here guard_pos)
         | _ => ())
    in selected end

  datatype resolution_policy =
      Always_Binder
    | Resolve_Constructor_Binding
    | Resolve_Constructor_Case

  datatype resolved_value =
      Resolved_Literal_Value of literal_payload
    | Resolved_Identifier_Value of string * Position.T

  datatype resolved_pattern =
      Resolved_Wild of Position.T
    | Resolved_Bind of R.binding_signature
    | Resolved_Constructor of
        R.constructor_info * Position.T * resolved_pattern list
    | Resolved_Tuple of resolved_pattern list * Position.T
    | Resolved_Alias of
        R.binding_signature * resolved_pattern * Position.T
    | Resolved_Value of literal_payload
    | Resolved_Range of
        range_kind * resolved_value * resolved_value * Position.T
    | Resolved_Slice of resolved_slice_item list * Position.T
    | Resolved_Or of resolved_pattern list * Position.T
  and resolved_slice_item =
      Resolved_Slice_Pattern of resolved_pattern
    | Resolved_Slice_Rest of Position.T

  datatype resolved_coverage =
      Coverage_Total
    | Coverage_Family of
        {name: string, members: term list, covered: term list}
    | Coverage_Partial

  fun resolved_position (Resolved_Wild pos) = pos
    | resolved_position (Resolved_Bind (_, pos, _)) = pos
    | resolved_position (Resolved_Constructor (_, pos, _)) = pos
    | resolved_position (Resolved_Tuple (_, pos)) = pos
    | resolved_position (Resolved_Alias (_, _, pos)) = pos
    | resolved_position (Resolved_Value payload) = literal_position payload
    | resolved_position (Resolved_Range (_, _, _, pos)) = pos
    | resolved_position (Resolved_Slice (_, pos)) = pos
    | resolved_position (Resolved_Or (_, pos)) = pos

  fun coverage_is_total Coverage_Total = true
    | coverage_is_total _ = false

  fun family_complete members covered =
    List.all
      (fn member =>
        List.exists (fn constructor => constructor aconv member) covered)
      members

  fun family_coverage name members covered =
    let
      val covered' =
        fold (fn constructor => insert (op aconv) constructor)
          covered []
    in
      if family_complete members covered'
      then Coverage_Total
      else
        Coverage_Family
          {name = name, members = members, covered = covered'}
    end

  fun same_family
      ({name = left_name, members = left_members, covered = _},
       {name = right_name, members = right_members, covered = _}) =
    left_name = right_name andalso
      eq_list (op aconv) (left_members, right_members)

  fun resolved_coverage pattern =
    let
      fun coverage (Resolved_Wild _) = Coverage_Total
        | coverage (Resolved_Bind _) = Coverage_Total
        | coverage
            (Resolved_Constructor (info, _, arguments)) =
            if List.all (coverage_is_total o coverage) arguments
            then
              (case R.constructor_family info of
                 SOME (name, members) =>
                   family_coverage name members
                     [R.constructor_term info]
               | NONE => Coverage_Partial)
            else Coverage_Partial
        | coverage (Resolved_Tuple (arguments, _)) =
            if List.all (coverage_is_total o coverage) arguments
            then Coverage_Total
            else Coverage_Partial
        | coverage (Resolved_Alias (_, inner, _)) = coverage inner
        | coverage (Resolved_Value _) = Coverage_Partial
        | coverage (Resolved_Range _) = Coverage_Partial
        | coverage (Resolved_Slice _) = Coverage_Partial
        | coverage (Resolved_Or (alternatives, _)) =
            let
              val alternatives' = map coverage alternatives
              val total =
                List.exists coverage_is_total alternatives'
              val partial =
                List.exists
                  (fn Coverage_Partial => true | _ => false)
                  alternatives'
              val families =
                map_filter
                  (fn Coverage_Family family => SOME family
                    | _ => NONE)
                  alternatives'
            in
              if total then Coverage_Total
              else if partial orelse null families
              then Coverage_Partial
              else
                let
                  val first = hd families
                in
                  if List.all (fn family =>
                        same_family (first, family)) (tl families)
                  then
                    family_coverage
                      (#name first) (#members first)
                      (maps #covered families)
                  else Coverage_Partial
                end
            end
    in coverage pattern end

  fun binding name pos =
    (name, pos, R.Binding_By_Value)

  fun resolve_value pattern =
    (case strip_groups pattern of
       P_Literal payload => Resolved_Literal_Value payload
     | P_Ident identifier => Resolved_Identifier_Value identifier
     | unsupported =>
         error ("urust_expr: invalid range-pattern endpoint" ^
           Position.here (position unsupported)))

  fun check_constructor_arity name pos info arguments =
    let
      val expected = R.constructor_arity info
      val actual = length arguments
    in
      if expected = actual then ()
      else
        error ("urust_expr: constructor " ^ quote name ^ " expects " ^
          string_of_int expected ^ " pattern argument(s), but got " ^
          string_of_int actual ^ Position.here pos)
    end

  fun resolve_pattern ctxt policy pattern =
    let
      fun resolve source_pattern =
        (case source_pattern of
           P_Wild pos => Resolved_Wild pos
         | P_Ident (name, pos) =>
             (case policy of
                Always_Binder => Resolved_Bind (binding name pos)
              | _ =>
                  (case R.resolve_constructor ctxt name of
                     NONE => Resolved_Bind (binding name pos)
                   | SOME info =>
                       (check_constructor_arity name pos info [];
                        R.report_constructor ctxt pos info;
                        Resolved_Constructor (info, pos, []))))
         | P_Literal (payload as LP_Integer (_, pos)) =>
             (case policy of
                Resolve_Constructor_Case =>
                  error ("urust_expr: numeric patterns are not supported in case patterns" ^
                    Position.here pos)
              | _ => Resolved_Value payload)
         | P_Literal payload => Resolved_Value payload
         | P_Constr (name, pos, arguments) =>
              (case R.resolve_constructor ctxt name of
                NONE =>
                  error ("urust_expr: `" ^ name ^
                    "` is not a known constructor" ^ Position.here pos)
              | SOME info =>
                  (check_constructor_arity name pos info arguments;
                   R.report_constructor ctxt pos info;
                   Resolved_Constructor
                     (info, pos, map resolve arguments)))
         | P_Tuple (arguments, pos) =>
             Resolved_Tuple (map resolve arguments, pos)
         | P_Group inner => resolve inner
         | P_Borrow (_, _, pos) =>
             error ("urust_expr: reference patterns are not implemented" ^
               Position.here pos)
         | P_Alias ("_", pos, _, _) =>
             error ("urust_expr: alias pattern binder cannot be `_`" ^
               Position.here pos)
         | P_Alias (name, pos, inner, alias_pos) =>
             Resolved_Alias (binding name pos, resolve inner, alias_pos)
         | P_Range (_, P_Range _, _, pos) =>
             error ("urust_expr: range patterns are non-associative" ^
               Position.here pos)
         | P_Range (kind, lower, upper, pos) =>
             Resolved_Range
               (kind, resolve_value lower, resolve_value upper, pos)
         | P_Slice (items, pos) =>
             let
               fun resolve_items _ [] = []
                 | resolve_items seen_rest (SI_Rest rest_pos :: rest) =
                     if seen_rest then
                       error ("urust_expr: slice pattern has multiple `..` rest entries" ^
                         Position.here rest_pos)
                     else
                       Resolved_Slice_Rest rest_pos ::
                         resolve_items true rest
                 | resolve_items seen_rest (SI_Pat nested :: rest) =
                     Resolved_Slice_Pattern (resolve nested) ::
                       resolve_items seen_rest rest
             in Resolved_Slice (resolve_items false items, pos) end
         | P_Struct (name, pos, fields) =>
             (case R.resolve_struct_pattern ctxt (name, pos, fields) of
                R.Resolved_Constructor_Struct (info, ordered) =>
                  let
                    val _ = R.report_constructor ctxt pos info
                    fun resolve_field (selector, field_pos, nested) =
                      (case field_pos of
                         SOME source_pos =>
                           R.report_selector ctxt source_pos selector
                       | NONE => ();
                       resolve nested)
                  in
                    Resolved_Constructor
                      (info, pos, map resolve_field ordered)
                  end
              | R.Resolved_Record_Struct (record_name, _) =>
                  R.unsupported_record_pattern record_name pos)
         | P_Or (alternatives, pos) =>
             Resolved_Or (map resolve alternatives, pos))
    in
      reject_reference_patterns pattern;
      resolve pattern
    end

  fun signature_name (name, _, _) = name
  fun signature_position (_, pos, _) = pos
  fun signature_mode (_, _, mode) = mode

  fun duplicate_binder name pos original_pos =
    error ("urust_expr: duplicate pattern binder " ^ quote name ^
      Position.here pos ^ "\nThe original binder is here" ^
      Position.here original_pos)

  fun validate_unique signatures =
    let
      fun add binder_sig table =
        let
          val name = signature_name binder_sig
          val pos = signature_position binder_sig
        in
          (case Symtab.lookup table name of
             NONE => Symtab.update (name, binder_sig) table
           | SOME original =>
               duplicate_binder name pos (signature_position original))
        end
      val _ = fold add signatures Symtab.empty
    in signatures end

  fun signature_table signatures =
    Symtab.make
      (map (fn binder_sig =>
        (signature_name binder_sig, binder_sig)) signatures)

  fun compare_or_alternative or_pos first_signatures alternative_signatures =
    let
      val first = signature_table first_signatures
      val alternative = signature_table alternative_signatures
      fun check_first (name, original) =
        (case Symtab.lookup alternative name of
           NONE =>
             error ("urust_expr: or-pattern alternative is missing binder " ^
               quote name ^ Position.here or_pos ^
               "\nThe first alternative binds it here" ^
               Position.here (signature_position original))
         | SOME current =>
             if signature_mode current = signature_mode original then ()
             else
               error ("urust_expr: or-pattern binder " ^ quote name ^
                 " has a different binding mode" ^
                 Position.here (signature_position current) ^
                 "\nThe first alternative binds it here" ^
                 Position.here (signature_position original)))
      fun check_extra (name, current) =
        if Symtab.defined first name then ()
        else
          error ("urust_expr: or-pattern alternative has extra binder " ^
            quote name ^ Position.here (signature_position current))
    in
      List.app check_first (Symtab.dest first);
      List.app check_extra (Symtab.dest alternative)
    end

  fun collect_bindings pattern =
    let
      fun collect (Resolved_Wild _) = []
        | collect (Resolved_Bind binder_sig) = [binder_sig]
        | collect (Resolved_Constructor (_, _, arguments)) =
            validate_unique (maps collect arguments)
        | collect (Resolved_Tuple (arguments, _)) =
            validate_unique (maps collect arguments)
        | collect (Resolved_Alias (binder_sig, inner, _)) =
            validate_unique (binder_sig :: collect inner)
        | collect (Resolved_Value _) = []
        | collect (Resolved_Range _) = []
        | collect (Resolved_Slice (items, _)) =
            validate_unique
              (maps
                (fn Resolved_Slice_Pattern nested => collect nested
                  | Resolved_Slice_Rest _ => []) items)
        | collect (Resolved_Or ([], pos)) =
            error ("urust_expr: internal empty or-pattern" ^ Position.here pos)
        | collect (Resolved_Or (first :: rest, pos)) =
            let
              val first_signatures = collect first
              val rest_signatures = map collect rest
              val _ =
                List.app
                  (compare_or_alternative pos first_signatures)
                  rest_signatures
            in first_signatures end
    in validate_unique (collect pattern) end

  fun lookup_signature environment binder_sig =
    let
      val name = signature_name binder_sig
      val pos = signature_position binder_sig
    in
      (case R.lookup_local environment name of
         SOME free => free
       | NONE =>
           error ("urust_expr: internal unallocated pattern binder " ^
             quote name ^ Position.here pos))
    end

  fun direct_abstraction ctxt report_wildcards allow_alias environment pattern =
    let
      fun direct (Resolved_Bind binder_sig) =
            let val free = lookup_signature environment binder_sig
            in SOME (fn body => Term.lambda free body) end
        | direct (Resolved_Wild pos) =
            (if report_wildcards then R.report_wildcard ctxt pos else ();
             SOME (fn body => R.anonymous_abstraction body))
        | direct (Resolved_Tuple (patterns, _)) =
            let
              val abstractions = map direct patterns
            in
              if List.all is_some abstractions then
                let
                  val concrete = map the abstractions
                  fun tuple_abstraction [abstraction] body =
                        T.case_product
                          (abstraction (R.anonymous_abstraction body))
                    | tuple_abstraction (abstraction :: rest) body =
                        T.case_product
                          (abstraction (tuple_abstraction rest body))
                    | tuple_abstraction [] _ =
                        error "urust_expr: internal empty tuple pattern"
                in SOME (fn body => tuple_abstraction concrete body) end
              else NONE
            end
        | direct (Resolved_Alias (binder_sig, inner, _)) =
            if allow_alias then
              (case direct inner of
                 NONE => NONE
               | SOME inner_abstraction =>
                   let
                     val alias_free = lookup_signature environment binder_sig
                     val matched =
                       Free
                         ("_urust_while_let_" ^
                           string_of_int (serial ()), dummyT)
                     fun abstraction body =
                       Term.lambda matched
                         (T.bind (T.literal matched)
                           (Term.lambda alias_free
                             (Term.betapply
                               (inner_abstraction body, matched))))
                   in SOME abstraction end)
            else NONE
        | direct _ = NONE
    in direct pattern end

  fun binder_site_description Let_Const_Binder =
        "an irrefutable (let/const) binder position"
    | binder_site_description Mutable_Let_Binder =
        "a mutable binding position"
    | binder_site_description For_Binder =
        "a `for` binder position"

  datatype prepared_binding =
    Prepared_Binding of
      {environment: R.environment,
       abstraction: term -> term,
       rhs_mode: mutable_rhs_mode}

  fun mutable_source_mode pattern =
    (case pattern of
       P_Ident _ => Allocate_Rhs
     | P_Wild _ => Allocate_Rhs
     | P_Tuple _ => Plain_Rhs
     | _ =>
         error ("urust_expr: invalid mutable binding pattern" ^
           " (expected identifier, `_`, or top-level tuple destructuring)" ^
           Position.here (position pattern)))

  fun prepare_binding site ctxt environment pattern =
    let
      val policy =
        (case site of
           For_Binder => Resolve_Constructor_Binding
         | _ => Always_Binder)
      val resolved = resolve_pattern ctxt policy pattern
      val signatures = collect_bindings resolved
      val rhs_mode =
        (case site of
           Mutable_Let_Binder => mutable_source_mode pattern
         | _ => Plain_Rhs)
      val environment' =
        R.allocate_locals ctxt environment signatures
      val abstraction =
        (case direct_abstraction ctxt true false environment' resolved of
           SOME abstraction => abstraction
         | NONE =>
             let
               val diagnostic_site =
                 (case (site, rhs_mode) of
                    (Mutable_Let_Binder, Plain_Rhs) =>
                      Let_Const_Binder
                  | _ => site)
             in
               error ("urust_expr: unsupported or refutable pattern in " ^
                 binder_site_description diagnostic_site ^
                 Position.here (resolved_position resolved))
             end)
    in
      Prepared_Binding
        {environment = environment',
         abstraction = abstraction,
         rhs_mode = rhs_mode}
    end

  fun binding_environment
      (Prepared_Binding {environment, ...}) = environment
  fun binding_abstraction
      (Prepared_Binding {abstraction, ...}) = abstraction
  fun mutable_rhs_mode
      (Prepared_Binding {rhs_mode, ...}) = rhs_mode

  datatype prepared_switch_arm =
    Prepared_Switch_Arm of term list * ur_expr

  fun switch_keys ctxt pattern =
    (case strip_groups pattern of
       P_Or (alternatives, _) => maps (switch_keys ctxt) alternatives
     | P_Literal (LP_Integer (lexeme, pos)) =>
         [T.option_some (T.integer_value pos lexeme)]
     | P_Wild pos => (R.report_wildcard ctxt pos; [T.option_none])
     | P_Ident (name, pos) =>
         error ("urust_expr: unsupported match_switch key " ^ quote name ^
           " (numeral or `_` only; const-id / path keys not yet supported)" ^
           Position.here pos)
     | unsupported =>
         error ("urust_expr: unsupported match_switch pattern" ^
           " (numeral, `_`, or an or-list of those; binding patterns need" ^
           " `match_case`)" ^ Position.here (position unsupported)))

  fun prepare_switch_arm ctxt (UR_Arm (pattern, guard, body)) =
    let
      val _ = reject_reference_patterns pattern
      val _ =
        (case guard of
           NONE => ()
         | SOME (_, pos) =>
             error ("urust_expr: guards are not supported in explicit `match_switch`" ^
               Position.here pos))
    in Prepared_Switch_Arm (switch_keys ctxt pattern, body) end

  fun prepared_switch_keys (Prepared_Switch_Arm (keys, _)) = keys
  fun prepared_switch_body (Prepared_Switch_Arm (_, body)) = body

  datatype basic_case_pattern =
      Basic_Wild
    | Basic_Generated of term
    | Basic_Constructor of
        R.constructor_info * Position.T * basic_case_pattern list
    | Basic_Resolved of term * basic_case_pattern list
    | Basic_Tuple of basic_case_pattern list

  datatype case_pattern_tree =
      Pattern_Constant of term
    | Pattern_Slot of int
    | Pattern_Application of term * case_pattern_tree list

  datatype payload_layout =
      Payload_None
    | Payload_Binder of R.binding_signature
    | Payload_Product of payload_layout * payload_layout

  type legacy_pattern_metric =
    {linear_nodes: int,
     copies: int,
     expanded_nodes: int}

  type compiled_plan =
    {matcher: term,
     layout: payload_layout,
     direct: (term -> term) option,
     legacy: legacy_pattern_metric}

  datatype pattern_plan =
    Pattern_Plan of
      {matcher: term,
       binders: term list,
       direct: (term -> term) option,
       position: Position.T,
       legacy: legacy_pattern_metric}

  datatype prepared_case_arm =
    Prepared_Case_Arm of
      {plan: pattern_plan,
       environment: R.environment,
       guard: (ur_expr * Position.T) option,
       body: ur_expr,
       total: bool}

  val legacy_copy_limit = 256
  val legacy_saturated_copy = legacy_copy_limit + 1

  fun saturating_add limit left right =
    if left >= limit orelse right >= limit - left
    then limit
    else left + right

  fun saturating_multiply limit left right =
    if left = 0 orelse right = 0 then 0
    else if left >= limit orelse right >= limit orelse left > limit div right
    then limit
    else left * right

  fun saturating_copy_add left right =
    saturating_add legacy_saturated_copy left right

  fun saturating_copy_multiply left right =
    saturating_multiply legacy_saturated_copy left right

  fun expanded_node_limit linear_nodes =
    legacy_copy_limit * linear_nodes + 1

  fun cap_expanded linear_nodes expanded_nodes =
    Int.min (expanded_nodes, expanded_node_limit linear_nodes)

  val empty_legacy_metric : legacy_pattern_metric =
    {linear_nodes = 0, copies = 1, expanded_nodes = 0}

  val leaf_legacy_metric : legacy_pattern_metric =
    {linear_nodes = 1, copies = 1, expanded_nodes = 1}

  fun unary_legacy_metric
      ({linear_nodes, copies, expanded_nodes} : legacy_pattern_metric) =
    let
      val linear_nodes' = linear_nodes + 1
      val limit = expanded_node_limit linear_nodes'
    in
      {linear_nodes = linear_nodes',
       copies = copies,
       expanded_nodes =
         saturating_add limit copies expanded_nodes}
    end

  fun cartesian_legacy_metric include_parent metrics =
    let
      val child_linear =
        fold (fn metric => Integer.add (#linear_nodes metric))
          metrics 0
      val linear_nodes =
        child_linear + (if include_parent then 1 else 0)
      val copies =
        fold (fn metric =>
          saturating_copy_multiply (#copies metric))
          metrics 1
      val limit = expanded_node_limit linear_nodes
      fun other_copies selected =
        fold_index
          (fn (index, metric) => fn product =>
            if index = selected then product
            else saturating_multiply limit (#copies metric) product)
          metrics 1
      val child_expanded =
        fold_index
          (fn (index, metric) => fn total =>
            saturating_add limit total
              (saturating_multiply limit
                (#expanded_nodes metric)
                (other_copies index)))
          metrics 0
      val parent_expanded =
        if include_parent then copies else 0
    in
      {linear_nodes = linear_nodes,
       copies = copies,
       expanded_nodes =
         saturating_add limit parent_expanded child_expanded}
    end

  fun choice_legacy_metric metrics =
    let
      val linear_nodes =
        1 + fold (fn metric => Integer.add (#linear_nodes metric))
          metrics 0
      val limit = expanded_node_limit linear_nodes
    in
      {linear_nodes = linear_nodes,
       copies =
         fold (fn metric =>
           saturating_copy_add (#copies metric))
           metrics 0,
       expanded_nodes =
         cap_expanded linear_nodes
           (fold (fn metric =>
             saturating_add limit (#expanded_nodes metric))
             metrics 1)}
    end

  fun split_resolved_slice_items items =
    let
      fun split prefix rest_pos suffix [] =
            (rev prefix, rest_pos, rev suffix)
        | split prefix NONE suffix
            (Resolved_Slice_Rest pos :: rest) =
            split prefix (SOME pos) suffix rest
        | split _ (SOME _) _ (Resolved_Slice_Rest pos :: _) =
            error ("urust_expr: internal duplicate slice rest" ^
              Position.here pos)
        | split prefix rest_pos suffix
            (Resolved_Slice_Pattern pattern :: rest) =
            if is_some rest_pos
            then split prefix rest_pos (pattern :: suffix) rest
            else split (pattern :: prefix) rest_pos suffix rest
    in split [] NONE [] items end

  fun resolved_value_term ctxt environment value =
    (case value of
       Resolved_Literal_Value payload =>
         T.literal (R.literal_value ctxt environment payload)
     | Resolved_Identifier_Value identifier =>
         R.literal_identifier ctxt environment identifier)

  fun instantiate_pattern arguments tree =
    (case tree of
       Pattern_Constant term => term
     | Pattern_Slot index => nth arguments index
     | Pattern_Application (constructor, nested) =>
         Term.list_comb
           (constructor, map (instantiate_pattern arguments) nested))

  fun abstract_slots wrap slots make_inner =
    let
      val count = length slots
      val arguments =
        map_index
          (fn (_, SOME free) => free
            | (index, NONE) => Bound (count - 1 - index))
          slots
    in
      fold_rev (fn slot => fn term =>
          wrap
            (case slot of
               SOME free => Term.lambda free term
             | NONE => R.anonymous_abstraction term))
        slots (make_inner arguments)
    end

  fun bind_basic_pattern pattern =
    let
      fun add_slot slot (slots_rev, count) =
        (Pattern_Slot count, (slot :: slots_rev, count + 1))

      fun walk Basic_Wild state = add_slot NONE state
        | walk (Basic_Generated free) state =
            add_slot (SOME free) state
        | walk (Basic_Constructor (info, _, arguments)) state =
            let
              val (trees, state') = fold_map walk arguments state
            in
              (Pattern_Application
                (R.constructor_term info, trees), state')
            end
        | walk (Basic_Resolved (constructor, arguments)) state =
            let val (trees, state') = fold_map walk arguments state
            in (Pattern_Application (constructor, trees), state') end
        | walk (Basic_Tuple arguments) state =
            let
              fun tuple_tree [] nested_state =
                    (Pattern_Constant T.tuple_nil_constructor, nested_state)
                | tuple_tree (argument :: rest) nested_state =
                    let
                      val (argument_tree, state') =
                        walk argument nested_state
                      val (rest_tree, state'') =
                        tuple_tree rest state'
                    in
                      (Pattern_Application
                        (T.pair_constructor,
                         [argument_tree, rest_tree]),
                       state'')
                    end
            in tuple_tree arguments state end

      val (tree, (slots_rev, _)) = walk pattern ([], 0)
    in
      fn body =>
        abstract_slots T.case_abstraction (rev slots_rev)
          (fn arguments =>
            T.case_element (instantiate_pattern arguments tree) body)
    end

  fun source_pack [] = HOLogic.unit
    | source_pack [field] = field
    | source_pack (field :: rest) =
        T.pair field (source_pack rest)

  fun pattern_destructor exhaustive pattern fields =
    let
      val value =
        Free
          ("_urust_destructure_value_" ^
            string_of_int (serial ()), dummyT)
      val accept =
        Free
          ("_urust_destructure_accept_" ^
            string_of_int (serial ()), dummyT)
      val reject =
        Free
          ("_urust_destructure_reject_" ^
            string_of_int (serial ()), dummyT)
      val success =
        bind_basic_pattern pattern
          (accept $ source_pack fields)
      val branches =
        if exhaustive then
          T.case_cons success T.case_nil
        else
          T.case_cons success
            (T.case_cons
              (bind_basic_pattern Basic_Wild reject)
              T.case_nil)
    in
      Term.lambda value
        (Term.lambda accept
          (Term.lambda reject
            (T.case_guard T.true_value value branches)))
    end

  fun layout_signatures Payload_None = []
    | layout_signatures (Payload_Binder binder_sig) = [binder_sig]
    | layout_signatures (Payload_Product (left, right)) =
        layout_signatures left @ layout_signatures right

  fun same_signature (left, right) =
    signature_name left = signature_name right andalso
      signature_mode left = signature_mode right

  fun same_layout (Payload_None, Payload_None) = true
    | same_layout
        (Payload_Binder left, Payload_Binder right) =
        same_signature (left, right)
    | same_layout
        (Payload_Product (left0, right0),
         Payload_Product (left1, right1)) =
        same_layout (left0, left1) andalso
          same_layout (right0, right1)
    | same_layout _ = false

  fun canonical_layout [] = Payload_None
    | canonical_layout (binder_sig :: rest) =
        Payload_Product
          (Payload_Binder binder_sig, canonical_layout rest)

  fun first_projection value =
    Const (\<^const_name>\<open>Product_Type.fst\<close>, dummyT) $ value

  fun second_projection value =
    Const (\<^const_name>\<open>Product_Type.snd\<close>, dummyT) $ value

  fun payload_bindings value layout =
    (case layout of
       Payload_None => []
     | Payload_Binder binder_sig => [(signature_name binder_sig, value)]
     | Payload_Product (left, right) =>
         payload_bindings (first_projection value) left @
           payload_bindings (second_projection value) right)

  fun payload_pack [] = HOLogic.unit
    | payload_pack (value :: rest) =
        T.pair value (payload_pack rest)

  fun canonicalize_plan signatures
      ({matcher, layout, direct, legacy} : compiled_plan) =
    let
      val target_layout = canonical_layout signatures
    in
      if same_layout (layout, target_layout) then
        {matcher = matcher,
         layout = layout,
         direct = direct,
         legacy = legacy}
      else
        let
          val source =
            Free
              ("_urust_payload_source_" ^
                string_of_int (serial ()), dummyT)
          val payload =
            Free
              ("_urust_payload_" ^
                string_of_int (serial ()), dummyT)
          val available = payload_bindings payload layout
          fun select binder_sig =
            (case AList.lookup (op =) available
                (signature_name binder_sig) of
               SOME value => value
             | NONE =>
                 error ("urust_expr: internal missing matcher payload " ^
                   quote (signature_name binder_sig) ^
                   Position.here (signature_position binder_sig)))
          val mapping =
            Term.lambda source
              (Term.lambda payload
                (payload_pack (map select signatures)))
        in
          {matcher = T.matcher_map mapping matcher,
           layout = target_layout,
           direct = direct,
           legacy = legacy}
        end
    end

  fun unit_plan () : compiled_plan =
    let
      val value =
        Free
          ("_urust_match_unit_" ^
            string_of_int (serial ()), dummyT)
    in
      {matcher =
         T.matcher_succeed
           (Term.lambda value HOLogic.unit),
       layout = Payload_None,
       direct = NONE,
       legacy = leaf_legacy_metric}
    end

  fun binder_plan environment binder_sig : compiled_plan =
    let
      val value =
        Free
          ("_urust_match_binder_" ^
            string_of_int (serial ()), dummyT)
      val free = lookup_signature environment binder_sig
    in
      {matcher =
         T.matcher_succeed (Term.lambda value value),
       layout = Payload_Binder binder_sig,
       direct = SOME (fn body => Term.lambda free body),
       legacy = leaf_legacy_metric}
    end

  fun wildcard_plan ctxt pos : compiled_plan =
    let
      val _ = R.report_wildcard ctxt pos
      val base = unit_plan ()
    in
      {matcher = #matcher base,
       layout = #layout base,
       direct = SOME R.anonymous_abstraction,
       legacy = #legacy base}
    end

  fun test_plan predicate : compiled_plan =
    let
      val source =
        Free
          ("_urust_test_source_" ^
            string_of_int (serial ()), dummyT)
      val payload =
        Free
          ("_urust_test_payload_" ^
            string_of_int (serial ()), dummyT)
      val discard =
        Term.lambda source
          (Term.lambda payload HOLogic.unit)
    in
      {matcher =
         T.matcher_map discard (T.matcher_test predicate),
       layout = Payload_None,
       direct = NONE,
       legacy = leaf_legacy_metric}
    end

  fun combine_plans [] =
        let val plan = unit_plan ()
        in
          {matcher = #matcher plan,
           layout = #layout plan,
           direct = #direct plan,
           legacy = empty_legacy_metric}
        end
    | combine_plans [plan] = plan
    | combine_plans (left :: rest) =
        let
          val right = combine_plans rest
        in
          {matcher =
             T.matcher_product (#matcher left) (#matcher right),
           layout =
             Payload_Product (#layout left, #layout right),
           direct = NONE,
           legacy =
             cartesian_legacy_metric false
               [#legacy left, #legacy right]}
        end

  fun tuple_direct plans =
    if List.all (is_some o #direct) plans then
      let
        val abstractions = map (the o #direct) plans
        fun tuple_abstraction [abstraction] body =
              T.case_product
                (abstraction (R.anonymous_abstraction body))
          | tuple_abstraction (abstraction :: rest) body =
              T.case_product
                (abstraction (tuple_abstraction rest body))
          | tuple_abstraction [] _ =
              error "urust_expr: internal empty tuple pattern"
      in SOME (fn body => tuple_abstraction abstractions body) end
    else NONE

  fun fresh_fields count =
    map (fn index =>
      Free
        ("_urust_match_field_" ^ string_of_int index ^ "_" ^
          string_of_int (serial ()), dummyT))
      (0 upto (count - 1))

  fun destructured_plan exhaustive pattern fields children direct :
      compiled_plan =
    let
      val combined = combine_plans children
      val destructor =
        pattern_destructor exhaustive pattern fields
    in
      {matcher =
         T.matcher_destructure destructor (#matcher combined),
       layout = #layout combined,
       direct = direct,
       legacy =
         cartesian_legacy_metric true
           (map #legacy children)}
    end

  fun compile_pattern_plan ctxt environment signatures resolved =
    let
      fun compile source_pattern : compiled_plan =
        (case source_pattern of
           Resolved_Wild pos => wildcard_plan ctxt pos
         | Resolved_Bind binder_sig =>
             binder_plan environment binder_sig
         | Resolved_Constructor (info, pos, arguments) =>
             let
               val children = map compile arguments
               val fields = fresh_fields (length arguments)
               val exhaustive =
                 (case R.constructor_family info of
                    SOME (_, [_]) => true
                  | _ => false)
               val basic =
                 Basic_Constructor
                   (info, pos, map Basic_Generated fields)
             in
               destructured_plan exhaustive basic fields children NONE
             end
         | Resolved_Tuple (arguments, _) =>
             let
               val children = map compile arguments
               val fields = fresh_fields (length arguments)
               val basic =
                 Basic_Tuple (map Basic_Generated fields)
             in
               destructured_plan true basic fields children
                 (tuple_direct children)
             end
         | Resolved_Alias (binder_sig, inner, _) =>
             let
               val compiled = compile inner
               val value =
                 Free
                   ("_urust_alias_value_" ^
                     string_of_int (serial ()), dummyT)
               val payload =
                 Free
                   ("_urust_alias_payload_" ^
                     string_of_int (serial ()), dummyT)
               val mapping =
                 Term.lambda value
                   (Term.lambda payload
                     (T.pair value payload))
               val alias_free =
                 lookup_signature environment binder_sig
               val direct =
                 (case #direct compiled of
                    NONE => NONE
                  | SOME inner_abstraction =>
                      let
                        val matched =
                          Free
                            ("_urust_direct_alias_" ^
                              string_of_int (serial ()), dummyT)
                      in
                        SOME (fn body =>
                          Term.lambda matched
                            (T.bind (T.literal matched)
                              (Term.lambda alias_free
                                (Term.betapply
                                  (inner_abstraction body, matched)))))
                      end)
             in
               {matcher =
                  T.matcher_map mapping (#matcher compiled),
                layout =
                  Payload_Product
                    (Payload_Binder binder_sig, #layout compiled),
                direct = direct,
                legacy =
                  unary_legacy_metric (#legacy compiled)}
             end
         | Resolved_Value payload =>
             let
               val literal =
                 R.literal_value ctxt environment payload
               val value =
                 Free
                   ("_urust_value_test_" ^
                     string_of_int (serial ()), dummyT)
               val predicate =
                 Term.lambda value
                   (T.binary Eq
                     (T.literal value) (T.literal literal))
             in test_plan predicate end
         | Resolved_Range (kind, lower, upper, _) =>
             let
               val lower' =
                 resolved_value_term ctxt environment lower
               val upper' =
                 resolved_value_term ctxt environment upper
               val value =
                 Free
                   ("_urust_range_test_" ^
                     string_of_int (serial ()), dummyT)
               val expression = T.literal value
               val predicate =
                 Term.lambda value
                   (T.binary And
                     (T.binary Ge expression lower')
                     (T.binary
                       (case kind of
                          RK_Exclusive => Lt
                        | RK_Inclusive => Le)
                       expression upper'))
             in test_plan predicate end
         | Resolved_Slice (items, _) => compile_slice items
         | Resolved_Or ([], pos) =>
             error ("urust_expr: internal empty resolved or-pattern" ^
               Position.here pos)
         | Resolved_Or (alternatives, _) =>
             let
               val compiled = map compile alternatives
               val alternative_signatures =
                 layout_signatures (#layout (hd compiled))
               val canonical =
                 map
                   (canonicalize_plan alternative_signatures)
                   compiled
               fun choices [plan] = #matcher plan
                 | choices (plan :: rest) =
                     T.matcher_choice (#matcher plan) (choices rest)
                 | choices [] =
                     error "urust_expr: internal empty matcher choice"
             in
              {matcher = choices canonical,
                layout = canonical_layout alternative_signatures,
                direct = NONE,
                legacy =
                  choice_legacy_metric
                    (map #legacy canonical)}
             end)

      and compile_slice items =
        let
          fun nil_plan () =
            destructured_plan false
              (Basic_Resolved (T.list_nil_constructor, []))
              [] [] NONE

          fun cons_plan head tail =
            let
              val fields = fresh_fields 2
              val basic =
                Basic_Resolved
                  (T.list_cons_constructor,
                   map Basic_Generated fields)
            in
              destructured_plan false basic fields [head, tail] NONE
            end

          fun chain [] tail = tail
            | chain (pattern :: rest) tail =
                let
                  val head = compile pattern
                  val tail' = chain rest tail
                in cons_plan head tail' end

          fun reverse_plan plan =
            let
              val value =
                Free
                  ("_urust_slice_reverse_" ^
                    string_of_int (serial ()), dummyT)
              val lifting =
                Term.lambda value
                  (T.reverse_list (T.literal value))
            in
              {matcher =
                 T.matcher_lift lifting (#matcher plan),
               layout = #layout plan,
               direct = NONE,
               legacy =
                 unary_legacy_metric (#legacy plan)}
            end

          val (prefix, rest_pos, suffix) =
            split_resolved_slice_items items
          val tail =
            (case rest_pos of
               NONE => nil_plan ()
             | SOME _ =>
                 if null suffix then unit_plan ()
                 else
                   reverse_plan
                     (chain (rev suffix) (nil_plan ())))
        in chain prefix tail end

      val compiled =
        canonicalize_plan signatures (compile resolved)
      val binders =
        map (lookup_signature environment) signatures
    in
      Pattern_Plan
        {matcher = #matcher compiled,
         binders = binders,
         direct = #direct compiled,
         position = resolved_position resolved,
         legacy = #legacy compiled}
    end

  fun prepare_case_arm ctxt environment
      (UR_Arm (pattern, guard, body)) =
    let
      val resolved = resolve_pattern ctxt Resolve_Constructor_Case pattern
      val signatures = collect_bindings resolved
      val arm_environment =
        R.allocate_locals ctxt environment signatures
      val plan =
        compile_pattern_plan ctxt arm_environment signatures resolved
      val total =
        coverage_is_total (resolved_coverage resolved)
    in
      Prepared_Case_Arm
        {plan = plan,
         environment = arm_environment,
         guard = guard,
         body = body,
         total = total}
    end

  fun prepared_environment
      (Prepared_Case_Arm {environment, ...}) = environment
  fun prepared_guard
      (Prepared_Case_Arm {guard, ...}) = guard
  fun prepared_body
      (Prepared_Case_Arm {body, ...}) = body
  fun prepared_direct_abstraction
      (Prepared_Case_Arm
        {plan = Pattern_Plan {direct, ...}, ...}) = direct
  fun prepared_is_total
      (Prepared_Case_Arm {total, ...}) = total
  fun prepared_pattern_position
      (Prepared_Case_Arm
        {plan = Pattern_Plan {position, ...}, ...}) = position
  fun prepared_legacy_linear_nodes
      (Prepared_Case_Arm
        {plan =
          Pattern_Plan
            {legacy = {linear_nodes, ...}, ...}, ...}) =
        linear_nodes
  fun prepared_legacy_copies
      (Prepared_Case_Arm
        {plan =
          Pattern_Plan
            {legacy = {copies, ...}, ...}, ...}) =
        copies
  fun prepared_legacy_expanded_nodes
      (Prepared_Case_Arm
        {plan =
          Pattern_Plan
            {legacy = {expanded_nodes, ...}, ...}, ...}) =
        expanded_nodes

  fun payload_abstraction [] body =
        R.anonymous_abstraction body
    | payload_abstraction (binder :: rest) body =
        T.case_product
          (Term.lambda binder
            (payload_abstraction rest body))

  fun compile_case_internal ctxt explicit_fallback scrutinee arms =
    let
      val value =
        Free
          ("_urust_case_value_" ^
            string_of_int (serial ()), dummyT)
      val fallback =
        the_default T.undefined_value explicit_fallback

      fun compile_sources [] = fallback
        | compile_sources
            ((Prepared_Case_Arm
                {plan = Pattern_Plan {matcher, binders, ...}, ...},
              source_guard, rhs) :: rest) =
            let
              val next_arm = compile_sources rest
              val success =
                payload_abstraction binders rhs
            in
              (case source_guard of
                 NONE =>
                   T.matcher_run_value matcher value
                     success next_arm
               | SOME guard =>
                   T.matcher_run_guarded_value matcher value
                     (payload_abstraction binders guard)
                     success next_arm)
            end
    in
      T.bind scrutinee
        (Term.lambda value (compile_sources arms))
    end

  fun compile_case ctxt scrutinee arms =
    compile_case_internal ctxt NONE scrutinee arms

  fun compile_case_with_fallback ctxt scrutinee fallback arms =
    compile_case_internal ctxt (SOME fallback) scrutinee arms
end
\<close>

end
