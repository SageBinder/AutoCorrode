theory Parser_Impl_Patterns
  imports Parser_Impl_Resolution
begin

section\<open> Resolved patterns and case compilation \<close>

ML\<open>
signature URUST_PATTERNS =
sig
  type prepared_binding
  type prepared_case_arm

  datatype binder_site =
      Let_Const_Binder
    | Mutable_Let_Binder of Position.T
    | For_Binder

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
  val bind_prepared:
    prepared_binding -> term -> term -> term

  val select_match_flavour:
    URust_AST.match_flavour ->
      URust_AST.ur_arm list ->
      Position.T ->
      URust_AST.match_flavour

  val prepare_switch_arm:
    Proof.context ->
      URust_AST.ur_arm ->
      term list * URust_AST.ur_expr

  val prepare_case_arms:
    Proof.context ->
      Position.T ->
      URust_Resolution.environment ->
      URust_AST.ur_arm list ->
      prepared_case_arm list
  val prepared_environment:
    prepared_case_arm -> URust_Resolution.environment
  val prepared_guard:
    prepared_case_arm -> (URust_AST.ur_expr * Position.T) option
  val prepared_body: prepared_case_arm -> URust_AST.ur_expr
  val prepared_direct_abstraction:
    prepared_case_arm -> (term -> term) option
  val prepared_is_total: prepared_case_arm -> bool
  val compile_case:
    Proof.context ->
      term option ->
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
(*
  URust_Patterns is the pattern-elaboration boundary between the unresolved URust_AST pattern
  language and recursive expression translation.  It owns use-site validation, binder-versus-
  constructor decisions, pattern-local environment allocation, bare-match classification, switch-key
  preparation, conservative coverage classification, and construction of the existing shallow case
  terms.  URust_AST owns the source representation, URust_Resolution owns name and constructor
  metadata operations, URust_Shallow_Terms owns the shallow-term vocabulary, and URust_Translate owns
  recursive lowering of expressions, guards, and bodies.

  The public binder_site constructors select the contract enforced by prepare_binding:
  Let_Const_Binder admits only directly irrefutable let/const patterns; Mutable_Let_Binder additionally
  restricts the source head to an identifier, wildcard, or top-level tuple and carries the mutable
  keyword position; and For_Binder resolves known constructors before enforcing irrefutability.
  prepare_binding recursively rejects reference patterns, validates all binders before allocating any
  of them, and returns an abstract prepared_binding. binding_environment is the exact environment in
  which the caller must lower the binding body. binding_abstraction closes such a lowered body over the
  matched RHS for consumers such as `for`. bind_prepared takes an already-lowered outer-scope RHS and
  inner-scope body, performs any mutable scalar/wildcard allocation selected during preparation, and
  constructs the shallow bind. The caller remains responsible for lowering both expressions in those
  prescribed environments.

  select_match_flavour preserves an explicit MF_Case or MF_Switch (while rejecting switch guards) and
  resolves MF_Auto according to the current case-versus-numeral-switch policy; it never returns
  MF_Auto. prepare_switch_arm accepts an unguarded numeral/wildcard pattern or an or-pattern composed
  from those forms, preserves alternative order, and returns the encoded option keys (Some numeral or
  None wildcard) with the unchanged source body for lowering in the outer environment.

  prepare_case_arms creates one constructor resolver for the supplied source span, then resolves and
  reports constructors, rejects unsupported patterns, validates duplicate and or-alternative binders
  atomically, and allocates one environment shared by every expanded alternative of each source arm.
  It returns source-ordered abstract prepared_case_arm values. prepared_environment is the environment
  in which both prepared_guard and
  prepared_body must be lowered.  prepared_direct_abstraction is SOME only when the complete pattern
  can bind a scrutinee directly without case compilation.  prepared_is_total is a conservative
  certificate that the supported coverage analysis found the arm total; false means partial or
  unknown, not necessarily non-total.

  compile_case consumes an optional explicit fallback followed by the scrutinee and source-ordered
  triples of a prepared_case_arm, its already-lowered optional
  guard, and its already-lowered body.  Each lowered term must correspond to that prepared arm and its
  prepared_environment.  Compilation evaluates the scrutinee once, preserves source-arm and
  or-alternative order, binds pattern variables before evaluating guards and bodies, and makes a false
  guard fall through to the next alternative or arm. NONE uses the existing case encoding's unmatched
  behavior; SOME term installs that term as the terminal unmatched result. Compilation preserves the
  shallow term shape required for old-frontend conformance.

  The representations of prepared_binding and prepared_case_arm are intentionally abstract.
  Pattern-position inspection, resolution policies, resolved/basic/case pattern datatypes, or-pattern
  expansion, normalization, generated names, recursive compiler helpers, and the exact coverage
  representation are implementation details. Callers may rely only on the signature and the scoping,
  ordering, validation, fallback, and term-shape contracts above.
*)
structure URust_Patterns :> URUST_PATTERNS =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure R = URust_Resolution

  type binding_signature = string * Position.T

  datatype binder_site =
      Let_Const_Binder
    | Mutable_Let_Binder of Position.T
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
    | Resolved_Bind of binding_signature
    | Resolved_Constructor of
        R.constructor_info * Position.T * resolved_pattern list
    | Resolved_Tuple of resolved_pattern list * Position.T
    | Resolved_Alias of
        binding_signature * resolved_pattern * Position.T
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
    | resolved_position (Resolved_Bind (_, pos)) = pos
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

  fun binding name pos = (name, pos)

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

  fun resolve_pattern resolver ctxt policy pattern =
    let
      fun resolve source_pattern =
        (case source_pattern of
           P_Wild pos => Resolved_Wild pos
         | P_Ident (name, pos) =>
             (case policy of
                Always_Binder => Resolved_Bind (binding name pos)
              | _ =>
                  (case R.resolve_constructor resolver
                      (name, pos) of
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
              (case R.resolve_constructor resolver
                  (name, pos) of
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
             (case R.resolve_struct_pattern ctxt resolver
                 (name, pos, fields) of
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
                  error ("urust_expr: HOL record pattern " ^
                    quote (Long_Name.base_name record_name) ^
                    " requires selector-based lowering" ^
                    Position.here pos))
         | P_Or (alternatives, pos) =>
             Resolved_Or (map resolve alternatives, pos))
    in
      reject_reference_patterns pattern;
      resolve pattern
    end

  fun signature_name (name, _) = name
  fun signature_position (_, pos) = pos

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
         | SOME _ =>
             ())
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
    | binder_site_description (Mutable_Let_Binder _) =
        "a mutable binding position"
    | binder_site_description For_Binder =
        "a `for` binder position"

  datatype prepared_binding =
    Prepared_Binding of
      {environment: R.environment,
       abstraction: term -> term,
       rhs_wrapper: term -> term}

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
      val resolver =
        R.make_constructor_resolver ctxt (position pattern)
      val resolved =
        resolve_pattern resolver ctxt policy pattern
      val signatures = collect_bindings resolved
      val rhs_mode =
        (case site of
           Mutable_Let_Binder _ => mutable_source_mode pattern
         | _ => Plain_Rhs)
      val rhs_wrapper =
        (case (site, rhs_mode) of
           (Mutable_Let_Binder mutable_pos, Allocate_Rhs) =>
             T.allocate_reference mutable_pos
         | _ => I)
      val environment' =
        R.allocate_locals ctxt environment signatures
      val abstraction =
        (case direct_abstraction ctxt true false environment' resolved of
           SOME abstraction => abstraction
         | NONE =>
             let
               val diagnostic_site =
                 (case (site, rhs_mode) of
                    (Mutable_Let_Binder _, Plain_Rhs) =>
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
         rhs_wrapper = rhs_wrapper}
    end

  fun binding_environment
      (Prepared_Binding {environment, ...}) = environment
  fun binding_abstraction
      (Prepared_Binding {abstraction, ...}) = abstraction
  fun bind_prepared
      (Prepared_Binding {abstraction, rhs_wrapper, ...})
      rhs body =
    T.bind (rhs_wrapper rhs) (abstraction body)

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
    in (switch_keys ctxt pattern, body) end

  datatype basic_case_pattern =
      Basic_Wild of Position.T option
    | Basic_Bind of binding_signature
    | Basic_Generated of term
    | Basic_Constructor of
        R.constructor_info * Position.T * basic_case_pattern list
    | Basic_Resolved of term * basic_case_pattern list
    | Basic_Tuple of basic_case_pattern list

  datatype case_pattern =
      Case_Wild of Position.T
    | Case_Bind of binding_signature
    | Case_Value of term * Position.T
    | Case_Constructor of
        R.constructor_info * Position.T * case_pattern list
    | Case_Resolved of term * case_pattern list
    | Case_Tuple of case_pattern list
    | Case_Alias of binding_signature * case_pattern
    | Case_Range of range_kind * term * term * Position.T
    | Case_Slice_Suffix of case_pattern

  datatype case_pattern_tree =
      Pattern_Constant of term
    | Pattern_Slot of int
    | Pattern_Application of term * case_pattern_tree list

  datatype prepared_case_arm =
    Prepared_Case_Arm of
      {patterns: case_pattern list,
       environment: R.environment,
       binders: term list,
       guard: (ur_expr * Position.T) option,
       body: ur_expr,
       direct_abstraction: (term -> term) option,
       total: bool}

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

  fun expand_resolved_pattern pattern =
    let
      fun products [] = [[]]
        | products (alternatives :: rest) =
            let val tails = products rest
            in
              maps (fn alternative =>
                map (fn tail => alternative :: tail) tails) alternatives
            end

      fun expand (Resolved_Or (alternatives, _)) = maps expand alternatives
        | expand (Resolved_Constructor (info, pos, arguments)) =
            map (fn expanded =>
                Resolved_Constructor (info, pos, expanded))
              (products (map expand arguments))
        | expand (Resolved_Tuple (arguments, pos)) =
            map (fn expanded => Resolved_Tuple (expanded, pos))
              (products (map expand arguments))
        | expand (Resolved_Alias (binder_sig, inner, alias_pos)) =
            map (fn expanded =>
                Resolved_Alias (binder_sig, expanded, alias_pos))
              (expand inner)
        | expand (Resolved_Slice (items, pos)) =
            let
              fun item_alternatives
                    (Resolved_Slice_Pattern nested) =
                    map Resolved_Slice_Pattern (expand nested)
                | item_alternatives
                    (Resolved_Slice_Rest rest_pos) =
                    [Resolved_Slice_Rest rest_pos]
            in
              map (fn expanded => Resolved_Slice (expanded, pos))
                (products (map item_alternatives items))
            end
        | expand source_pattern = [source_pattern]
    in expand pattern end

  fun resolved_value_term ctxt environment value =
    (case value of
       Resolved_Literal_Value payload =>
         T.literal (R.literal_value ctxt environment payload)
     | Resolved_Identifier_Value identifier =>
         R.literal_identifier ctxt environment identifier)

  fun prepare_case_pattern ctxt environment pattern =
    (case pattern of
       Resolved_Wild pos =>
         (R.report_wildcard ctxt pos; Case_Wild pos)
     | Resolved_Bind binder_sig =>
         let
           val name = signature_name binder_sig
           val pos = signature_position binder_sig
           val _ =
             (case R.use_local ctxt environment (name, pos) of
                SOME _ => ()
              | NONE =>
                  error ("urust_expr: internal unallocated case binder " ^
                    quote name ^ Position.here pos))
         in Case_Bind binder_sig end
     | Resolved_Value payload =>
         Case_Value
           (R.literal_value ctxt environment payload,
            literal_position payload)
     | Resolved_Constructor (info, pos, arguments) =>
         Case_Constructor
           (info, pos, map (prepare_case_pattern ctxt environment) arguments)
     | Resolved_Tuple (arguments, _) =>
         Case_Tuple
           (map (prepare_case_pattern ctxt environment) arguments)
     | Resolved_Alias (binder_sig, inner, _) =>
         Case_Alias
           (binder_sig, prepare_case_pattern ctxt environment inner)
     | Resolved_Range (kind, lower, upper, pos) =>
         Case_Range
           (kind,
            resolved_value_term ctxt environment lower,
            resolved_value_term ctxt environment upper,
            pos)
     | Resolved_Slice (items, _) =>
         let
           val (prefix, rest_pos, suffix) =
             split_resolved_slice_items items
           fun cons_chain patterns tail =
             fold_rev (fn nested => fn rest =>
                 Case_Resolved
                   (T.list_cons_constructor,
                    [prepare_case_pattern ctxt environment nested, rest]))
               patterns tail
           val nil_pattern =
             Case_Resolved (T.list_nil_constructor, [])
         in
           (case rest_pos of
              NONE => cons_chain prefix nil_pattern
            | SOME _ =>
                if null suffix
                then cons_chain prefix (Case_Wild Position.none)
                else
                  cons_chain prefix
                    (Case_Slice_Suffix
                      (cons_chain (rev suffix) nil_pattern)))
         end
     | Resolved_Or (_, pos) =>
         error ("urust_expr: internal unexpanded resolved or-pattern" ^
           Position.here pos))

  fun prepare_case_arm resolver ctxt environment
      (UR_Arm (pattern, guard, body)) =
    let
      val resolved =
        resolve_pattern resolver ctxt Resolve_Constructor_Case pattern
      val signatures = collect_bindings resolved
      val arm_environment =
        R.allocate_locals ctxt environment signatures
      val patterns =
        map (prepare_case_pattern ctxt arm_environment)
          (expand_resolved_pattern resolved)
      val binders =
        map (lookup_signature arm_environment) signatures
      val direct =
        direct_abstraction ctxt false true arm_environment resolved
      val total =
        coverage_is_total (resolved_coverage resolved)
    in
      Prepared_Case_Arm
        {patterns = patterns,
         environment = arm_environment,
         binders = binders,
         guard = guard,
         body = body,
         direct_abstraction = direct,
         total = total}
    end

  fun prepare_case_arms ctxt pos environment arms =
    let val resolver = R.make_constructor_resolver ctxt pos
    in map (prepare_case_arm resolver ctxt environment) arms end

  fun prepared_environment
      (Prepared_Case_Arm {environment, ...}) = environment
  fun prepared_guard
      (Prepared_Case_Arm {guard, ...}) = guard
  fun prepared_body
      (Prepared_Case_Arm {body, ...}) = body
  fun prepared_direct_abstraction
      (Prepared_Case_Arm {direct_abstraction, ...}) =
        direct_abstraction
  fun prepared_is_total
      (Prepared_Case_Arm {total, ...}) = total

  fun normalize_basic_pattern pattern =
    (case pattern of
       Case_Wild pos => Basic_Wild (SOME pos)
     | Case_Bind binder_sig => Basic_Bind binder_sig
     | Case_Value (_, pos) =>
         error ("urust_expr: internal unnormalized value pattern" ^
           Position.here pos)
     | Case_Constructor (info, pos, arguments) =>
         Basic_Constructor
           (info, pos, map normalize_basic_pattern arguments)
     | Case_Resolved (constructor, arguments) =>
         Basic_Resolved
           (constructor, map normalize_basic_pattern arguments)
     | Case_Tuple arguments =>
         Basic_Tuple (map normalize_basic_pattern arguments)
     | Case_Alias (binder_sig, _) =>
         error ("urust_expr: internal unnormalized alias pattern" ^
           Position.here (signature_position binder_sig))
     | Case_Range (_, _, _, pos) =>
         error ("urust_expr: internal unnormalized range pattern" ^
           Position.here pos)
     | Case_Slice_Suffix _ =>
         error "urust_expr: internal unnormalized slice suffix pattern")

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

  fun bind_basic_pattern ctxt environment pattern =
    let
      fun add_slot slot (slots_rev, count) =
        (Pattern_Slot count, (slot :: slots_rev, count + 1))

      fun walk (Basic_Wild pos) state =
            (case pos of
               SOME source_pos => R.report_wildcard ctxt source_pos
             | NONE => ();
             add_slot NONE state)
        | walk (Basic_Bind binder_sig) state =
            let
              val name = signature_name binder_sig
              val pos = signature_position binder_sig
            in
              (case R.use_local ctxt environment (name, pos) of
                 SOME free => add_slot (SOME free) state
               | NONE =>
                   error ("urust_expr: internal unregistered case binder " ^
                     quote name ^ Position.here pos))
            end
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

  fun requires_nested_match pattern =
    (case pattern of
       Case_Value _ => true
     | Case_Alias _ => true
     | Case_Range _ => true
     | Case_Slice_Suffix _ => true
     | Case_Constructor (_, _, arguments) =>
         List.exists requires_nested_match arguments
     | Case_Resolved (_, arguments) =>
         List.exists requires_nested_match arguments
     | Case_Tuple arguments =>
         List.exists requires_nested_match arguments
     | _ => false)

  fun extend_guard generated NONE = SOME generated
    | extend_guard generated (SOME source) =
        SOME (T.binary And source generated)

  fun alias_wrapper environment expression binder_sig rhs =
    let
      val name = signature_name binder_sig
      val pos = signature_position binder_sig
    in
      (case R.lookup_local environment name of
         SOME free => T.bind expression (Term.lambda free rhs)
       | NONE =>
           error ("urust_expr: internal unregistered alias binder " ^
             quote name ^ Position.here pos))
    end

  fun compile_nested_case compiler ctxt environment expression pattern
      success fallback =
    compiler ctxt expression
      [(pattern, environment, NONE, success),
       (Case_Wild Position.none, environment, NONE, fallback)]

  fun normalize_pattern_for_nested compiler ctxt environment pattern =
    let
      fun normalize_arguments [] = ([], [], [])
        | normalize_arguments (argument :: rest) =
            let
              val (argument', guards0, wrappers0) =
                if requires_nested_match argument then
                  let
                    val temporary =
                      Free
                        ("_urust_pat_" ^
                          string_of_int (serial ()), dummyT)
                    val temporary_expression = T.literal temporary
                    val (matched_expression, matched_pattern) =
                      (case argument of
                         Case_Slice_Suffix reversed_suffix =>
                           (T.reverse_list temporary_expression,
                            reversed_suffix)
                       | _ => (temporary_expression, argument))
                    val guard =
                      compile_nested_case compiler ctxt environment
                        matched_expression matched_pattern
                        (T.literal T.true_value)
                        (T.literal T.false_value)
                    fun wrapper rhs =
                      compile_nested_case compiler ctxt environment
                        matched_expression matched_pattern
                        rhs T.undefined_value
                  in
                    (Basic_Generated temporary, [guard], [wrapper])
                  end
                else
                  normalize_pattern_for_nested
                    compiler ctxt environment argument
              val (rest', guards1, wrappers1) =
                normalize_arguments rest
            in
              (argument' :: rest',
               guards0 @ guards1,
               wrappers0 @ wrappers1)
            end
    in
      (case pattern of
         Case_Constructor (info, pos, arguments) =>
           let
             val (arguments', guards, wrappers) =
               normalize_arguments arguments
           in
             (Basic_Constructor (info, pos, arguments'),
              guards, wrappers)
           end
       | Case_Resolved (constructor, arguments) =>
           let
             val (arguments', guards, wrappers) =
               normalize_arguments arguments
           in
             (Basic_Resolved (constructor, arguments'),
              guards, wrappers)
           end
       | Case_Tuple arguments =>
           let
             val (arguments', guards, wrappers) =
               normalize_arguments arguments
           in (Basic_Tuple arguments', guards, wrappers) end
       | _ => (normalize_basic_pattern pattern, [], []))
    end

  fun normalize_extended_pattern compiler ctxt environment expression pattern =
    (case pattern of
       Case_Alias (binder_sig, inner) =>
         let
           val (basic, guards, wrappers) =
             normalize_extended_pattern
               compiler ctxt environment expression inner
           fun wrap rhs =
             alias_wrapper environment expression binder_sig rhs
         in (basic, guards, wrappers @ [wrap]) end
     | Case_Value (literal, _) =>
         (Basic_Wild NONE,
          [T.binary Eq expression (T.literal literal)],
          [])
     | Case_Range (kind, lower, upper, _) =>
         let
           val upper_guard =
             T.binary
               (case kind of
                  RK_Exclusive => Lt
                | RK_Inclusive => Le)
               expression upper
         in
           (Basic_Wild NONE,
            [T.binary And
              (T.binary Ge expression lower) upper_guard],
            [])
         end
     | Case_Slice_Suffix reversed_suffix =>
         let
           val reversed_expression = T.reverse_list expression
           val guard =
             compile_nested_case compiler ctxt environment
               reversed_expression reversed_suffix
               (T.literal T.true_value)
               (T.literal T.false_value)
           fun wrap rhs =
             compile_nested_case compiler ctxt environment
               reversed_expression reversed_suffix
               rhs T.undefined_value
         in (Basic_Wild NONE, [guard], [wrap]) end
     | _ =>
         normalize_pattern_for_nested
           compiler ctxt environment pattern)

  fun normalize_case_alternative compiler ctxt value
      (pattern, environment) =
    let
      val (basic_pattern, generated_guards, wrappers) =
        normalize_extended_pattern
          compiler ctxt environment (T.literal value) pattern
      val abstraction =
        bind_basic_pattern ctxt environment basic_pattern
      val generated_guard =
        fold extend_guard generated_guards NONE
      fun wrap rhs =
        fold_rev (fn wrapper => fn body => wrapper body)
          wrappers rhs
      val wild =
        (case basic_pattern of
           Basic_Wild _ => true
         | _ => false)
    in (wild, abstraction, generated_guard, wrap) end

  fun normalize_case_arm compiler ctxt value
      (pattern, environment, source_guard, rhs) =
    let
      val (wild, abstraction, generated_guard, wrap) =
        normalize_case_alternative compiler ctxt value
          (pattern, environment)
      val guard =
        (case generated_guard of
           NONE => source_guard
         | SOME generated =>
             extend_guard generated source_guard)
    in (wild, abstraction, guard, wrap rhs) end

  fun compile_pattern_case ctxt scrutinee arms =
    let
      val value =
        Free
          ("_urust_case_value_" ^
            string_of_int (serial ()), dummyT)
      val normalized =
        map (normalize_case_arm compile_pattern_case ctxt value) arms

      fun case_term branches =
        T.case_guard T.true_value value
          (fold_rev T.case_cons branches T.case_nil)

      fun generated_wild rhs =
        bind_basic_pattern ctxt R.empty_environment
          (Basic_Wild NONE) rhs

      val undefined = T.undefined_value

      fun compile_branches [] =
            error "urust_expr: internal empty case branch list"
        | compile_branches [(wild, abstraction, NONE, rhs)] =
            if wild then rhs
            else case_term [abstraction rhs]
        | compile_branches [(wild, abstraction, SOME guard, rhs)] =
            if wild then T.conditional guard rhs undefined
            else
              let val fallback = undefined in
                case_term
                  [abstraction
                    (T.conditional guard rhs fallback),
                   generated_wild fallback]
              end
        | compile_branches
            ((wild, abstraction, guard, rhs) :: rest) =
            let
              val fallback = compile_branches rest
              val rhs' =
                (case guard of
                   SOME condition =>
                     T.conditional condition rhs fallback
                 | NONE => rhs)
            in
              if wild then rhs'
              else
                case_term
                  [abstraction rhs',
                   generated_wild fallback]
            end

      val selector =
        if List.exists
            (fn (_, _, guard, _) => is_some guard) normalized
        then compile_branches normalized
        else
          case_term
            (map
              (fn (_, abstraction, _, rhs) =>
                abstraction rhs) normalized)
    in T.bind scrutinee (Term.lambda value selector) end

  fun compile_case_internal ctxt explicit_fallback scrutinee arms =
    let
      val value =
        Free
          ("_urust_case_value_" ^
            string_of_int (serial ()), dummyT)

      fun case_term branches =
        T.case_guard T.true_value value
          (fold_rev T.case_cons branches T.case_nil)

      fun generated_wild rhs =
        bind_basic_pattern ctxt R.empty_environment
          (Basic_Wild NONE) rhs

      fun normalize_source_arm
          (Prepared_Case_Arm
            {patterns, environment, binders, ...},
           source_guard, rhs) =
        {alternatives =
           map
             (normalize_case_alternative
               compile_pattern_case ctxt value)
             (map (fn pattern => (pattern, environment)) patterns),
         binders = binders,
         source_guard = source_guard,
         rhs = rhs}

      val normalized = map normalize_source_arm arms

      fun has_generated_guard
          {alternatives, source_guard, ...} =
        is_some source_guard orelse
          List.exists
            (fn (_, _, guard, _) => is_some guard)
            alternatives

      fun handler_term binders source_guard rhs next_arm =
        fold_rev Term.lambda binders
          (case source_guard of
             SOME guard => T.conditional guard rhs next_arm
           | NONE => rhs)

      fun handler_call handler binders =
        Term.list_comb (handler, binders)

      fun compile_alternatives [] _ _ _ =
            error "urust_expr: internal empty source-arm alternative list"
        | compile_alternatives
            [(wild, abstraction, generated_guard, wrap)]
            handler binders next_arm =
            let
              val success = wrap (handler_call handler binders)
              val guarded =
                (case generated_guard of
                   SOME guard =>
                     T.conditional guard success next_arm
                 | NONE => success)
            in
              if wild then guarded
              else
                case_term
                  [abstraction guarded,
                   generated_wild next_arm]
            end
        | compile_alternatives
            ((wild, abstraction, generated_guard, wrap) :: rest)
            handler binders next_arm =
            let
              val next_alternative =
                compile_alternatives rest handler binders next_arm
              val success = wrap (handler_call handler binders)
              val guarded =
                (case generated_guard of
                   SOME guard =>
                     T.conditional guard success next_alternative
                 | NONE => success)
            in
              if wild then guarded
              else
                case_term
                  [abstraction guarded,
                   generated_wild next_alternative]
            end

      val fallback =
        the_default T.undefined_value explicit_fallback

      fun compile_guarded_sources [] = fallback
        | compile_guarded_sources
            ({alternatives, binders, source_guard, rhs} :: rest) =
            let
              val next_arm = compile_guarded_sources rest
              val handler =
                handler_term binders source_guard rhs next_arm
            in
              compile_alternatives alternatives
                handler binders next_arm
            end

      fun compile_unguarded_sources sources =
        let
          fun install [] branches =
                case_term
                  (maps I (rev branches) @
                    (case explicit_fallback of
                       SOME term => [generated_wild term]
                     | NONE => []))
            | install
                ({alternatives, binders, source_guard = NONE, rhs} :: rest)
                branches =
                let
                  val handler = fold_rev Term.lambda binders rhs
                  fun branch
                      (wild, abstraction, NONE, wrap) =
                        abstraction
                          (wrap (handler_call handler binders))
                    | branch _ =
                        error
                          "urust_expr: internal guarded alternative in unguarded case"
                  val current = map branch alternatives
                in install rest (current :: branches) end
            | install _ _ =
                error
                  "urust_expr: internal guarded source arm in unguarded case"
        in install sources [] end

      val selector =
        if List.exists has_generated_guard normalized
        then compile_guarded_sources normalized
        else compile_unguarded_sources normalized
    in
      T.bind scrutinee (Term.lambda value selector)
    end

  fun compile_case ctxt fallback scrutinee arms =
    compile_case_internal ctxt fallback scrutinee arms
end
\<close>

end
