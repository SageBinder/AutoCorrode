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
    Proof.context ->
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
  of them, and returns an abstract prepared_binding. Case preparation instead treats reference
  patterns as syntax-only wrappers, matching the current frontend. binding_environment is the exact
  environment in which the caller must lower the binding body. binding_abstraction closes such a
  lowered body over the matched RHS for consumers such as `for`. bind_prepared takes an already-lowered
  outer-scope RHS and inner-scope body, performs any mutable scalar/wildcard allocation selected during
  preparation, and constructs the shallow bind. The caller remains responsible for lowering both
  expressions in those prescribed environments.

  select_match_flavour preserves an explicit MF_Case or MF_Switch (while rejecting switch guards) and
  resolves MF_Auto according to the current case-versus-numeral-switch policy; it never returns
  MF_Auto. The auto query is contextual only for exact literal registrations: authentic registered
  constructors are case-only, registered nonconstructors support both lowerings, switch wins when
  every arm is binder-free, guard-free, and value/wildcard compatible, and guards still force case.
  This is not general type-directed matching.
  prepare_switch_arm accepts an unguarded numeral/wildcard/registered-value pattern or an or-pattern
  composed from those forms, preserves alternative order, and returns the encoded option keys (Some
  value or None wildcard) with the unchanged source body for lowering in the outer environment.

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
    | position (P_Path path) = path_position path
    | position (P_Constr (path, _)) = path_position path
    | position (P_Tuple (_, pos)) = pos
    | position (P_Group pattern) = position pattern
    | position (P_Borrow (_, _, pos)) = pos
    | position (P_Alias (_, _, _, pos)) = pos
    | position (P_Range (_, _, _, pos)) = pos
    | position (P_Slice (_, pos)) = pos
    | position (P_Struct (path, _)) = path_position path
    | position (P_Or (_, pos)) = pos

  fun reject_reference_patterns pattern =
    let
      fun reject (P_Borrow (_, _, pos)) =
            error ("urust_expr: reference patterns are not implemented" ^
              Position.here pos)
        | reject (P_Constr (_, arguments)) = List.app reject arguments
        | reject (P_Tuple (arguments, _)) = List.app reject arguments
        | reject (P_Group inner) = reject inner
        | reject (P_Alias (_, _, inner, _)) = reject inner
        | reject (P_Range (_, lower, upper, _)) =
            (reject lower; reject upper)
        | reject (P_Slice (items, _)) =
            List.app
              (fn SI_Pat nested => reject nested | SI_Rest _ => ()) items
        | reject (P_Struct (_, fields)) =
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

  datatype match_capability =
    Match_Capability of {case_ok: bool, switch_ok: bool}

  fun classify_match ctxt arms pos =
    let
      val resolver = R.make_constructor_resolver ctxt pos

      fun registered_capability path =
        (case R.classify_registered_literal ctxt resolver path of
           R.Unregistered_Literal =>
             Match_Capability {case_ok = true, switch_ok = false}
         | R.Registered_Value_Literal =>
             Match_Capability {case_ok = true, switch_ok = true}
         | R.Registered_Constructor_Literal =>
             Match_Capability {case_ok = true, switch_ok = false})

      fun capability pattern =
        (case strip_groups pattern of
           P_Literal (LP_Integer _) =>
             Match_Capability {case_ok = false, switch_ok = true}
         | P_Ident identifier =>
             registered_capability (make_single_path identifier)
         | P_Path path => registered_capability path
         | P_Wild _ =>
             Match_Capability {case_ok = true, switch_ok = true}
         | _ =>
             Match_Capability {case_ok = true, switch_ok = false})
      val capabilities = map (capability o arm_pattern) arms
      fun case_compatible
          (Match_Capability {case_ok, ...}) = case_ok
      fun switch_compatible
          (Match_Capability {switch_ok, ...}) = switch_ok
    in
      if List.exists (is_some o arm_guard) arms then MF_Case
      else if List.all switch_compatible capabilities then MF_Switch
      else if List.all case_compatible capabilities then MF_Case
      else
        error ("urust_expr: mixed numeral and constructor patterns in bare `match`" ^
          Position.here pos)
    end

  fun first_guard_position [] = NONE
    | first_guard_position (UR_Arm (_, SOME (_, pos), _) :: _) = SOME pos
    | first_guard_position (_ :: rest) = first_guard_position rest

  fun select_match_flavour ctxt flavour arms pos =
    let
      val selected =
        (case flavour of
           MF_Auto => classify_match ctxt arms pos
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
    | Resolved_Path_Value of ur_path

  datatype resolved_pattern =
      Resolved_Wild of Position.T
    | Resolved_Bind of binding_signature
    | Resolved_Constructor of
        R.constructor_info * Position.T * resolved_pattern list
    | Resolved_Tuple of resolved_pattern list * Position.T
    | Resolved_Alias of
        binding_signature * resolved_pattern * Position.T
    | Resolved_Value of literal_payload
    | Resolved_Path of ur_path
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
    | resolved_position (Resolved_Path path) = path_position path
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
        | coverage (Resolved_Path _) = Coverage_Partial
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
     | P_Path path => Resolved_Path_Value path
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
                  (case R.resolve_constructor ctxt resolver
                      (make_single_path (name, pos)) of
                     NONE => Resolved_Bind (binding name pos)
                   | SOME info =>
                       (check_constructor_arity name pos info [];
                        R.report_constructor ctxt
                          (make_single_path (name, pos)) info;
                        Resolved_Constructor (info, pos, []))))
         | P_Literal (payload as LP_Integer (_, pos)) =>
             (case policy of
                Resolve_Constructor_Case =>
                  error ("urust_expr: numeric patterns are not supported in case patterns" ^
                    Position.here pos)
              | _ => Resolved_Value payload)
         | P_Literal payload => Resolved_Value payload
         | P_Path path =>
             (case R.resolve_constructor ctxt resolver path of
                SOME info =>
                  let
                    val (name, pos) =
                      segment_identifier (final_segment path)
                  in
                    check_constructor_arity name pos info [];
                    R.report_constructor ctxt path info;
                    Resolved_Constructor (info, pos, [])
                  end
              | NONE => Resolved_Path path)
         | P_Constr (path, arguments) =>
              let
                val name = render_path path
                val pos = #2 (segment_identifier (final_segment path))
              in
              (case R.resolve_constructor ctxt resolver path of
                NONE =>
                  error ("urust_expr: `" ^ name ^
                    "` is not a known constructor" ^ Position.here pos)
              | SOME info =>
                  (check_constructor_arity name pos info arguments;
                   R.report_constructor ctxt path info;
                   Resolved_Constructor
                     (info, pos, map resolve arguments)))
              end
         | P_Tuple (arguments, pos) =>
             Resolved_Tuple (map resolve arguments, pos)
         | P_Group inner => resolve inner
         | P_Borrow (_, inner, pos) =>
             (case policy of
                Resolve_Constructor_Case => resolve inner
              | _ =>
                  error ("urust_expr: reference patterns are not implemented" ^
                    Position.here pos))
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
         | P_Struct (path, fields) =>
             let
               val pos = #2 (segment_identifier (final_segment path))
             in
             (case R.resolve_struct_pattern ctxt resolver
                 (path, fields) of
                R.Resolved_Constructor_Struct (info, ordered) =>
                  let
                    val _ = R.report_constructor ctxt path info
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
             end
         | P_Or (alternatives, pos) =>
             Resolved_Or (map resolve alternatives, pos))
    in
      (case policy of
         Resolve_Constructor_Case => ()
       | _ => reject_reference_patterns pattern);
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
        | collect (Resolved_Path _) = []
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

  fun switch_keys resolver ctxt pattern =
    (case strip_groups pattern of
       P_Or (alternatives, _) =>
         maps (switch_keys resolver ctxt) alternatives
     | P_Literal (LP_Integer (lexeme, pos)) =>
         [T.option_some (T.integer_value pos lexeme)]
     | P_Wild pos => (R.report_wildcard ctxt pos; [T.option_none])
     | P_Path path =>
         (case R.classify_registered_literal ctxt resolver path of
            R.Registered_Value_Literal =>
              [T.option_some
                (R.literal_path_value ctxt R.empty_environment path)]
          | R.Registered_Constructor_Literal =>
              error ("urust_expr: authentic constructor " ^
                quote (render_path path) ^
                " requires case-pattern lowering" ^
                Position.here (path_position path))
          | R.Unregistered_Literal =>
              error ("urust_expr: unsupported match_switch key " ^
                quote (render_path path) ^
                " (expected an exact registered literal value)" ^
                Position.here (path_position path)))
     | P_Ident (name, pos) =>
         (case R.classify_registered_literal ctxt resolver
             (make_single_path (name, pos)) of
            R.Unregistered_Literal =>
              error ("urust_expr: unsupported match_switch key " ^ quote name ^
                " (numeral or `_` only; const-id / path keys not yet supported)" ^
                Position.here pos)
          | R.Registered_Value_Literal =>
              [T.option_some
                (R.literal_identifier_value ctxt R.empty_environment
                  (name, pos))]
          | R.Registered_Constructor_Literal =>
              error ("urust_expr: authentic constructor " ^ quote name ^
                " requires case-pattern lowering" ^ Position.here pos))
     | unsupported =>
         error ("urust_expr: unsupported match_switch pattern" ^
           " (numeral, `_`, or an or-list of those; binding patterns need" ^
           " `match_case`)" ^ Position.here (position unsupported)))

  fun prepare_switch_arm ctxt (UR_Arm (pattern, guard, body)) =
    let
      val resolver =
        R.make_constructor_resolver ctxt (position pattern)
      val _ = reject_reference_patterns pattern
      val _ =
        (case guard of
           NONE => ()
         | SOME (_, pos) =>
             error ("urust_expr: guards are not supported in explicit `match_switch`" ^
               Position.here pos))
    in (switch_keys resolver ctxt pattern, body) end

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
         R.literal_identifier ctxt environment identifier
     | Resolved_Path_Value path =>
         R.literal_path ctxt environment path)

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
     | Resolved_Path path =>
         Case_Value
           (R.literal_path_value ctxt environment path,
            path_position path)
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

  datatype structural_constructor =
    Structural_Constructor of {term: term, arity: int}

  datatype structural_family =
    Structural_Family of
      {name: string, members: structural_constructor list}

  datatype structural_pattern =
      Structural_Any of term option
    | Structural_Node of
        {head: structural_constructor,
         family: structural_family option,
         arguments: structural_pattern list}

  datatype structural_subject =
    Structural_Subject of
      {value: term, children: structural_subject list}

  type source_position =
    {arm_index: int, alternative_index: int}

  datatype scope_wrapper =
      Alias_Scope_Wrapper of (term -> term)
    | Nested_Scope_Wrapper of (term -> term)
    | Transformed_Scope_Wrapper of (term -> term)

  datatype clause_scope =
      Direct_Clause_Scope
    | Alias_Clause_Scope of (term -> term)
    | Nested_Clause_Scope of (term -> term)
    | Transformed_Clause_Scope of (term -> term)

  datatype case_clause =
    Case_Clause of
      {structural_pattern: structural_pattern,
       generated_test: term option,
       scope: clause_scope}

  datatype alternative_plan =
    Alternative_Plan of
      {position: source_position, clause: case_clause}

  datatype arm_plan =
    Arm_Plan of
      {arm_index: int,
       alternatives: alternative_plan list,
       source_guard: term option,
       body: term}

  datatype decision_row =
    Decision_Row of
      {position: source_position,
       clause: case_clause,
       source_guard: term option,
       body: term}

  datatype structural_exclusion =
    Decision_Exclusion of
      {position: source_position,
       pattern: structural_pattern}

  datatype decision_state =
    Decision_State of
      {region: structural_pattern,
       subject: structural_subject,
       exclusions: structural_exclusion list}

  datatype structural_selection_witness =
      Selected_Any of
        {binder: term option,
         subject: structural_subject}
    | Selected_Node of
        {subject: structural_subject,
         arguments: structural_selection_witness list}

  datatype clause_selection =
      Reused_Clause_Selection of
        {region: structural_pattern,
         witness: structural_selection_witness}
    | Opened_Covering_Clause_Selection of
        {region: structural_pattern,
         abstraction: term -> term,
         witness: structural_selection_witness}
    | Opened_Partial_Clause_Selection of
        {region: structural_pattern,
         abstraction: term -> term,
         witness: structural_selection_witness}

  datatype selected_failure_continuation =
    Selected_Failure_Continuation of
      {region: structural_pattern,
       selection: structural_selection_witness,
       exclusions: structural_exclusion list}

  datatype arm_failure_continuation =
    Enclosing_Branch_Continuation of
      {region: structural_pattern,
       subject: structural_subject,
       exclusions: structural_exclusion list}

  datatype selected_row_state =
    Selected_Row_State of
      {selection: structural_selection_witness,
       nested_failure: selected_failure_continuation,
       arm_failure: arm_failure_continuation}

  datatype compiled_decision_fragment =
    Compiled_Decision_Fragment of
      {semantic: term, historical: term}

  datatype compiled_outer_branch =
    Compiled_Outer_Branch of
      {semantic: term, historical: term}

  datatype compatibility_failure =
      Alternative_Compatibility_Failure
    | Arm_Compatibility_Failure

  datatype compatibility_reconstruction =
    Compatibility_Reconstruction of
      {failure: compatibility_failure,
       rows: decision_row list}

  datatype root_plan_context =
      Normal_Root_Plan
    | Compatibility_Root_Plan of compatibility_failure

  datatype applicable_row =
    Applicable_Row of
      {row: decision_row,
       decision_state: decision_state,
       remaining_rows: decision_row list}

  datatype opened_pattern =
    Opened_Pattern of
      {abstraction: term -> term,
       subject: structural_subject}

  datatype structural_group =
    Structural_Group of
      {pattern: structural_pattern,
       members: decision_row list,
       catchall_exclusions: structural_exclusion list}

  datatype outer_group_plan =
    Outer_Group_Plan of
      {groups: structural_group list,
       catchall: structural_group option}

  datatype root_suffix_plan =
    Root_Suffix_Plan of
      {rows: decision_row list,
       groups: structural_group list,
       outer_catchall: structural_group option,
       catchall_exclusions: structural_exclusion list,
       historical_groups: structural_group list,
       historical_outer_catchall: structural_group option,
       historical_catchall_exclusions:
         structural_exclusion list}

  type decision_source_arm =
    {patterns: case_pattern list,
     environment: R.environment,
     source_guard: term option,
     body: term}

  (*
    The ordered decision IR deliberately stays in ML until final case emission.

    - structural_pattern is a typed algebraic pattern. Structural_Any optionally records the exact
      Free that the source alternative binds at that point; constructor identity, arity, and complete
      native family order remain explicit in Structural_Node.
    - case_clause owns one structural pattern, its alternative-local generated test, and one explicit
      clause_scope operation. A closing scope binds aliases and recursively extracted nested binders
      around the source guard and body together; a direct scope is the identity operation.
    - source_position is stable source order. alternative_plan and arm_plan preserve the distinction
      between alternative failure and source-guard failure: a generated-test miss advances to the next
      alternative, while a false source guard advances to the next arm.
    - decision_state describes the structural region already selected by enclosing cases. exclusions
      record preceding case clauses that failed in that region. selected_failure_continuation ties
      nested failure to that selected region, its certified witness, and its already-bound subject.
      Enclosing_Branch_Continuation advances after a false source guard from the same already-bound
      branch root without sharing the selected alternative's binders. The
      structural_selection_witness certifies recursively that the selected region and subject
      decomposition conform before binders are extracted. Semantic totality never creates this
      witness: a singleton constructor or tuple over Structural_Any is opened to obtain its children.
      Decision_Exclusion suppresses only its exact source position. No binder or source-guard result
      is shared between alternatives.
    - compiled_decision_fragment is the boundary between semantics and retained term shape. The
      semantic term always uses the selected subject directly. The historical term is rendered from
      the same typed decision, after semantic continuations are fixed, and retains the old redundant
      root cases for direct guards, nested/transformed generated-test misses, and outer catchalls.
      root_suffix_plan is the single typed grouping and coverage result for both normal roots and
      compatibility suffixes. Compatibility caches that plan by failure context and source positions,
      then renders only its historical view; it never restarts the compiler outside root planning or
      changes semantic decision states, selections, exclusions, or failure continuations. No
      compatibility choice feeds back into decision-state selection.

    One compiler below handles ordinary, guarded, overlapping, and recursive nested cases. It never
    packs compiler metadata into HOL terms, never decodes generated terms, and never has separate
    guarded/unguarded compilation paths.
  *)

  fun constructor_term
      (Structural_Constructor {term, ...}) = term

  fun constructor_arity
      (Structural_Constructor {arity, ...}) = arity

  fun same_constructor (left, right) =
    Term.aconv_untyped
      (constructor_term left, constructor_term right)

  fun declared_constructor ctxt term =
    (case term of
       Const (name, _) =>
         Structural_Constructor
           {term = Const (name, dummyT),
            arity =
              length
                (binder_types
                  (Sign.the_const_type
                    (Proof_Context.theory_of ctxt) name))}
     | _ =>
         error
           "urust_expr: internal non-constant structural constructor")

  fun constructor_family_from_terms ctxt name members =
    Structural_Family
      {name = name, members = map (declared_constructor ctxt) members}

  fun constructor_head ctxt constructor family_hint =
    let
      val (name, typ) =
        (case constructor of
           Const (constructor_name, _) =>
             (constructor_name,
              Sign.the_const_type
                (Proof_Context.theory_of ctxt)
                constructor_name)
         | _ =>
             error
               "urust_expr: internal non-constant structural constructor")
      val head = declared_constructor ctxt constructor
      val family =
        (case Case_Translation.lookup_by_constr_permissive ctxt
            (name, typ) of
           SOME (_, members) =>
             SOME
               (constructor_family_from_terms ctxt
                 (the_default name
                   (try dest_Type_name (body_type typ)))
                 members)
         | NONE =>
             Option.map
               (fn (family_name, members) =>
                 constructor_family_from_terms ctxt
                   family_name members)
               family_hint)
    in (head, family) end

  fun make_structural_node ctxt constructor family_hint arguments =
    let val (head, family) =
      constructor_head ctxt constructor family_hint
    in
      Structural_Node
        {head = head, family = family, arguments = arguments}
    end

  fun structural_pattern_of_basic ctxt environment pattern =
    let
      fun local_free binder_sig =
        let
          val name = signature_name binder_sig
          val pos = signature_position binder_sig
        in
          (case R.lookup_local environment name of
             SOME free => free
           | NONE =>
               error ("urust_expr: internal unregistered case binder " ^
                 quote name ^ Position.here pos))
        end

      fun tuple_pattern [] =
            make_structural_node ctxt T.tuple_nil_constructor NONE []
        | tuple_pattern (argument :: rest) =
            make_structural_node ctxt T.pair_constructor NONE
              [convert argument, tuple_pattern rest]
      and convert (Basic_Wild _) = Structural_Any NONE
        | convert (Basic_Bind binder_sig) =
            Structural_Any (SOME (local_free binder_sig))
        | convert (Basic_Generated free) =
            Structural_Any (SOME free)
        | convert
            (Basic_Constructor (info, _, arguments)) =
            make_structural_node ctxt
              (R.constructor_term info)
              (R.constructor_family info)
              (map convert arguments)
        | convert (Basic_Resolved (constructor, arguments)) =
            make_structural_node ctxt constructor NONE
              (map convert arguments)
        | convert (Basic_Tuple arguments) =
            tuple_pattern arguments
    in convert pattern end

  fun erase_structural_bindings (Structural_Any _) =
        Structural_Any NONE
    | erase_structural_bindings
        (Structural_Node {head, family, arguments}) =
        Structural_Node
          {head = head, family = family,
           arguments = map erase_structural_bindings arguments}

  fun structural_is_any (Structural_Any _) = true
    | structural_is_any _ = false

  fun structural_same_shape
      (Structural_Any _, Structural_Any _) = true
    | structural_same_shape
        (Structural_Node
           {head = left_head, arguments = left_arguments, ...},
         Structural_Node
           {head = right_head, arguments = right_arguments, ...}) =
        same_constructor (left_head, right_head) andalso
          eq_list structural_same_shape
            (left_arguments, right_arguments)
    | structural_same_shape _ = false

  fun structural_subsumes
      (Structural_Any _, _) = true
    | structural_subsumes
        (Structural_Node
           {head = left_head, arguments = left_arguments, ...},
         Structural_Node
           {head = right_head, arguments = right_arguments, ...}) =
        same_constructor (left_head, right_head) andalso
          eq_list structural_subsumes
            (left_arguments, right_arguments)
    | structural_subsumes _ = false

  fun structural_intersection
      (Structural_Any _, right) =
        SOME (erase_structural_bindings right)
    | structural_intersection
        (left, Structural_Any _) =
        SOME (erase_structural_bindings left)
    | structural_intersection
        (Structural_Node
           {head = left_head, family = left_family,
            arguments = left_arguments},
         Structural_Node
           {head = right_head, family = _,
            arguments = right_arguments}) =
        if same_constructor (left_head, right_head)
        then
          (case map2
              (fn left => fn right =>
                structural_intersection (left, right))
              left_arguments right_arguments of
             intersections =>
               if List.all is_some intersections
               then
                 SOME
                   (Structural_Node
                     {head = left_head,
                      family = left_family,
                      arguments = map the intersections})
               else NONE)
        else NONE

  fun family_members
      (Structural_Family {members, ...}) = members

  fun same_family
      (Structural_Family
         {name = left_name, members = left_members},
       Structural_Family
         {name = right_name, members = right_members}) =
    left_name = right_name andalso
      eq_list same_constructor (left_members, right_members)

  fun structural_is_total (Structural_Any _) = true
    | structural_is_total
        (Structural_Node {head, family = SOME family, arguments}) =
        (case family_members family of
           [only] =>
             same_constructor (head, only) andalso
               List.all structural_is_total arguments
         | _ => false)
    | structural_is_total _ = false

  fun structural_root_region (Structural_Any _) =
        Structural_Any NONE
    | structural_root_region
        (Structural_Node {head, family, arguments}) =
        (case family of
           SOME known =>
             (case family_members known of
                [only] =>
                  if same_constructor (head, only)
                  then
                    Structural_Node
                      {head = head,
                       family = family,
                       arguments =
                         map structural_root_region arguments}
                  else Structural_Any NONE
              | _ => Structural_Any NONE)
         | NONE => Structural_Any NONE)

  fun structural_root_group_pattern pattern =
    (case structural_root_region pattern of
       Structural_Any _ => pattern
     | region => region)

  fun structural_semantically_subsumes
      (Structural_Any _, _) = true
    | structural_semantically_subsumes
        (left, Structural_Any _) =
        structural_is_total left
    | structural_semantically_subsumes
        (Structural_Node
           {head = left_head, arguments = left_arguments, ...},
         Structural_Node
           {head = right_head, arguments = right_arguments, ...}) =
        same_constructor (left_head, right_head) andalso
          eq_list structural_semantically_subsumes
            (left_arguments, right_arguments)
    | structural_semantically_subsumes _ = false

  fun replace_column index replacements row =
    take index row @ replacements @ drop (index + 1) row

  fun first_structural_column rows =
    let
      val width =
        (case rows of [] => 0 | row :: _ => length row)
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
                      Structural_Node {head, family, ...} =>
                        SOME (head, family)
                    | Structural_Any _ => NONE))
                 rows
             val family =
               (case heads of
                  [] => NONE
                | (_, NONE) :: _ => NONE
                | (_, SOME candidate) :: rest =>
                    if List.all
                        (fn (_, SOME other) =>
                              same_family (candidate, other)
                          | _ => false)
                        rest
                    then SOME candidate
                    else NONE)

             fun specialize member row =
               (case nth row column of
                  Structural_Any _ =>
                    SOME
                      (replace_column column
                        (replicate (constructor_arity member)
                          (Structural_Any NONE))
                        row)
                | Structural_Node {head, arguments, ...} =>
                    if same_constructor (head, member)
                    then SOME
                      (replace_column column arguments row)
                    else NONE)
           in
             (case family of
                NONE => false
              | SOME known =>
                  List.all
                    (fn member =>
                      matrix_covers_all
                        (map_filter (specialize member) rows))
                    (family_members known))
           end)

  fun patterns_cover_all patterns =
    matrix_covers_all
      (map (fn pattern => [erase_structural_bindings pattern])
        patterns)

  fun subject_value
      (Structural_Subject {value, ...}) = value

  fun subject_children
      (Structural_Subject {children, ...}) = children

  fun fresh_pattern_subject ctxt pattern =
    let
      fun fresh_leaf () =
        Free
          ("_urust_region_" ^
            string_of_int (serial ()), dummyT)

      fun open_pattern (Structural_Any _) =
            let
              val free = fresh_leaf ()
            in
              (Basic_Generated free,
               Structural_Subject {value = free, children = []})
            end
        | open_pattern
            (Structural_Node {head, arguments, ...}) =
            let
              val opened = map open_pattern arguments
              val basics = map fst opened
              val subjects = map snd opened
              val value =
                Term.list_comb
                  (constructor_term head,
                   map subject_value subjects)
            in
              (Basic_Resolved
                (constructor_term head, basics),
               Structural_Subject
                 {value = value, children = subjects})
            end

      val (basic, subject) = open_pattern pattern
    in
      Opened_Pattern
        {abstraction =
           bind_basic_pattern ctxt R.empty_environment basic,
         subject = subject}
    end

  fun selection_subject
      (Selected_Any {subject, ...}) = subject
    | selection_subject
        (Selected_Node {subject, ...}) = subject

  fun make_structural_selection_witness
      pattern region subject =
    let
      fun refine_arguments [] [] [] = SOME []
        | refine_arguments
            (pattern :: patterns)
            (region :: regions)
            (subject :: subjects) =
            (case refine pattern region subject of
               NONE => NONE
             | SOME selected =>
                 Option.map
                   (fn rest => selected :: rest)
                   (refine_arguments
                     patterns regions subjects))
        | refine_arguments _ _ _ = NONE
      and refine
          (Structural_Any binder) _ subject =
            SOME
              (Selected_Any
                {binder = binder, subject = subject})
        | refine
            (Structural_Node
              {head = pattern_head,
               arguments = pattern_arguments, ...})
            (Structural_Node
              {head = region_head,
               arguments = region_arguments, ...})
            subject =
            if same_constructor
                (pattern_head, region_head)
            then
              Option.map
                (fn selected_arguments =>
                  Selected_Node
                    {subject = subject,
                     arguments = selected_arguments})
                (refine_arguments
                  pattern_arguments region_arguments
                  (subject_children subject))
            else NONE
        | refine (Structural_Node _) (Structural_Any _) _ =
            NONE
    in refine pattern region subject end

  fun select_structural_clause ctxt pattern
      (Decision_State {region, subject, ...}) =
    (case make_structural_selection_witness
        pattern region subject of
       SOME witness =>
         Reused_Clause_Selection
           {region = region, witness = witness}
     | NONE =>
         let
           val shape = erase_structural_bindings pattern
           val Opened_Pattern
             {abstraction, subject = opened_subject} =
               fresh_pattern_subject ctxt shape
           val witness =
             (case make_structural_selection_witness
                 pattern shape opened_subject of
                SOME selected => selected
              | NONE =>
                  error
                    "urust_expr: internal invalid opened structural selection")
         in
           if structural_semantically_subsumes
               (shape, region)
           then
             Opened_Covering_Clause_Selection
               {region = shape,
                abstraction = abstraction,
                witness = witness}
           else
             Opened_Partial_Clause_Selection
               {region = shape,
                abstraction = abstraction,
                witness = witness}
         end)

  fun structural_bindings
      (Selected_Any {binder = NONE, ...}) = []
    | structural_bindings
        (Selected_Any
          {binder = SOME free, subject}) =
        [(free, subject_value subject)]
    | structural_bindings
        (Selected_Node {arguments, ...}) =
        maps structural_bindings arguments

  fun specialize_term bindings =
    if null bindings then I
    else Term.subst_free bindings

  fun close_clause_scope Direct_Clause_Scope rhs = rhs
    | close_clause_scope
        (Alias_Clause_Scope close_scope) rhs =
        close_scope rhs
    | close_clause_scope
        (Nested_Clause_Scope close_scope) rhs =
        close_scope rhs
    | close_clause_scope
        (Transformed_Clause_Scope close_scope) rhs =
        close_scope rhs

  fun scope_wrapper_operation
      (Alias_Scope_Wrapper operation) = operation
    | scope_wrapper_operation
        (Nested_Scope_Wrapper operation) = operation
    | scope_wrapper_operation
        (Transformed_Scope_Wrapper operation) = operation

  fun scope_wrapper_is_nested
      (Nested_Scope_Wrapper _) = true
    | scope_wrapper_is_nested _ = false

  fun scope_wrapper_is_transformed
      (Transformed_Scope_Wrapper _) = true
    | scope_wrapper_is_transformed _ = false

  fun extend_generated_test generated NONE = SOME generated
    | extend_generated_test generated (SOME prior) =
        SOME (T.binary And prior generated)

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
      fun requires_registered_nested_case
            (Case_Constructor (info, _, _ :: _)) =
            R.constructor_is_exact_registered info
        | requires_registered_nested_case _ = false

      fun normalize_arguments [] = ([], [], [])
        | normalize_arguments (argument :: rest) =
            let
              val (argument', guards0, wrappers0) =
                (case argument of
                   Case_Constructor (info, _, []) =>
                     if R.constructor_is_exact_registered info then
                       let
                         val temporary =
                           Free
                             ("_urust_pat_" ^
                               string_of_int (serial ()), dummyT)
                         val guard =
                           T.binary Eq (T.literal temporary)
                             (T.literal (R.constructor_term info))
                       in
                         (Basic_Generated temporary, [guard], [])
                       end
                     else
                       normalize_pattern_for_nested
                         compiler ctxt environment argument
                 | _ =>
                     if requires_nested_match argument orelse
                        requires_registered_nested_case argument
                     then
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
                         (Basic_Generated temporary, [guard],
                          [(case argument of
                              Case_Slice_Suffix _ =>
                                Transformed_Scope_Wrapper
                                  wrapper
                            | _ =>
                                Nested_Scope_Wrapper wrapper)])
                       end
                     else
                       normalize_pattern_for_nested
                         compiler ctxt environment argument)
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
         in
           (basic, guards,
            wrappers @ [Alias_Scope_Wrapper wrap])
         end
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
         in
           (Basic_Wild NONE, [guard],
            [Transformed_Scope_Wrapper wrap])
         end
     | _ =>
         normalize_pattern_for_nested
           compiler ctxt environment pattern)

  fun normalize_case_alternative compiler ctxt value
      (pattern, environment) =
    let
      val (basic_pattern, generated_guards, wrappers) =
        normalize_extended_pattern
          compiler ctxt environment (T.literal value) pattern
      val generated_test =
        fold extend_generated_test generated_guards NONE
      val scope =
        if null wrappers
        then Direct_Clause_Scope
        else
          let
            val close_scope =
              fn rhs =>
                fold_rev
                  (fn wrapper => fn body =>
                    scope_wrapper_operation wrapper body)
                  wrappers rhs
          in
            if List.exists scope_wrapper_is_transformed
                wrappers
            then Transformed_Clause_Scope close_scope
            else if List.exists scope_wrapper_is_nested
                wrappers
            then Nested_Clause_Scope close_scope
            else Alias_Clause_Scope close_scope
          end
    in
      Case_Clause
        {structural_pattern =
           structural_pattern_of_basic
             ctxt environment basic_pattern,
         generated_test = generated_test,
         scope = scope}
    end

  fun compile_pattern_case ctxt scrutinee arms =
        compile_decision_case ctxt NONE scrutinee
          (map
            (fn (pattern, environment, source_guard, body) =>
              {patterns = [pattern],
               environment = environment,
               source_guard = source_guard,
               body = body})
            arms)

  and compile_decision_case ctxt explicit_fallback scrutinee source_arms =
    let
      val value =
        Free
          ("_urust_case_value_" ^
            string_of_int (serial ()), dummyT)

      fun case_term_on subject branches =
        T.case_guard T.true_value subject
          (fold_rev T.case_cons branches T.case_nil)

      fun plain_fragment semantic =
        Compiled_Decision_Fragment
          {semantic = semantic, historical = semantic}

      fun fragment_semantic
          (Compiled_Decision_Fragment {semantic, ...}) =
        semantic

      fun compatibility_term
          (Compiled_Decision_Fragment
            {historical, ...}) =
        historical

      fun generated_wild rhs =
        bind_basic_pattern ctxt R.empty_environment
          (Basic_Wild NONE) rhs

      val terminal_fallback =
        the_default T.undefined_value explicit_fallback

      fun selector_of [] = terminal_fallback
        | selector_of branches =
            case_term_on value branches

      val source_arms_with_fallback =
        source_arms @
          (case explicit_fallback of
             NONE => []
           | SOME body =>
               [{patterns = [Case_Wild Position.none],
                 environment = R.empty_environment,
                 source_guard = NONE,
                 body = body}])

      fun normalize_arm
          (arm_index,
           {patterns, environment, source_guard, body} :
             decision_source_arm) =
        let
          fun normalize_alternative
              (alternative_index, pattern) =
            Alternative_Plan
              {position =
                 {arm_index = arm_index,
                  alternative_index = alternative_index},
               clause =
                 normalize_case_alternative
                   compile_pattern_case ctxt value
                   (pattern, environment)}
        in
          Arm_Plan
            {arm_index = arm_index,
             alternatives =
               map_index normalize_alternative patterns,
             source_guard = source_guard,
             body = body}
        end

      val arm_plans =
        map_index normalize_arm source_arms_with_fallback

      fun rows_of_arm
          (Arm_Plan
            {alternatives, source_guard, body, ...}) =
        map
          (fn Alternative_Plan
                {position, clause} =>
            Decision_Row
              {position = position,
               clause = clause,
               source_guard = source_guard,
               body = body})
          alternatives

      val rows = maps rows_of_arm arm_plans

      fun unconditional_total_row
          (Decision_Row
            {clause =
               Case_Clause
                 {structural_pattern, generated_test, ...},
             source_guard, ...}) =
        is_none generated_test andalso
          is_none source_guard andalso
          structural_is_total structural_pattern

      fun validate_row_reachability [] = ()
        | validate_row_reachability [_] = ()
        | validate_row_reachability (row :: rest) =
            if unconditional_total_row row
            then error "clauses are redundant"
            else validate_row_reachability rest

      (* The explicit false branch used by matches! is a real final decision row. Keeping this
         elementary usefulness check in the typed matrix preserves the legacy redundancy diagnostic
         for `_` and binder patterns instead of optimizing the unreachable row away. *)
      val _ = validate_row_reachability rows

      val root_state =
        Decision_State
          {region = Structural_Any NONE,
           subject =
             Structural_Subject
               {value = value, children = []},
           exclusions = []}

      fun row_arm
          (Decision_Row
            {position = {arm_index, ...}, ...}) =
        arm_index

      fun row_position
          (Decision_Row {position, ...}) =
        position

      fun row_pattern
          (Decision_Row
            {clause =
               Case_Clause {structural_pattern, ...}, ...}) =
        structural_pattern

      fun row_has_generated_test
          (Decision_Row
            {clause =
               Case_Clause {generated_test, ...}, ...}) =
        is_some generated_test

      fun row_shape row =
        erase_structural_bindings (row_pattern row)

      fun drop_source_arm arm_index rows =
        drop_prefix (fn row => row_arm row = arm_index) rows

      fun same_source_position
          ({arm_index = left_arm,
            alternative_index = left_alternative} : source_position,
           {arm_index = right_arm,
            alternative_index = right_alternative} : source_position) =
        left_arm = right_arm andalso
          left_alternative = right_alternative

      fun row_exclusion row pattern =
        Decision_Exclusion
          {position = row_position row, pattern = pattern}

      fun same_outer_group (left, right) =
        structural_same_shape (left, right) orelse
          (structural_is_total left andalso
           structural_is_total right)

      fun add_structural_group
          row group_pattern exclusion_pattern [] =
            let
              val exclusion =
                row_exclusion row exclusion_pattern
            in
              [Structural_Group
                {pattern = group_pattern,
                 members = [row],
                 catchall_exclusions = [exclusion]}]
            end
        | add_structural_group
            row group_pattern exclusion_pattern
            (Structural_Group
              {pattern, members,
               catchall_exclusions} :: rest) =
            if same_outer_group (pattern, group_pattern)
            then
              Structural_Group
                {pattern = pattern,
                 members = members @ [row],
                 catchall_exclusions =
                   row_exclusion row exclusion_pattern ::
                     catchall_exclusions} ::
                rest
            else
              Structural_Group
                {pattern = pattern,
                 members = members,
                 catchall_exclusions = catchall_exclusions} ::
                add_structural_group
                  row group_pattern exclusion_pattern rest

      fun install_source_catchall row NONE =
            SOME
              (Structural_Group
                {pattern = row_pattern row,
                 members = [row],
                 catchall_exclusions = []})
        | install_source_catchall row
            (SOME
              (group as
                Structural_Group {pattern, ...})) =
            (case (pattern, row_pattern row) of
               (Structural_Any NONE,
                bound as Structural_Any (SOME _)) =>
                 SOME
                   (Structural_Group
                     {pattern = bound,
                      members = [row],
                      catchall_exclusions = []})
             | _ => SOME group)

      fun add_root_group row
          (Outer_Group_Plan {groups, catchall}) =
        let
          val shape = row_shape row
          val group_pattern =
            structural_root_group_pattern shape
          val (groups', catchall') =
            if structural_is_any shape
            then
              (groups,
               install_source_catchall row catchall)
            else
              (add_structural_group
                 row group_pattern shape groups,
               catchall)
        in
          Outer_Group_Plan
            {groups = groups',
             catchall = catchall'}
        end

      fun add_historical_group row shape [] =
            [Structural_Group
              {pattern = shape,
               members = [row],
               catchall_exclusions =
                 [row_exclusion row shape]}]
        | add_historical_group row shape
            (Structural_Group
              {pattern, members,
               catchall_exclusions} :: rest) =
            if same_outer_group (pattern, shape)
            then
              Structural_Group
                {pattern = pattern,
                 members = members @ [row],
                 catchall_exclusions =
                   if row_has_generated_test row
                   then
                     row_exclusion row shape ::
                       catchall_exclusions
                   else catchall_exclusions} ::
                rest
            else
              Structural_Group
                {pattern = pattern,
                 members = members,
                 catchall_exclusions = catchall_exclusions} ::
                add_historical_group row shape rest

      fun transformed_compatibility_tail
          (Decision_Row
            {clause =
               Case_Clause
                 {scope = Transformed_Clause_Scope _, ...},
             ...}) = true
        | transformed_compatibility_tail _ = false

      fun row_has_source_guard
          (Decision_Row {source_guard, ...}) =
        is_some source_guard

      fun prefix_has_structural_group prefix =
        List.exists
          (not o structural_is_any o row_shape) prefix

      fun compatibility_outer_prefix _ prefix [] =
            (rev prefix, false)
        | compatibility_outer_prefix guarded_arm prefix
            (row :: rest) =
            if transformed_compatibility_tail row
            then (rev prefix, true)
            else
              (case guarded_arm of
                 SOME active_arm =>
                   if row_arm row = active_arm
                   then
                     compatibility_outer_prefix guarded_arm
                       (row :: prefix) rest
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
                     compatibility_outer_prefix guarded_arm'
                       (row :: prefix) rest
                   end)

      fun historical_groups_of
          (Structural_Group {members, ...}) =
        fold
          (fn row => fn groups =>
            add_historical_group
              row (row_shape row) groups)
          members []

      fun historical_group_exclusions
          (Structural_Group {members, ...}) =
        (case members of
           [] =>
             error
               "urust_expr: internal empty structural group"
         | first :: rest =>
             row_exclusion first (row_shape first) ::
               map
                 (fn row =>
                   row_exclusion row (row_shape row))
                 (filter row_has_generated_test rest))

      fun plan_root_suffix context planned_rows =
        let
          val Outer_Group_Plan
            {groups, catchall = source_catchall} =
            fold add_root_group planned_rows
              (Outer_Group_Plan
                {groups = [], catchall = NONE})
          val structural_patterns =
            map
              (fn Structural_Group {pattern, ...} =>
                pattern)
              groups
          val catchall_exclusions =
            maps
              (fn Structural_Group
                    {catchall_exclusions, ...} =>
                catchall_exclusions)
              groups
          val outer_catchall =
            (case source_catchall of
               NONE => NONE
             | SOME group =>
                 if patterns_cover_all structural_patterns
                 then NONE
                 else SOME group)
          fun group_is_coverage_complete
              (Structural_Group {pattern, members, ...}) =
            structural_is_total pattern andalso
              List.exists
                (structural_is_total o row_shape)
                members
          val coverage_complete_group =
            (case (groups, outer_catchall) of
               ([group], NONE) =>
                 if group_is_coverage_complete group
                 then SOME group
                 else NONE
             | _ => NONE)
          (*
            A single structurally total group containing a total source row is coverage-complete.
            Both normal and compatibility historical rendering must open that planned group directly
            instead of reconstructing a redundant root tail. This rule depends only on typed
            structural coverage, not on any particular constructor or tuple shape.
          *)
          val (historical_prefix_rows,
               reconstruct_historical_root_tail) =
            (case coverage_complete_group of
               SOME _ => (planned_rows, false)
             | NONE =>
                 (case context of
                    Normal_Root_Plan =>
                      compatibility_outer_prefix
                        NONE [] planned_rows
                  | Compatibility_Root_Plan _ =>
                      ([], not (null planned_rows))))
          val historical_groups =
            (case coverage_complete_group of
               SOME group =>
                 [group]
             | NONE =>
                 if reconstruct_historical_root_tail
                 then
                   fold
                     (fn row => fn planned_groups =>
                       if structural_is_any (row_shape row)
                       then planned_groups
                       else
                         add_historical_group
                           row (row_shape row)
                           planned_groups)
                     historical_prefix_rows []
                 else maps historical_groups_of groups)
          val historical_patterns =
            map
              (fn Structural_Group {pattern, ...} =>
                pattern)
              historical_groups
          val historical_catchall_exclusions =
            maps historical_group_exclusions
              historical_groups
          val historical_outer_catchall =
            if reconstruct_historical_root_tail
            then
              if patterns_cover_all historical_patterns
              then NONE
              else
                SOME
                  (the_default
                    (Structural_Group
                      {pattern = Structural_Any NONE,
                       members = [],
                       catchall_exclusions = []})
                    source_catchall)
            else
              (case source_catchall of
                 NONE => NONE
               | SOME group =>
                   if patterns_cover_all historical_patterns
                   then NONE
                   else SOME group)
        in
          Root_Suffix_Plan
            {rows = planned_rows,
             groups = groups,
             outer_catchall = outer_catchall,
             catchall_exclusions = catchall_exclusions,
             historical_groups = historical_groups,
             historical_outer_catchall =
               historical_outer_catchall,
             historical_catchall_exclusions =
               historical_catchall_exclusions}
        end

      fun historical_following_exclusion
          (Structural_Group {members, ...}) =
        (case members of
           [] =>
             error
               "urust_expr: internal empty historical structural group"
         | first :: _ =>
             if row_has_generated_test first
             then NONE
             else
               SOME
                 (row_exclusion first (row_shape first)))

      fun nested_compatibility_scope
          (Decision_Row
            {clause =
               Case_Clause
                 {scope = Nested_Clause_Scope _,
                  generated_test = SOME _, ...},
             ...}) = true
        | nested_compatibility_scope _ = false

      fun rows_after_position _ [] =
            error
              "urust_expr: internal missing compatibility row"
        | rows_after_position position (row :: rest) =
            if same_source_position
                (position, row_position row)
            then rest
            else rows_after_position position rest

      fun nested_compatibility_suffix planned_rows
          (Structural_Group {members, ...}) =
        (case members of
           first :: _ =>
             if nested_compatibility_scope first
             then
               SOME
                 (rows_after_position
                   (row_position first) planned_rows)
             else NONE
         | [] =>
             error
               "urust_expr: internal empty historical structural group")

      datatype compatibility_root_cache_entry =
        Compatibility_Root_Cache_Entry of
          {context: root_plan_context,
           positions: source_position list,
           plan: root_suffix_plan}

      val compatibility_root_cache =
        Unsynchronized.ref
          ([] : compatibility_root_cache_entry list)

      fun same_position_list ([], []) = true
        | same_position_list
            (left :: left_rest, right :: right_rest) =
            same_source_position (left, right) andalso
              same_position_list (left_rest, right_rest)
        | same_position_list _ = false

      fun same_root_plan_context
          (Normal_Root_Plan, Normal_Root_Plan) = true
        | same_root_plan_context
            (Compatibility_Root_Plan left,
             Compatibility_Root_Plan right) =
            left = right
        | same_root_plan_context _ = false

      fun cached_compatibility_root _ _ [] = NONE
        | cached_compatibility_root context positions
            (Compatibility_Root_Cache_Entry
              {context = cached_context,
               positions = cached_positions,
               plan} :: rest) =
            if same_root_plan_context
                 (context, cached_context) andalso
               same_position_list
                (positions, cached_positions)
            then SOME plan
            else
              cached_compatibility_root
                context positions rest

      fun exclusion_position
          (Decision_Exclusion {position, ...}) = position

      fun exclusion_pattern
          (Decision_Exclusion {pattern, ...}) = pattern

      fun excluded_region exclusions position region =
        List.exists
          (fn exclusion =>
            same_source_position
              (exclusion_position exclusion, position) andalso
              structural_semantically_subsumes
                (exclusion_pattern exclusion, region))
          exclusions

      fun row_intersection
          (Decision_State {region, exclusions, ...}) row =
        (case structural_intersection
            (region, row_shape row) of
           NONE => NONE
         | SOME matched =>
             if excluded_region exclusions
                 (row_position row) matched
             then NONE
             else SOME matched)

      fun first_applicable _ [] = NONE
        | first_applicable state (row :: rest) =
            (case row_intersection state row of
               SOME matched =>
                 SOME
                   (Applicable_Row
                     {row = row,
                      decision_state = state,
                      remaining_rows = rest})
             | NONE => first_applicable state rest)

      fun add_exclusion
          (Decision_State {region, subject, exclusions})
          position pattern =
        Decision_State
          {region = region,
           subject = subject,
           exclusions =
             Decision_Exclusion
               {position = position, pattern = pattern} ::
             exclusions}

      fun selected_states
          (Decision_State {exclusions, ...})
          region selection =
        let val selected_subject = selection_subject selection
        in
        Selected_Row_State
          {selection = selection,
           nested_failure =
             Selected_Failure_Continuation
               {region = region,
                selection = selection,
                exclusions = exclusions},
           arm_failure =
             Enclosing_Branch_Continuation
               {region = region,
                subject = selected_subject,
                exclusions = exclusions}}
        end

      fun selected_failure_state
          (Selected_Failure_Continuation
            {region, selection, exclusions}) =
        Decision_State
          {region = region,
           subject = selection_subject selection,
           exclusions = exclusions}

      fun arm_failure_state
          (Enclosing_Branch_Continuation
            {region, subject, exclusions}) =
        Decision_State
          {region = region,
           subject = subject,
           exclusions = exclusions}

      fun compatibility_reconstructions
          scope shape generated_test source_guard
          alternative_rows arm_rows =
        let
          val alternative =
            if is_some generated_test andalso
               (case scope of
                  Nested_Clause_Scope _ => true
                | Transformed_Clause_Scope _ => true
                | _ => false)
            then
              [Compatibility_Reconstruction
                {failure = Alternative_Compatibility_Failure,
                 rows = alternative_rows}]
            else []
          val arm =
            if is_some source_guard andalso
               (case (scope, shape) of
                  (Direct_Clause_Scope, Structural_Node _) => true
                | _ => false)
            then
              [Compatibility_Reconstruction
                {failure = Arm_Compatibility_Failure,
                 rows = arm_rows}]
            else []
        in alternative @ arm end

      fun compatibility_rows _ [] = NONE
        | compatibility_rows target
            (Compatibility_Reconstruction
              {failure, rows} :: rest) =
            if failure = target
            then SOME rows
            else compatibility_rows target rest

      fun close_selected_clause
          (Case_Clause
            {generated_test, scope, ...})
          selection source_guard body
          alternative_failure arm_failure
          historical_alternative_failure
          historical_arm_failure =
        let
          val bindings =
            structural_bindings selection
          val specialize = specialize_term bindings
          val semantic_alternative =
            fragment_semantic alternative_failure
          val historical_alternative =
            (case historical_alternative_failure of
               SOME historical =>
                 compatibility_term historical
             | NONE =>
                 compatibility_term alternative_failure)
          val semantic_arm =
            fragment_semantic arm_failure
          val historical_arm =
            (case historical_arm_failure of
               SOME historical =>
                 compatibility_term historical
             | NONE =>
                 compatibility_term arm_failure)
          val semantic_guarded_body =
            (case source_guard of
               NONE => body
             | SOME guard =>
                 T.conditional guard body semantic_arm)
          val historical_guarded_body =
            (case source_guard of
               NONE => body
             | SOME guard =>
                 T.conditional guard body historical_arm)
          val semantic_scoped_body =
            specialize
              (close_clause_scope scope semantic_guarded_body)
          val historical_scoped_body =
            specialize
              (close_clause_scope scope historical_guarded_body)
          val semantic =
            (case generated_test of
               NONE => semantic_scoped_body
             | SOME test =>
                 T.conditional
                   (specialize test)
                   semantic_scoped_body semantic_alternative)
          val historical =
            (case generated_test of
               NONE => historical_scoped_body
             | SOME test =>
                 T.conditional
                   (specialize test)
                   historical_scoped_body
                   historical_alternative)
        in
          Compiled_Decision_Fragment
            {semantic = semantic,
             historical = historical}
        end

      fun compile_rows state remaining =
        (case first_applicable state remaining of
           NONE => plain_fragment terminal_fallback
         | SOME
             (Applicable_Row
               {row =
                  (row as
                    Decision_Row
                      {clause =
                         (clause as
                           Case_Clause
                             {structural_pattern, generated_test,
                              scope, ...}),
                       source_guard, body,
                       position =
                         (position as {arm_index, ...})}),
                decision_state, remaining_rows = rest,
                ...}) =>
             let
               val shape =
                 erase_structural_bindings structural_pattern

               fun compile_matched
                   (Selected_Row_State
                     {selection,
                      nested_failure,
                      arm_failure}) =
                 let
                   val next_alternative =
                     compile_rows
                       (selected_failure_state nested_failure)
                       rest
                   val next_arm =
                     compile_rows
                       (arm_failure_state arm_failure)
                       (drop_source_arm arm_index rest)
                   val arm_rows =
                     drop_source_arm arm_index rest
                   val reconstructions =
                     compatibility_reconstructions
                       scope shape generated_test source_guard
                       rest arm_rows
                   val historical_alternative_failure =
                     Option.map
                       (compile_compatibility_root
                         (Compatibility_Root_Plan
                           Alternative_Compatibility_Failure))
                       (compatibility_rows
                         Alternative_Compatibility_Failure
                         reconstructions)
                   val historical_arm_failure =
                     Option.map
                       (compile_compatibility_root
                         (Compatibility_Root_Plan
                           Arm_Compatibility_Failure))
                       (compatibility_rows
                         Arm_Compatibility_Failure
                         reconstructions)
                 in
                   close_selected_clause clause
                     selection source_guard body
                     next_alternative next_arm
                     historical_alternative_failure
                     historical_arm_failure
                 end
               val selection =
                 select_structural_clause ctxt
                   structural_pattern decision_state
             in
                (case selection of
                  Reused_Clause_Selection
                    {region, witness} =>
                    compile_matched
                      (selected_states
                        decision_state region witness)
                | Opened_Covering_Clause_Selection
                    {region, abstraction, witness} =>
                  let
                    val success =
                      compile_matched
                        (selected_states
                          decision_state region witness)
                    val subject =
                      (case decision_state of
                         Decision_State {subject, ...} =>
                           subject_value subject)
                  in
                    Compiled_Decision_Fragment
                      {semantic =
                         case_term_on subject
                           [abstraction
                             (fragment_semantic success)],
                       historical =
                         case_term_on subject
                           [abstraction
                             (compatibility_term success)]}
                  end
                | Opened_Partial_Clause_Selection
                    {region, abstraction, witness} =>
                  let
                   val selected_state =
                     selected_states
                       decision_state region witness
                   val success =
                     compile_matched selected_state
                   val failure =
                     compile_rows
                       (add_exclusion
                         decision_state position shape) rest
                   val subject =
                     (case decision_state of
                        Decision_State {subject, ...} =>
                          subject_value subject)
                 in
                   Compiled_Decision_Fragment
                     {semantic =
                        case_term_on subject
                          [abstraction
                             (fragment_semantic success),
                           generated_wild
                             (fragment_semantic failure)],
                      historical =
                        case_term_on subject
                          [abstraction
                             (compatibility_term success),
                           generated_wild
                             (compatibility_term failure)]}
                  end)
             end)

      and compile_outer_pattern planned_rows exclusions pattern =
        let
          val Opened_Pattern {abstraction, subject} =
            fresh_pattern_subject ctxt pattern
          val state =
            Decision_State
              {region = pattern,
               subject = subject,
               exclusions = exclusions}
          val compiled =
            compile_rows state planned_rows
        in
          Compiled_Outer_Branch
            {semantic =
               abstraction (fragment_semantic compiled),
             historical =
               abstraction (compatibility_term compiled)}
        end

      and compile_outer_group planned_rows exclusions
          (Structural_Group {pattern, ...}) =
        compile_outer_pattern planned_rows exclusions pattern

      and compile_outer_catchall planned_rows
          render_fragment render_branch exclusions
          (Structural_Group {pattern, ...}) =
        (case pattern of
           Structural_Any NONE =>
             let
               val Decision_State {subject, ...} = root_state
               val state =
                 Decision_State
                   {region = pattern,
                    subject = subject,
                    exclusions = exclusions}
             in
               generated_wild
                 (render_fragment
                   (compile_rows state planned_rows))
             end
         | Structural_Any (SOME _) =>
             render_branch
               (compile_outer_pattern
                 planned_rows exclusions pattern)
         | Structural_Node _ =>
             error
               "urust_expr: internal non-wild outer catchall")

      and render_semantic_root_suffix_plan
          (Root_Suffix_Plan
            {rows = planned_rows, groups,
             outer_catchall, catchall_exclusions, ...}) =
        let
          val branches =
            map
              (fn group =>
                let
                  val Compiled_Outer_Branch
                    {semantic, ...} =
                    compile_outer_group planned_rows [] group
                in semantic end)
              groups @
            (case outer_catchall of
               NONE => []
             | SOME group =>
                 [compile_outer_catchall planned_rows
                   fragment_semantic
                   (fn Compiled_Outer_Branch
                         {semantic, ...} =>
                     semantic)
                   catchall_exclusions group])
        in selector_of branches end

      and compile_historical_root_branch
          (Structural_Group {pattern, ...}) remaining =
        let
          val Opened_Pattern {abstraction, ...} =
            fresh_pattern_subject ctxt pattern
        in
          abstraction
            (compatibility_term
              (compile_compatibility_root
                (Compatibility_Root_Plan
                  Alternative_Compatibility_Failure)
                remaining))
        end

      and compile_historical_structural_groups
          _ [] _ root_suffix =
            ([], root_suffix)
        | compile_historical_structural_groups
            planned_rows (group :: rest)
            exclusions root_suffix =
            let
              val historical =
                (case root_suffix of
                   SOME remaining =>
                     compile_historical_root_branch
                       group remaining
                 | NONE =>
                     let
                       val Compiled_Outer_Branch
                         {historical, ...} =
                         compile_outer_group planned_rows
                           exclusions group
                     in historical end)
              val exclusions' =
                (case root_suffix of
                   SOME _ => exclusions
                 | NONE =>
                     (case historical_following_exclusion group of
                        NONE => exclusions
                      | SOME exclusion =>
                          exclusion :: exclusions))
              val root_suffix' =
                (case root_suffix of
                   SOME _ => root_suffix
                 | NONE =>
                     nested_compatibility_suffix
                       planned_rows group)
              val (following, final_root_suffix) =
                compile_historical_structural_groups
                  planned_rows rest exclusions'
                  root_suffix'
            in
              (historical :: following,
               final_root_suffix)
            end

      and render_historical_root_suffix_plan
          (Root_Suffix_Plan
            {rows = planned_rows,
             historical_groups,
             historical_outer_catchall,
             historical_catchall_exclusions, ...}) =
        let
          val (group_branches, root_suffix) =
            compile_historical_structural_groups
              planned_rows historical_groups [] NONE
          val branches =
            group_branches @
              (case historical_outer_catchall of
                 NONE => []
               | SOME group =>
                   [(case root_suffix of
                       SOME remaining =>
                         compile_historical_root_branch
                           group remaining
                     | NONE =>
                         compile_outer_catchall planned_rows
                           compatibility_term
                           (fn Compiled_Outer_Branch
                                 {historical, ...} =>
                             historical)
                           historical_catchall_exclusions
                           group)])
        in selector_of branches end

      and compile_compatibility_root context remaining =
        let
          val positions = map row_position remaining
          val plan =
            (case cached_compatibility_root
                context positions
                (!compatibility_root_cache) of
               SOME cached => cached
             | NONE =>
                 let
                   val planned =
                     plan_root_suffix context remaining
                   val _ =
                     compatibility_root_cache :=
                       Compatibility_Root_Cache_Entry
                         {context = context,
                          positions = positions,
                          plan = planned} ::
                       !compatibility_root_cache
                 in planned end)
          val historical =
            render_historical_root_suffix_plan plan
        in
          plain_fragment historical
        end

      val root_plan =
        plan_root_suffix Normal_Root_Plan rows
      val semantic_selector =
        render_semantic_root_suffix_plan root_plan
      val historical_selector =
        render_historical_root_suffix_plan root_plan
      val selector =
        compatibility_term
          (Compiled_Decision_Fragment
            {semantic = semantic_selector,
             historical = historical_selector})
    in
      T.bind scrutinee (Term.lambda value selector)
    end

  fun compile_case_internal ctxt explicit_fallback scrutinee arms =
    let
      fun source_arm
          (Prepared_Case_Arm
            {patterns, environment, ...},
           source_guard, body) =
        {patterns = patterns,
         environment = environment,
         source_guard = source_guard,
         body = body}
    in
      compile_decision_case ctxt explicit_fallback scrutinee
        (map source_arm arms)
    end

  fun compile_case ctxt fallback scrutinee arms =
    compile_case_internal ctxt fallback scrutinee arms
end
\<close>

end
