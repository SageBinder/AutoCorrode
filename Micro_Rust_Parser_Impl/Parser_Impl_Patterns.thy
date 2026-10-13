theory Parser_Impl_Patterns
  imports Parser_Impl_Resolution
begin

section\<open> Resolved patterns and case compilation \<close>

ML\<open>
signature URUST_PATTERNS =
sig
  type prepared_binding
  type prepared_case_arm

  datatype case_compilation_mode =
      Ordinary_Case_Compilation
    | Source_Match_Compilation

  datatype binder_site =
      Let_Binder
    | Let_Const_Binder
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
    case_compilation_mode ->
      Proof.context ->
      Position.T list ->
      term option ->
      term ->
      (prepared_case_arm * (term * Position.T) option * term) list ->
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
  Let_Binder admits directly irrefutable patterns, including recursive aliases and rest-only slices;
  Let_Const_Binder retains the narrower local-const pattern policy. Mutable_Let_Binder additionally
  restricts the source head to an identifier, wildcard, or top-level tuple and carries the mutable
  keyword position; and For_Binder resolves known constructors before enforcing irrefutability while
  admitting the same aliases and rest-only slices as Let_Binder.
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

  compile_case consumes a compilation mode, an optional explicit fallback, the scrutinee, and
  source-ordered triples of a prepared_case_arm, its already-lowered optional
  guard, and its already-lowered body.  Each lowered term must correspond to that prepared arm and its
  prepared_environment.  Compilation evaluates the scrutinee once, preserves source-arm and
  or-alternative order, binds pattern variables before evaluating guards and bodies, and makes a false
  guard fall through to the next alternative or arm. NONE uses the existing case encoding's unmatched
  behavior; SOME term installs that term as the terminal unmatched result. Compilation preserves the
  established shallow term shape. Ordinary_Case_Compilation retains the
  existing constructor-selector navigation used by `if let`, `while let`, `let ... else`, and
  `matches!`. Source_Match_Compilation additionally gives nonstructural source matches an explicit
  control target without placing generated comparison predicates under the match-token range.

  The representations of prepared_binding and prepared_case_arm are intentionally abstract.
  Pattern-position inspection, resolution policies, resolved/case/clause pattern datatypes,
  or-pattern expansion, normalization, generated names, recursive compiler helpers, and the exact
  coverage representation are implementation details. Callers may rely only on the signature and the
  scoping, ordering, validation, fallback, and term-shape contracts above.
*)
structure URust_Patterns :> URUST_PATTERNS =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure R = URust_Resolution
  structure Navigation = Micro_Rust_Semantic_Navigation

  datatype case_compilation_mode =
      Ordinary_Case_Compilation
    | Source_Match_Compilation

  val word_type_name =
    (case \<^typ>\<open>64 word\<close> of
       Type (name, _) => name
     | _ => error "urust_expr: internal word type is not a type constructor")

  fun literal_positions payload =
    (case payload of
       LP_Integer integer =>
         [integer_literal_numeric_position integer]
     | LP_Bool (_, pos) => [pos]
     | LP_String (_, pos) => [pos]
     | LP_ValAntiq antiquotation =>
         source_tokens
           (value_antiquotation_source_layout antiquotation)
         |> map #2)

  fun lower_literal_value ctxt environment payload =
    let
      val _ =
        (case payload of
           LP_Integer integer =>
             Option.app
               (fn suffix_pos =>
                 Navigation.defer_type ctxt suffix_pos word_type_name)
               (integer_literal_suffix_position integer)
         | _ => ())
      fun lower () = R.literal_value ctxt environment payload
    in
      (case literal_positions payload of
         [] => lower ()
       | positions =>
           Navigation.with_source positions (fn () =>
             Navigation.annotate Navigation.Primary
               (Const
                 (\<^const_name>\<open>Core_Expression.literal\<close>,
                  dummyT))
               (lower ())))
    end

  type binding_signature = string * Position.T

  datatype binder_site =
      Let_Binder
    | Let_Const_Binder
    | Mutable_Let_Binder of Position.T
    | For_Binder

  datatype mutable_rhs_mode =
      Plain_Rhs
    | Allocate_Rhs

  fun position (P_Wild pos) = pos
    | position (P_Ident (_, pos)) = pos
    | position (P_Literal payload) = literal_position payload
    | position (P_Path path) = path_position path
    | position (P_Constr (path, _, _)) = path_position path
    | position (P_Tuple (_, layout)) = source_span layout
    | position (P_Group (pattern, _)) = position pattern
    | position (P_Borrow (_, _, layout)) =
        the_source_token_position layout Operator_Token
    | position (P_Alias (_, _, _, layout)) =
        the_source_token_position layout Operator_Token
    | position (P_Range (_, _, _, layout)) =
        the_source_token_position layout Operator_Token
    | position (P_Slice (_, layout)) = source_span layout
    | position (P_Struct (path, _, _)) = path_position path
    | position (P_Or (_, layout)) =
        the_source_token_position layout Operator_Token

  fun reject_reference_patterns pattern =
    let
      fun reject (P_Borrow (_, _, layout)) =
            error ("urust_expr: reference patterns are not implemented" ^
              Position.here
                (the_source_token_position layout Operator_Token))
        | reject (P_Constr (_, arguments, _)) = List.app reject arguments
        | reject (P_Tuple (arguments, _)) = List.app reject arguments
        | reject (P_Group (inner, _)) = reject inner
        | reject (P_Alias (_, _, inner, _)) = reject inner
        | reject (P_Range (_, lower, upper, _)) =
            (reject lower; reject upper)
        | reject (P_Slice (items, _)) =
            List.app
              (fn SI_Pat nested => reject nested | SI_Rest _ => () | SI_BoundRest _ => ()) items
        | reject (P_Struct (_, fields, _)) =
            List.app
              (fn SF_Field (_, _, nested) => reject nested
                | SF_Shorthand _ => ()
                | SF_Rest _ => ()) fields
        | reject (P_Or (alternatives, _)) = List.app reject alternatives
        | reject _ = ()
    in reject pattern end

  fun strip_groups (P_Group (pattern, _)) = strip_groups pattern
    | strip_groups pattern = pattern

  fun arm_pattern (UR_Arm (pattern, _, _, _)) = pattern
  fun arm_guard (UR_Arm (_, guard, _, _)) = guard

  fun classify_match ctxt arms pos =
    let
      val resolver = R.make_constructor_resolver ctxt pos

      fun registered_switch_capability path =
        (case R.classify_registered_literal ctxt resolver path of
           R.Unregistered_Literal => false
         | R.Registered_Value_Literal => true
         | R.Registered_Constructor_Literal => false)

      (* Every pattern admits case lowering; the capability records whether it also admits
         numeral-switch lowering. *)
      fun switch_capability pattern =
        (case strip_groups pattern of
           P_Literal (LP_Integer _) => true
         | P_Ident identifier =>
             registered_switch_capability (make_single_path identifier)
         | P_Path path => registered_switch_capability path
         | P_Wild _ => true
         | P_Or (alternatives, _) =>
             List.all I (map switch_capability alternatives)
         | _ => false)
      (* Classify every arm and or-alternative before the guard test: constructor resolution and
         literal classification can raise errors. *)
      val capabilities = map (switch_capability o arm_pattern) arms
    in
      if List.exists (is_some o arm_guard) arms then MF_Case
      else if List.all I capabilities then MF_Switch
      else MF_Case
    end

  fun first_guard_position [] = NONE
    | first_guard_position
        (UR_Arm (_, SOME (_, pos), _, _) :: _) = SOME pos
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
    | Resolved_Navigated of Position.T list * resolved_pattern
    | Resolved_Or of resolved_pattern list * Position.T
  and resolved_slice_item =
      Resolved_Slice_Pattern of resolved_pattern
    | Resolved_Slice_Rest of Position.T
    | Resolved_Slice_Bound_Rest of
        binding_signature * Position.T * Position.T

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
    | resolved_position (Resolved_Navigated (_, inner)) =
        resolved_position inner
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

  fun same_coverage_family
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
        | coverage (Resolved_Slice ([Resolved_Slice_Rest _], _)) =
            Coverage_Total
        | coverage (Resolved_Slice ([Resolved_Slice_Bound_Rest _], _)) =
            Coverage_Total
        | coverage (Resolved_Slice _) = Coverage_Partial
        | coverage (Resolved_Navigated (_, inner)) = coverage inner
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
                        same_coverage_family (first, family)) (tl families)
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
      val pending_reports =
        Unsynchronized.ref ([]: (unit -> unit) list)
      fun defer report =
        pending_reports := report :: !pending_reports

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
                        defer
                          (fn () =>
                            R.report_constructor ctxt
                              (make_single_path (name, pos)) info);
                        Resolved_Constructor (info, pos, []))))
         | P_Literal payload => Resolved_Value payload
         | P_Path path =>
             (case R.resolve_constructor ctxt resolver path of
                SOME info =>
                  let
                    val (name, pos) =
                      segment_identifier (final_segment path)
                  in
                    check_constructor_arity name pos info [];
                    defer
                      (fn () =>
                        R.report_constructor ctxt path info);
                    Resolved_Constructor (info, pos, [])
                  end
              | NONE => Resolved_Path path)
         | P_Constr (path, arguments, _) =>
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
                   defer
                     (fn () =>
                       R.report_constructor ctxt path info);
                   Resolved_Constructor
                     (info, pos, map resolve arguments)))
              end
         | P_Tuple (arguments, layout) =>
             Resolved_Tuple
               (map resolve arguments, source_span layout)
         | P_Group (inner, _) => resolve inner
         | P_Borrow (_, inner, _) =>
             (* Binding sites reject every reference pattern before resolution, so only case
                patterns reach this point; they treat the reference as a syntax-only wrapper. *)
             resolve inner
         | P_Alias ("_", pos, _, _) =>
             error ("urust_expr: alias pattern binder cannot be `_`" ^
               Position.here pos)
         | P_Alias (name, pos, inner, layout) =>
             Resolved_Alias
               (binding name pos, resolve inner,
                the_source_token_position layout Operator_Token)
         | P_Range (_, P_Range _, _, layout) =>
             error ("urust_expr: range patterns are non-associative" ^
               Position.here
                 (the_source_token_position layout Operator_Token))
         | P_Range (kind, lower, upper, layout) =>
             Resolved_Range
               (kind, resolve_value lower, resolve_value upper,
                the_source_token_position layout Operator_Token)
         | P_Slice (items, layout) =>
             let
               fun check_rest seen_rest rest_pos =
                 if seen_rest then
                   error ("urust_expr: slice pattern has multiple `..` rest entries" ^
                     Position.here rest_pos)
                 else ()
               fun resolve_items _ [] = []
                 | resolve_items seen_rest (SI_Rest rest_pos :: rest) =
                     (check_rest seen_rest rest_pos;
                      Resolved_Slice_Rest rest_pos :: resolve_items true rest)
                 | resolve_items seen_rest
                     (SI_BoundRest (name, name_pos, alias_pos, rest_pos) :: rest) =
                     (* A rest name is always a binder, even if a constructor has that spelling. *)
                     (check_rest seen_rest rest_pos;
                      if name = "_" then
                        error ("urust_expr: alias pattern binder cannot be `_`" ^
                          Position.here name_pos)
                      else ();
                      Resolved_Slice_Bound_Rest
                        (binding name name_pos, alias_pos, rest_pos) ::
                      resolve_items true rest)
                 | resolve_items seen_rest (SI_Pat nested :: rest) =
                     Resolved_Slice_Pattern (resolve nested) ::
                       resolve_items seen_rest rest
             in
               Resolved_Navigated
                 (source_token_positions_for layout
                    [Delimiter_Token "[",
                     Operator_Token,
                     Delimiter_Token "..",
                     Delimiter_Token "]"],
                  Resolved_Slice
                    (resolve_items false items, source_span layout))
             end
         | P_Struct (path, fields, _) =>
             let
               val pos = #2 (segment_identifier (final_segment path))
             in
             (case R.resolve_struct_pattern ctxt resolver
                 (path, fields) of
                R.Resolved_Constructor_Struct (info, ordered) =>
                  let
                    val _ =
                      defer
                        (fn () =>
                          R.report_struct_constructor ctxt path info)
                    fun resolve_field
                        {selector, field_reference, source_position,
                         pattern, shorthand} =
                      (* Generated Rust fields have their own source identity even at shorthand
                         binders. Native HOL shorthand retains its binder-only navigation policy. *)
                      (case if shorthand andalso is_none field_reference
                            then NONE else source_position of
                         SOME source_pos =>
                           defer
                             (fn () =>
                               R.report_field ctxt source_pos
                                 selector field_reference)
                       | NONE => ();
                       resolve pattern)
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
         | P_Or (alternatives, layout) =>
             Resolved_Or
               (map resolve alternatives,
                the_source_token_position layout Operator_Token))
    in
      (case policy of
         Resolve_Constructor_Case => ()
       | _ => reject_reference_patterns pattern);
      (resolve pattern, rev (!pending_reports))
    end

  fun emit_semantic_reports reports =
    List.app (fn report => report ()) reports

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
                  | Resolved_Slice_Rest _ => []
                  | Resolved_Slice_Bound_Rest (binder_sig, _, _) =>
                      [binder_sig]) items)
        | collect (Resolved_Navigated (_, inner)) = collect inner
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

  fun directly_irrefutable allow_extended pattern =
    let
      fun direct (Resolved_Bind _) = true
        | direct (Resolved_Wild _) = true
        | direct (Resolved_Tuple (patterns, _)) =
            not (null patterns) andalso List.all direct patterns
        | direct (Resolved_Alias (_, inner, _)) =
            allow_extended andalso direct inner
        | direct (Resolved_Slice ([Resolved_Slice_Rest _], _)) =
            allow_extended
        | direct (Resolved_Slice ([Resolved_Slice_Bound_Rest _], _)) =
            allow_extended
        | direct (Resolved_Navigated (_, inner)) = direct inner
        | direct _ = false
    in direct pattern end

  fun constrain_pattern_abstraction typ pos abstraction =
    Type.constraint (typ --> dummyT) (T.source_position pos abstraction)

  fun direct_abstraction ctxt report_wildcards allow_extended environment pattern =
    let
      fun has_alias (Resolved_Alias _) = true
        | has_alias (Resolved_Tuple (patterns, _)) = exists has_alias patterns
        | has_alias _ = false
      fun list_abstraction pos abstraction =
        Option.map
          (fn bind => fn body =>
            constrain_pattern_abstraction (HOLogic.listT dummyT) pos (bind body))
          abstraction
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
                  (* Alias continuations bind expressions, not the curried functions used while
                     opening a tuple. Open all tuple slots before applying those continuations. *)
                  fun scoped_tuple body =
                    let
                      val slots =
                        map (fn _ =>
                          Free ("_urust_tuple_slot_" ^ string_of_int (serial ()), dummyT))
                          concrete
                      val scoped_body =
                        fold_rev
                          (fn (abstraction, slot) => fn continuation =>
                            Term.betapply (abstraction continuation, slot))
                          (concrete ~~ slots) body
                    in
                      tuple_abstraction (map Term.lambda slots) scoped_body
                    end
                in
                  SOME (if exists has_alias patterns then scoped_tuple
                    else fn body => tuple_abstraction concrete body)
                end
              else NONE
            end
        | direct (Resolved_Alias (binder_sig, inner, at_pos)) =
            if allow_extended then
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
                         (Navigation.with_source [at_pos] (fn () =>
                           T.bind (T.literal matched)
                             (Term.lambda alias_free
                               (Term.betapply
                                 (inner_abstraction body, matched)))))
                   in SOME abstraction end)
            else NONE
        | direct (Resolved_Slice ([Resolved_Slice_Rest rest_pos], pos)) =
            if allow_extended
            then list_abstraction pos (direct (Resolved_Wild rest_pos))
            else NONE
        | direct
            (Resolved_Slice ([Resolved_Slice_Bound_Rest (binder_sig, _, _)], pos)) =
            if allow_extended
            then list_abstraction pos (direct (Resolved_Bind binder_sig))
            else NONE
        | direct (Resolved_Navigated (positions, inner)) =
            Option.map
              (fn abstraction => fn body =>
                Navigation.with_source positions (fn () =>
                  abstraction
                    (Navigation.annotate Navigation.Primary
                      (Const (\<^const_name>\<open>Core_Expression.bind\<close>, dummyT))
                      body)))
              (direct inner)
        | direct _ = NONE
    in direct pattern end

  fun binder_site_description Let_Binder =
        "an irrefutable (let/const) binder position"
    | binder_site_description Let_Const_Binder =
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
      val (resolved, reports) =
        resolve_pattern resolver ctxt policy pattern
      val signatures = collect_bindings resolved
      val rhs_mode =
        (case site of
           Mutable_Let_Binder _ => mutable_source_mode pattern
         | _ => Plain_Rhs)
      val rhs_wrapper =
        (case (site, rhs_mode) of
           (Mutable_Let_Binder mutable_pos, Allocate_Rhs) =>
             (fn rhs =>
               Navigation.with_source_position mutable_pos
                 (fn () => T.allocate_reference mutable_pos rhs))
         | _ => I)
      val allow_extended =
        (case site of
           Let_Binder => true
         | For_Binder => true
         | _ => false)
      val diagnostic_site =
        (case (site, rhs_mode) of
           (Mutable_Let_Binder _, Plain_Rhs) => Let_Const_Binder
         | _ => site)
      (* Reject refutable binding shapes before allocating or reporting their local identities. *)
      val _ =
        if directly_irrefutable allow_extended resolved then ()
        else
          error ("urust_expr: unsupported or refutable pattern in " ^
            binder_site_description diagnostic_site ^
            Position.here (resolved_position resolved))
      val environment' =
        R.allocate_locals ctxt environment signatures
      (* A directly irrefutable pattern always has a direct abstraction. Building it reports the
         pattern's wildcards before the deferred semantic reports below. *)
      val abstraction =
        (case direct_abstraction ctxt true allow_extended environment' resolved of
           SOME abstraction => abstraction
         | NONE =>
             error ("urust_expr: internal irrefutable pattern without a direct abstraction" ^
               Position.here (resolved_position resolved)))
      val _ = emit_semantic_reports reports
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
     | P_Literal (payload as LP_Integer _) =>
         [T.option_some
           (lower_literal_value ctxt R.empty_environment payload)]
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

  fun prepare_switch_arm ctxt (UR_Arm (pattern, guard, body, _)) =
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

  (* A Case_Node head is used exactly as given: R.constructor_term of a resolved constructor (it
     can be a type-instantiated Const shared with the typing witness) or a list constructor of a
     slice. family_hint is the resolver's family, if any. Tuples stay Case_Tuple at this level. *)
  datatype case_pattern =
      Case_Wild
    | Case_Bind of binding_signature
    | Case_Value of term * Position.T
    | Case_Node of
        {head: term,
         family_hint: (string * term list) option,
         arguments: case_pattern list}
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
        {head: term,
         family_hint: (string * term list) option,
         arguments: clause_pattern list}

  datatype case_pattern_tree =
      Pattern_Slot of int
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
      fun split prefix rest_binding suffix [] =
            (rev prefix, rest_binding, rev suffix)
        | split prefix NONE suffix
            (Resolved_Slice_Rest pos :: rest) =
            split prefix (SOME (NONE, pos)) suffix rest
        | split _ (SOME _) _ (Resolved_Slice_Rest pos :: _) =
            error ("urust_expr: internal duplicate slice rest" ^
              Position.here pos)
        | split prefix NONE suffix
            (Resolved_Slice_Bound_Rest (binder_sig, _, pos) :: rest) =
            split prefix (SOME (SOME binder_sig, pos)) suffix rest
        | split _ (SOME _) _
            (Resolved_Slice_Bound_Rest (_, _, pos) :: _) =
            error ("urust_expr: internal duplicate slice rest" ^
              Position.here pos)
        | split prefix rest_binding suffix
            (Resolved_Slice_Pattern pattern :: rest) =
            if is_some rest_binding
            then split prefix rest_binding (pattern :: suffix) rest
            else split (pattern :: prefix) rest_binding suffix rest
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
                | item_alternatives
                    (rest as Resolved_Slice_Bound_Rest _) = [rest]
            in
              map (fn expanded => Resolved_Slice (expanded, pos))
                (products (map item_alternatives items))
            end
        | expand (Resolved_Navigated (positions, inner)) =
            map
              (fn expanded =>
                Resolved_Navigated (positions, expanded))
              (expand inner)
        | expand source_pattern = [source_pattern]
    in expand pattern end

  fun resolved_value_term ctxt environment value =
    (case value of
       Resolved_Literal_Value payload =>
         T.literal (lower_literal_value ctxt environment payload)
     | Resolved_Identifier_Value identifier =>
         R.literal_identifier ctxt environment identifier
     | Resolved_Path_Value path =>
         R.literal_path ctxt environment path)

  fun report_case_binder ctxt environment binder_sig =
    (case R.use_pattern_binder ctxt environment binder_sig of
       SOME _ => ()
     | NONE =>
         error ("urust_expr: internal unallocated case binder " ^
           quote (signature_name binder_sig) ^
           Position.here (signature_position binder_sig)))

  fun prepare_case_pattern ctxt environment pattern =
    (case pattern of
       Resolved_Wild pos =>
         (R.report_wildcard ctxt pos; Case_Wild)
     | Resolved_Bind binder_sig =>
         (report_case_binder ctxt environment binder_sig;
          Case_Bind binder_sig)
     | Resolved_Value payload =>
         Case_Value
           (lower_literal_value ctxt environment payload,
            literal_position payload)
     | Resolved_Path path =>
         Case_Value
           (R.literal_path_value ctxt environment path,
            path_position path)
     | Resolved_Constructor (info, _, arguments) =>
         Case_Node
           {head = R.constructor_term info,
            family_hint = R.constructor_family info,
            arguments = map (prepare_case_pattern ctxt environment) arguments}
     | Resolved_Tuple (arguments, _) =>
         Case_Tuple
           (map (prepare_case_pattern ctxt environment) arguments)
      | Resolved_Alias (binder_sig, inner, at_pos) =>
          (report_case_binder ctxt environment binder_sig;
           Case_Alias
             (binder_sig, I, prepare_case_pattern ctxt environment inner, at_pos))
     | Resolved_Range (kind, lower, upper, pos) =>
         Case_Range
           (kind,
            resolved_value_term ctxt environment lower,
            resolved_value_term ctxt environment upper,
            pos)
     | Resolved_Slice (items, pos) =>
         let
           val (prefix, rest_binding, suffix) =
             split_resolved_slice_items items
           fun cons_chain patterns tail =
             fold_rev (fn nested => fn rest =>
                 Case_Node
                   {head = T.list_cons_constructor,
                    family_hint = NONE,
                    arguments = [prepare_case_pattern ctxt environment nested, rest]})
               patterns tail
           val nil_pattern =
             Case_Node {head = T.list_nil_constructor, family_hint = NONE, arguments = []}
           (* Open slices count only explicit elements. Suffix matching reverses the remainder;
              reverse its residual middle back before exposing a named capture. *)
           fun rest_tail _ NONE = Case_Wild
             | rest_tail true (SOME binder_sig) =
                 (* The alias captures the restored middle; its inner pattern stays a wildcard.
                    Report the source binder explicitly instead of preparing a discarded binding. *)
                 (report_case_binder ctxt environment binder_sig;
                   Case_Alias
                     (binder_sig, T.reverse_list, Case_Wild,
                      Position.none))
             | rest_tail false (SOME binder_sig) =
                 prepare_case_pattern ctxt environment (Resolved_Bind binder_sig)
         in
           (case rest_binding of
              NONE => cons_chain prefix nil_pattern
            | SOME (binder_sig, _) =>
                if null suffix
                then
                  let val capture = rest_tail false binder_sig
                  in
                    if null prefix
                    then Case_Constraint (HOLogic.listT dummyT, pos, capture)
                    else cons_chain prefix capture
                  end
                else
                  cons_chain prefix
                    (Case_Slice_Suffix
                      (cons_chain (rev suffix) (rest_tail true binder_sig))))
         end
     | Resolved_Navigated (positions, inner) =>
         Case_Navigated
           (positions,
            prepare_case_pattern ctxt environment inner)
     | Resolved_Or (_, pos) =>
         error ("urust_expr: internal unexpanded resolved or-pattern" ^
           Position.here pos))

  fun prepare_case_arm resolver ctxt environment
      (UR_Arm (pattern, guard, body, _)) =
    let
      val (resolved, reports) =
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
      (Prepared_Case_Arm
         {patterns = patterns,
          environment = arm_environment,
          binders = binders,
          guard = guard,
          body = body,
          direct_abstraction = direct,
          total = total},
       reports)
    end

  fun prepare_case_arms ctxt pos environment arms =
    let
      val resolver = R.make_constructor_resolver ctxt pos
      val prepared =
        map (prepare_case_arm resolver ctxt environment) arms
      val _ =
        prepared
        |> maps snd
        |> emit_semantic_reports
    in map fst prepared end

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

  fun tuple_clause [] =
        Clause_Node {head = T.tuple_nil_constructor, family_hint = NONE, arguments = []}
    | tuple_clause (argument :: rest) =
        Clause_Node
          {head = T.pair_constructor,
           family_hint = NONE,
           arguments = [argument, tuple_clause rest]}

  (* The clause form of a case pattern: navigation is dropped and tuples become Pair/TNil chains.
     Values, ranges, slice suffixes, aliases and type constraints have no clause form; normalization
     replaces them by generated tests and scopes first. *)
  fun clause_of_case_pattern pattern =
    (case pattern of
       Case_Wild => Clause_Wild
     | Case_Bind binder_sig => Clause_Binder binder_sig
     | Case_Value (_, pos) =>
         error ("urust_expr: internal unnormalized value pattern" ^
           Position.here pos)
     | Case_Node {head, family_hint, arguments} =>
         Clause_Node
           {head = head,
            family_hint = family_hint,
            arguments = map clause_of_case_pattern arguments}
     | Case_Tuple arguments =>
         tuple_clause (map clause_of_case_pattern arguments)
     | Case_Alias (binder_sig, _, _, _) =>
         error ("urust_expr: internal unnormalized alias pattern" ^
           Position.here (signature_position binder_sig))
     | Case_Constraint (_, pos, _) =>
         error ("urust_expr: internal unnormalized pattern type constraint" ^
           Position.here pos)
     | Case_Range (_, _, _, pos) =>
         error ("urust_expr: internal unnormalized range pattern" ^
           Position.here pos)
     | Case_Slice_Suffix _ =>
         error "urust_expr: internal unnormalized slice suffix pattern"
     | Case_Navigated (_, inner) =>
         clause_of_case_pattern inner)

  fun instantiate_pattern arguments tree =
    (case tree of
       Pattern_Slot index => nth arguments index
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

  fun bind_clause_pattern ctxt environment pattern =
    let
      fun add_slot slot (slots_rev, count) =
        (Pattern_Slot count, (slot :: slots_rev, count + 1))

      fun walk Clause_Wild state = add_slot NONE state
        | walk (Clause_Binder binder_sig) state =
            let
              val name = signature_name binder_sig
              val pos = signature_position binder_sig
            in
              (case R.use_pattern_binder ctxt environment (name, pos) of
                 SOME free => add_slot (SOME free) state
               | NONE =>
                   error ("urust_expr: internal unregistered case binder " ^
                     quote name ^ Position.here pos))
            end
        | walk (Clause_Generated free) state =
            add_slot (SOME free) state
        | walk (Clause_Node {head, arguments, ...}) state =
            let val (trees, state') = fold_map walk arguments state
            in (Pattern_Application (head, trees), state') end

      val (tree, (slots_rev, _)) = walk pattern ([], 0)
    in
      fn body =>
        abstract_slots Case_Term_Backend.case_abstraction
          (rev slots_rev)
          (fn arguments =>
            Case_Term_Backend.case_element
              (instantiate_pattern arguments tree) body)
    end

  fun requires_nested_match pattern =
    (case pattern of
       Case_Value _ => true
     | Case_Alias _ => true
     | Case_Constraint _ => true
     | Case_Range _ => true
     | Case_Slice_Suffix _ => true
     | Case_Navigated (_, inner) => requires_nested_match inner
     | Case_Node {arguments, ...} =>
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

  (* covers_region: the opened shape subsumes the enclosing region, so no
     fallback branch follows it. *)
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
    Opened_Pattern of
      {abstraction: term -> term,
       subject: structural_subject}

  datatype structural_group =
    Structural_Group of
      {pattern: structural_pattern,
       members: decision_row list}

  datatype outer_group_plan =
    Outer_Group_Plan of
      {groups: structural_group list,
       catchall: structural_group option}

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
      Free that the source alternative binds at that point; constructor identity, arity, and complete
      native family order remain explicit in Structural_Node.
    - case_clause owns one structural pattern, its alternative-local generated test, one clause_scope,
      and an optional renderer for direct structural lowering. A clause_scope pairs its scope_kind
      with its closing operation, which binds aliases and recursively extracted nested binders around
      the source guard and body together; a direct scope closes with the identity. The direct
      renderer is derived from the normalized clause pattern and is only selected when every row in
      the matrix has the same structural capability. Both direct and recursive case emission use the
      backend constructors owned by Case_Term_Backend.
    - source_position is stable source order. Each decision_row records its arm and alternative
      index, which preserves the distinction between alternative failure and source-guard failure: a
      generated-test miss advances to the next alternative, while a false source guard advances to
      the next arm.
    - decision_state describes the structural region already selected by enclosing cases. exclusions
      record preceding case clauses that failed in that region. A structural_selection_witness
      certifies recursively that the selected region and subject decomposition conform before binders
      are extracted. Semantic totality never creates this witness: a singleton constructor or tuple
      over Structural_Any is opened to obtain its children. A selection that reuses the enclosing
      region fails back into its input decision state; an opened selection fails into the opened
      region over the witness's subject. Generated-test failure tries the next alternative;
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
               error ("urust_expr: internal unregistered case binder " ^
                 quote name ^ Position.here pos))
        end

      fun convert Clause_Wild = Structural_Any NONE
        | convert (Clause_Binder binder_sig) =
            Structural_Any (SOME (local_free binder_sig))
        | convert (Clause_Generated free) =
            Structural_Any (SOME free)
        | convert (Clause_Node {head, family_hint, arguments}) =
            make_structural_node ctxt head family_hint
              (map convert arguments)
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

  (* Structural totality ignores binders, aliases and type constraints. A value, range or slice
     suffix has no clause form, so clause_of_case_pattern fails on it; try turns that failure, and
     any failure to resolve a constructor head, into false. *)
  fun case_pattern_structurally_total ctxt pattern =
    let
      fun spine (Case_Bind _) = Case_Wild
        | spine (Case_Node {head, family_hint, arguments}) =
            Case_Node
              {head = head, family_hint = family_hint, arguments = map spine arguments}
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
              (Clause_Generated free,
               Structural_Subject {value = free, children = []})
            end
        | open_pattern
            (Structural_Node {head, arguments, ...}) =
            let
              val opened = map open_pattern arguments
              val clauses = map fst opened
              val subjects = map snd opened
              val value =
                Term.list_comb
                  (constructor_term head,
                   map subject_value subjects)
            in
              (Clause_Node
                {head = constructor_term head, family_hint = NONE, arguments = clauses},
               Structural_Subject
                 {value = value, children = subjects})
            end

      val (clause, subject) = open_pattern pattern
    in
      Opened_Pattern
        {abstraction =
           bind_clause_pattern ctxt R.empty_environment clause,
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
       SOME witness => Reused_Clause_Selection witness
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
           Opened_Clause_Selection
             {covers_region =
                structural_semantically_subsumes
                  (shape, region),
              region = shape,
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
    | extend_generated_test generated (SOME prior) =
        SOME (T.binary And prior generated)

  fun alias_wrapper transform environment expression binder_sig rhs =
    let
      val name = signature_name binder_sig
      val pos = signature_position binder_sig
    in
      (case R.lookup_local environment name of
         SOME free => T.bind (transform expression) (Term.lambda free rhs)
       | NONE =>
           error ("urust_expr: internal unregistered alias binder " ^
             quote name ^ Position.here pos))
    end

  fun compile_nested_case compiler ctxt environment expression pattern
      success fallback =
    compiler ctxt expression
      ([(pattern, environment, NONE, success)] @
       (if case_pattern_structurally_total ctxt pattern
        then []
        else
          [(Case_Wild,
            environment, NONE, fallback)]))

  (*
    Slice punctuation denotes the generated list case even when the list pattern
    is nested inside another constructor. Keep this probe in the branch body:
    wrapping case_abs/case_elem itself would make Ctr_Sugar reject the clause.
  *)
  fun slice_navigation_wrapper positions rhs =
    Navigation.with_source positions (fn () =>
      Navigation.probe
        (Navigation.mark Navigation.Primary
          (Const
            (\<^const_name>\<open>List.case_list\<close>,
             dummyT)))
        rhs)

  fun apply_navigation wrappers rhs =
    fold_rev (fn wrapper => fn body => wrapper body)
      wrappers rhs

  fun strip_case_navigation (Case_Navigated (positions, inner)) =
        let
          val (nested, core) = strip_case_navigation inner
        in (positions :: nested, core) end
    | strip_case_navigation pattern = ([], pattern)

  fun normalize_pattern_for_nested compiler ctxt environment pattern =
    let
      fun normalize_arguments [] = ([], [], [], [])
        | normalize_arguments (argument :: rest) =
            let
              val (navigation_positions, bare_argument) =
                strip_case_navigation argument
              val (argument', guards0, wrappers0, navigation0) =
                if requires_nested_match bare_argument
                then
                  let
                    val temporary =
                      Free
                        ("_urust_pat_" ^
                          string_of_int (serial ()), dummyT)
                    val temporary_expression = T.literal temporary
                    val (matched_expression, matched_pattern) =
                      (case bare_argument of
                         Case_Slice_Suffix reversed_suffix =>
                           (T.reverse_list temporary_expression,
                            reversed_suffix)
                       | _ => (temporary_expression, bare_argument))
                    val structurally_total =
                      case_pattern_structurally_total
                        ctxt matched_pattern
                    val guards =
                      if structurally_total
                      then []
                      else
                        [compile_nested_case compiler ctxt environment
                          matched_expression matched_pattern
                          (T.literal T.true_value)
                          (T.literal T.false_value)]
                    fun wrapper rhs =
                      compile_nested_case compiler ctxt environment
                        matched_expression matched_pattern
                        rhs T.undefined_value
                  in
                    (Clause_Generated temporary, guards,
                     [{kind =
                         (case bare_argument of
                            Case_Slice_Suffix _ => Transformed_Scope
                          | _ => Nested_Scope),
                       close = wrapper}],
                     map slice_navigation_wrapper
                       navigation_positions)
                  end
                else
                  normalize_pattern_for_nested
                    compiler ctxt environment argument
              val (rest', guards1, wrappers1, navigation1) =
                normalize_arguments rest
            in
              (argument' :: rest',
               guards0 @ guards1,
               wrappers0 @ wrappers1,
               navigation0 @ navigation1)
            end
      val (navigation_positions, bare_pattern) =
        strip_case_navigation pattern
      val (clause, guards, wrappers, navigation) =
        (case bare_pattern of
           Case_Node {head, family_hint, arguments} =>
             let
               val (arguments', guards, wrappers, navigation) =
                 normalize_arguments arguments
             in
               (Clause_Node
                 {head = head, family_hint = family_hint, arguments = arguments'},
                guards, wrappers, navigation)
             end
         | Case_Tuple arguments =>
             let
               val (arguments', guards, wrappers, navigation) =
                 normalize_arguments arguments
             in
               (tuple_clause arguments', guards,
                wrappers, navigation)
             end
         | _ =>
             (clause_of_case_pattern bare_pattern, [], [], []))
    in
      (clause, guards, wrappers,
       navigation @
         map slice_navigation_wrapper navigation_positions)
    end

  fun normalize_extended_pattern compiler ctxt environment expression pattern =
    let
      val (navigation_positions, bare_pattern) =
        strip_case_navigation pattern
      val (clause, guards, wrappers, navigation) =
        (case bare_pattern of
           Case_Alias (binder_sig, transform, inner, at_pos) =>
             let
               val (clause, guards, wrappers, navigation) =
                 normalize_extended_pattern
                   compiler ctxt environment expression inner
                fun wrap rhs =
                  Navigation.with_source_position at_pos (fn () =>
                    alias_wrapper transform environment expression binder_sig rhs)
             in
               (clause, guards,
                wrappers @ [{kind = Alias_Scope, close = wrap}],
                navigation)
             end
         | Case_Constraint (typ, pos, inner) =>
             let
               val (clause, guards, wrappers, navigation) =
                 normalize_extended_pattern
                   compiler ctxt environment expression inner
               fun wrap rhs =
                 T.bind expression
                   (constrain_pattern_abstraction typ pos
                     (R.anonymous_abstraction rhs))
             in
               (clause, guards, wrappers @ [{kind = Nested_Scope, close = wrap}], navigation)
             end
         | Case_Value (literal, _) =>
             (Clause_Wild,
              [T.binary Eq expression (T.literal literal)],
              [], [])
         | Case_Range (kind, lower, upper, _) =>
             let
               val upper_guard =
                 T.binary
                   (case kind of
                      RK_Exclusive => Lt
                    | RK_Inclusive => Le)
                   expression upper
             in
               (Clause_Wild,
                [T.binary And
                  (T.binary Ge expression lower) upper_guard],
                [], [])
             end
         | Case_Slice_Suffix reversed_suffix =>
             let
               val reversed_expression =
                 T.reverse_list expression
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
               (Clause_Wild, [guard],
                [{kind = Transformed_Scope, close = wrap}], [])
             end
         | _ =>
             normalize_pattern_for_nested
               compiler ctxt environment bare_pattern)
    in
      (clause, guards, wrappers,
       navigation @
         map slice_navigation_wrapper navigation_positions)
    end

  fun normalize_case_alternative compiler ctxt value
      (pattern, environment) =
    let
      val
        (clause_pattern, generated_guards, wrappers, navigation) =
        normalize_extended_pattern
          compiler ctxt environment (T.literal value) pattern
      val generated_test =
        fold extend_generated_test generated_guards NONE
      val scope = combine_scopes wrappers
      val direct_branch =
        try (bind_clause_pattern ctxt environment) clause_pattern
    in
      Case_Clause
        {structural_pattern =
           structural_pattern_of_clause
             ctxt environment clause_pattern,
         generated_test = generated_test,
         scope = scope,
         navigation = navigation,
         direct_branch = direct_branch}
    end

  fun case_term_on subject branches =
    let
      val raw = Case_Term_Backend.make_case
        T.true_value subject branches
      (* Keep clause heads raw for native case translation. The complete
         selector resolves to its datatype case constant before navigation
         erasure; auxiliary case constructors remain secondary targets. *)
    in
      fold_rev
        (fn name => fn body =>
          Navigation.annotate Navigation.Secondary
            (Const (name, dummyT)) body)
        [\<^const_name>\<open>case_nil\<close>,
         \<^const_name>\<open>case_cons\<close>,
         \<^const_name>\<open>case_elem\<close>,
         \<^const_name>\<open>case_abs\<close>,
         \<^const_name>\<open>case_guard\<close>]
        (Navigation.mark Navigation.Primary raw)
    end

  fun generated_wild ctxt rhs =
    bind_clause_pattern ctxt R.empty_environment
      Clause_Wild rhs

  fun outer_clause_pattern
      (Const (name, _) $ Abs (_, _, body)) =
        if name = \<^const_name>\<open>case_abs\<close>
        then outer_clause_pattern body
        else NONE
    | outer_clause_pattern
        (Const (name, _) $ pattern $ _) =
        if name = \<^const_name>\<open>case_elem\<close>
        then SOME pattern
        else NONE
    | outer_clause_pattern _ = NONE

  fun constructor_clause branch =
    (case outer_clause_pattern branch of
       SOME pattern =>
         (case
             Term.head_of
               (Term_Position.strip_positions pattern) of
            Const _ => true
          | _ => false)
     | NONE => false)

  fun direct_structural_branch
      (Decision_Row
        {clause =
           Case_Clause
             {generated_test, scope = {kind, ...}, navigation,
              direct_branch, ...},
         source_guard, body, ...}) =
    (case (source_guard, generated_test, kind, direct_branch) of
       (NONE, NONE, Direct_Scope, SOME render) =>
         SOME (render (apply_navigation navigation body))
     | _ => NONE)

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

  fun row_has_source_guard
      (Decision_Row {source_guard, ...}) =
    is_some source_guard

  fun row_shape row =
    erase_structural_bindings (row_pattern row)

  datatype match_root_decision =
      Structural_Match_Root
    | Conditional_Match_Root
    | Binding_Match_Root

  fun drop_source_arm arm_index rows =
    drop_prefix (fn row => row_arm row = arm_index) rows

  fun row_exclusion row pattern =
    Decision_Exclusion
      {position = row_position row, pattern = pattern}

  fun same_outer_group (left, right) =
    structural_same_shape (left, right) orelse
      (structural_is_total left andalso
       structural_is_total right)

  fun add_group_row row group_pattern [] =
        [Structural_Group {pattern = group_pattern, members = [row]}]
    | add_group_row row group_pattern
        (Structural_Group {pattern, members} :: rest) =
        if same_outer_group (pattern, group_pattern)
        then
          Structural_Group {pattern = pattern, members = members @ [row]} :: rest
        else
          Structural_Group {pattern = pattern, members = members} ::
            add_group_row row group_pattern rest

  fun install_source_catchall row NONE =
        SOME
          (Structural_Group
            {pattern = row_pattern row,
             members = [row]})
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
                  members = [row]})
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
          (add_group_row
             row group_pattern groups,
           catchall)
    in
      Outer_Group_Plan
        {groups = groups',
         catchall = catchall'}
    end

  fun transformed_root_tail
      (Decision_Row
        {clause =
           Case_Clause
             {scope = {kind = Transformed_Scope, ...}, ...},
         ...}) = true
    | transformed_root_tail _ = false

  fun prefix_has_structural_group prefix =
    List.exists
      (not o structural_is_any o row_shape) prefix

  fun emission_root_prefix _ prefix [] =
        (rev prefix, false)
    | emission_root_prefix guarded_arm prefix
        (row :: rest) =
        if transformed_root_tail row
        then (rev prefix, true)
        else
          (case guarded_arm of
             SOME active_arm =>
               if row_arm row = active_arm
               then
                 emission_root_prefix guarded_arm
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
                 emission_root_prefix guarded_arm'
                   (row :: prefix) rest
               end)

  fun emission_groups_of
      (Structural_Group {members, ...}) =
    fold
      (fn row => fn groups =>
        add_group_row
          row (row_shape row) groups)
      members []

  fun emission_group_exclusions
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

  fun group_starts_with_generated_test
      (Structural_Group {members, ...}) =
    (case members of
       first :: _ => row_has_generated_test first
     | [] =>
         error
           "urust_expr: internal empty structural group")

  fun group_pattern
      (Structural_Group {pattern, ...}) = pattern

  fun remove_subsumed_emission_groups groups =
    let
      fun covered prior candidate =
        List.exists
          (fn group =>
            group_starts_with_generated_test group andalso
              structural_subsumes
                (group_pattern group,
                 group_pattern candidate))
          prior
      fun retain _ [] = []
        | retain prior (group :: rest) =
            if covered prior group
            then retain prior rest
            else group :: retain (prior @ [group]) rest
    in retain [] groups end

  fun plan_root_suffix context planned_rows =
    let
      val Outer_Group_Plan
        {groups, catchall = source_catchall} =
        fold add_root_group planned_rows
          (Outer_Group_Plan
            {groups = [], catchall = NONE})
      fun group_is_coverage_complete
          (Structural_Group {pattern, members, ...}) =
        structural_is_total pattern andalso
          List.exists
            (structural_is_total o row_shape)
            members
      val coverage_complete_group =
        (case groups of
           [group] =>
             if group_is_coverage_complete group
             then SOME group
             else NONE
         | _ => NONE)
      (*
        A single structurally total group containing a total source row is coverage-complete.
        Root emission must open that planned group directly instead of reconstructing
        a redundant root tail. This rule depends only on typed
        structural coverage, not on any particular constructor or tuple shape.
      *)
      val (prefix_rows,
           reconstruct_root_tail) =
        (case coverage_complete_group of
           SOME _ => (planned_rows, false)
         | NONE =>
             (case context of
                Match_Root =>
                  emission_root_prefix
                    NONE [] planned_rows
              | Failure_Root =>
                  ([], not (null planned_rows))))
      val emission_groups =
        remove_subsumed_emission_groups
          (case coverage_complete_group of
             SOME group =>
               [group]
           | NONE =>
               if reconstruct_root_tail
               then
                 fold
                   (fn row => fn planned_groups =>
                     if structural_is_any (row_shape row)
                     then planned_groups
                     else
                       add_group_row
                         row (row_shape row)
                         planned_groups)
                   prefix_rows []
               else maps emission_groups_of groups)
      val emission_patterns =
        map
          (fn Structural_Group {pattern, ...} =>
            pattern)
          emission_groups
      val emission_exclusions =
        maps emission_group_exclusions
          emission_groups
      val emission_catchall =
        if reconstruct_root_tail
        then
          if patterns_cover_all emission_patterns
          then NONE
          else
            SOME
              (the_default
                (Structural_Group
                  {pattern = Structural_Any NONE,
                   members = []})
                source_catchall)
        else
          (case source_catchall of
             NONE => NONE
           | SOME group =>
               if patterns_cover_all emission_patterns
               then NONE
               else SOME group)
    in
      Root_Suffix_Plan
        {rows = planned_rows,
         groups = emission_groups,
         outer_catchall = emission_catchall,
         catchall_exclusions = emission_exclusions}
    end

  fun following_group_exclusion
      (Structural_Group {members, ...}) =
    (case members of
       [] =>
         error
           "urust_expr: internal empty structural group"
     | first :: _ =>
         if row_has_generated_test first
         then NONE
         else
           SOME
             (row_exclusion first (row_shape first)))

  fun nested_failure_scope
      (Decision_Row
        {clause =
           Case_Clause
             {scope = {kind = Nested_Scope, ...},
              generated_test = SOME _, ...},
         ...}) = true
    | nested_failure_scope _ = false

  fun rows_after_position _ [] =
        error
          "urust_expr: internal missing suffix row"
    | rows_after_position position (row :: rest) =
        if position = row_position row
        then rest
        else rows_after_position position rest

  fun nested_failure_suffix planned_rows
      (Structural_Group {members, ...}) =
    (case members of
       first :: _ =>
         if nested_failure_scope first
         then
           SOME
             (rows_after_position
               (row_position first) planned_rows)
         else NONE
     | [] =>
         error
           "urust_expr: internal empty structural group")

  fun exclusion_position
      (Decision_Exclusion {position, ...}) = position

  fun exclusion_pattern
      (Decision_Exclusion {pattern, ...}) = pattern

  fun excluded_region exclusions position region =
    List.exists
      (fn exclusion =>
        exclusion_position exclusion = position andalso
          structural_semantically_subsumes
            (exclusion_pattern exclusion, region))
      exclusions

  fun row_intersection
      (Decision_State {region, exclusions, ...}) row =
    (case structural_intersection
        (region, row_shape row) of
       NONE => false
     | SOME matched =>
         not (excluded_region exclusions
           (row_position row) matched))

  fun first_applicable _ [] = NONE
    | first_applicable state (row :: rest) =
        if row_intersection state row
        then SOME (row, rest)
        else first_applicable state rest

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

  fun close_selected_clause
      (Case_Clause
        {generated_test, scope, navigation, ...})
      selection source_guard body
      alternative_failure arm_failure =
    let
      val specialize =
        specialize_term (structural_bindings selection)
      val navigated_body =
        apply_navigation navigation body
      val guarded_body =
        (case source_guard of
           NONE => navigated_body
         | SOME (guard, guard_pos) =>
             Navigation.with_source_position guard_pos
               (fn () =>
                 T.conditional guard navigated_body (the arm_failure)))
      val scoped_body =
        specialize (#close scope guarded_body)
    in
      (case generated_test of
         NONE => scoped_body
       | SOME test =>
           T.conditional (specialize test) scoped_body (the alternative_failure))
    end

  fun retain_witness witness body =
    Abs ("_urust_pattern_type_probe_" ^ string_of_int (serial ()),
      dummyT, Term.incr_boundvars 1 body) $ witness

  fun compile_pattern_case ctxt scrutinee arms =
        compile_decision_case Ordinary_Case_Compilation
          [] ctxt [] NONE scrutinee
          (map
            (fn (pattern, environment, source_guard, body) =>
              {patterns = [pattern],
               environment = environment,
               source_guard = source_guard,
               body = body})
            arms)

  and compile_decision_case compilation_mode typing_arms ctxt source_positions
      explicit_fallback scrutinee source_arms =
    let
      val value =
        Free
          ("_urust_case_value_" ^
            string_of_int (serial ()), dummyT)

      val terminal_fallback =
        the_default T.undefined_value explicit_fallback

      (*
        Generated value/range tests also create root-subject selectors, but
        wildcard-only clauses type-check directly to their branch body. Scope
        the match token only over genuine constructor selectors so those
        generated operations cannot become match navigation targets.
      *)
      fun selector_of [] = terminal_fallback
        | selector_of branches =
            if List.exists constructor_clause branches
            then
              Navigation.with_source source_positions (fn () =>
                case_term_on value branches)
            else case_term_on value branches

      val source_arms_with_fallback =
        source_arms @
          (case explicit_fallback of
             NONE => []
           | SOME body =>
               [{patterns = [Case_Wild],
                 environment = R.empty_environment,
                 source_guard = NONE,
                 body = body}])

      (* One row per source alternative, arm-major and alternative-minor. Each alternative is
         normalized exactly once, left to right. *)
      fun normalize_arm
          (arm_index,
           {patterns, environment, source_guard, body} :
             decision_source_arm) =
        map_index
          (fn (alternative_index, pattern) =>
            Decision_Row
              {position =
                 {arm_index = arm_index,
                  alternative_index = alternative_index},
               clause =
                 normalize_case_alternative
                   compile_pattern_case ctxt value
                   (pattern, environment),
               source_guard = source_guard,
               body = body})
          patterns

      val rows =
        flat (map_index normalize_arm source_arms_with_fallback)

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
           subject =
             Structural_Subject
               {value = value, children = []},
           exclusions = []}

      val match_root_decision =
        (case compilation_mode of
           Ordinary_Case_Compilation => NONE
         | Source_Match_Compilation =>
             SOME
               (if List.exists
                    (not o structural_is_any o row_shape) rows
                then Structural_Match_Root
                else if List.exists
                    (fn row =>
                      row_has_generated_test row orelse
                      row_has_source_guard row)
                    rows
                then Conditional_Match_Root
                else Binding_Match_Root))

      fun compile_rows state remaining =
        (case first_applicable state remaining of
           NONE => terminal_fallback
         | SOME
             (Decision_Row
                {clause =
                   (clause as
                     Case_Clause
                       {structural_pattern, generated_test,
                        scope, ...}),
                 source_guard, body,
                 position =
                   (position as {arm_index, ...})},
              rest) =>
             let
               val shape =
                 erase_structural_bindings structural_pattern

               fun compile_matched selection failure_state =
                 let
                   (* A generated-test miss tries the next alternative. A false
                      source guard skips the entire source arm. Choose the one
                      emitted destination before closing the clause; an absent
                      test or guard constructs no failure term. *)
                   val alternative_failure =
                     Option.map
                       (fn _ =>
                         (case #kind scope of
                            Nested_Scope =>
                              compile_root_suffix Failure_Root rest
                          | Transformed_Scope =>
                              compile_root_suffix Failure_Root rest
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
                   close_selected_clause clause
                     selection source_guard body
                     alternative_failure arm_failure
                 end
               val Decision_State {subject, exclusions, ...} = state
             in
               (case select_structural_clause ctxt
                   structural_pattern state of
                  Reused_Clause_Selection witness =>
                    compile_matched witness state
                | Opened_Clause_Selection
                    {covers_region, region, abstraction, witness} =>
                    let
                      val success =
                        compile_matched witness
                          (Decision_State
                            {region = region,
                             subject = selection_subject witness,
                             exclusions = exclusions})
                      val failure =
                        if covers_region then []
                        else
                          [compile_rows
                            (add_exclusion state position shape) rest]
                    in
                      case_term_on (subject_value subject)
                        (abstraction success :: map (generated_wild ctxt) failure)
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
          abstraction compiled
        end

      and compile_outer_group planned_rows exclusions
          (Structural_Group {pattern, ...}) =
        compile_outer_pattern planned_rows exclusions pattern

      and compile_outer_catchall planned_rows exclusions
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
               generated_wild ctxt (compile_rows state planned_rows)
             end
         | Structural_Any (SOME _) =>
             compile_outer_pattern planned_rows exclusions pattern
         | Structural_Node _ =>
             error
               "urust_expr: internal non-wild outer catchall")

      and compile_reconstructed_branch
          (Structural_Group {pattern, ...}) remaining =
        let
          val Opened_Pattern {abstraction, ...} =
            fresh_pattern_subject ctxt pattern
        in
          abstraction
            (compile_root_suffix Failure_Root remaining)
        end

      and compile_emission_groups
          _ [] _ root_suffix =
            ([], root_suffix)
        | compile_emission_groups
            planned_rows (group :: rest)
            exclusions root_suffix =
            let
              val branch =
                (case root_suffix of
                   SOME remaining =>
                     compile_reconstructed_branch
                       group remaining
                 | NONE =>
                     compile_outer_group planned_rows exclusions group)
              val exclusions' =
                (case root_suffix of
                   SOME _ => exclusions
                 | NONE =>
                     (case following_group_exclusion group of
                        NONE => exclusions
                      | SOME exclusion =>
                          exclusion :: exclusions))
              val root_suffix' =
                (case root_suffix of
                   SOME _ => root_suffix
                 | NONE =>
                     nested_failure_suffix
                       planned_rows group)
              val (following, final_root_suffix) =
                compile_emission_groups
                  planned_rows rest exclusions'
                  root_suffix'
            in
              (branch :: following,
               final_root_suffix)
            end

      and emit_root_suffix
          (Root_Suffix_Plan
            {rows = planned_rows, groups,
             outer_catchall, catchall_exclusions}) =
        let
          val (group_branches, root_suffix) =
            compile_emission_groups
              planned_rows groups [] NONE
          val branches =
            group_branches @
              (case outer_catchall of
                 NONE => []
               | SOME group =>
                   [(case root_suffix of
                       SOME remaining =>
                         compile_reconstructed_branch
                           group remaining
                     | NONE =>
                         compile_outer_catchall planned_rows
                           catchall_exclusions group)])
        in selector_of branches end

      and compile_root_suffix context remaining =
        emit_root_suffix (plan_root_suffix context remaining)

      val selector =
        (case direct_structural_matrix () of
           SOME branches => selector_of branches
         | NONE =>
             emit_root_suffix
               (plan_root_suffix Match_Root rows))
      val navigated_selector =
        (case match_root_decision of
           SOME Conditional_Match_Root =>
             Navigation.with_source source_positions (fn () =>
               Navigation.annotate Navigation.Primary
                 (Const
                   (\<^const_name>\<open>two_armed_conditional\<close>,
                    dummyT))
                 selector)
         | SOME Binding_Match_Root =>
             Navigation.with_source source_positions (fn () =>
               Navigation.annotate Navigation.Primary
                 (Const
                   (\<^const_name>\<open>Core_Expression.bind\<close>,
                    dummyT))
                 selector)
         | _ => selector)
      (* Reachability can discard an arm or alternative before the completed term is checked.
         Retain independent pattern-only typing witnesses for every source pattern.
         They use the selected value, never the source scrutinee, guard, or body. A late native
         term-check phase removes these unused beta redexes after all witnesses are inferred.
         Canonical captures share one result type per source arm, including unused binders.
         Internal matcher calls receive no typing arms, preventing recursive witness generation. *)
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

  fun compile_case compilation_mode ctxt source_positions
      explicit_fallback scrutinee arms =
    let
      fun source_arm
          (Prepared_Case_Arm
            {patterns, environment, ...},
           source_guard, body) =
        {patterns = patterns,
         environment = environment,
         source_guard = source_guard,
         body = body}
      fun typing_arm
          (Prepared_Case_Arm {patterns, environment, binders, ...}, _, _) =
        (patterns, environment, binders)
    in
      compile_decision_case compilation_mode (map typing_arm arms) ctxt source_positions
        explicit_fallback scrutinee
        (map source_arm arms)
    end

  fun is_typing_witness
      (Abs (name, _, body) $
        (Const (bind_name, _) $ _ $ Abs (value_name, _, _))) =
        String.isPrefix "_urust_pattern_type_probe_" name andalso
        String.isPrefix "_urust_case_value_" value_name andalso
        bind_name = \<^const_name>\<open>Core_Expression.bind\<close> andalso
        not (Term.loose_bvar1 (body, 0))
    | is_typing_witness _ = false

  fun erase_typing_witnesses
      (term as Abs (name, typ, body) $ witness) =
        if is_typing_witness term
        then erase_typing_witnesses (Term.betapply (Abs (name, typ, body), witness))
        else erase_typing_witnesses (Abs (name, typ, body)) $
          erase_typing_witnesses witness
    | erase_typing_witnesses (function $ argument) =
        erase_typing_witnesses function $ erase_typing_witnesses argument
    | erase_typing_witnesses (Abs (name, typ, body)) =
        Abs (name, typ, erase_typing_witnesses body)
    | erase_typing_witnesses atomic = atomic

  val _ = Context.>>
    (Syntax_Phases.term_check 99 "urust_pattern_typing"
      (fn _ => map (fn term =>
        if Term.exists_subterm
          is_typing_witness term
        then erase_typing_witnesses term else term)))
end
\<close>

end
