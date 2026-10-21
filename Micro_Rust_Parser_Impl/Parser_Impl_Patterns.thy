theory Parser_Impl_Patterns
  imports Parser_Impl_Case_Compiler
begin

section\<open> Pattern resolution and case-arm preparation \<close>

ML\<open>
signature URUST_PATTERNS =
sig
  type prepared_binding
  type prepared_closure_formals
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
  val binding_environment: prepared_binding -> URust_Resolution.environment
  val binding_abstraction: prepared_binding -> term -> term
  val bind_prepared: prepared_binding -> term -> term -> term

  val prepare_closure_formals:
    Proof.context ->
      URust_Resolution.environment ->
      URust_AST.ur_pat list ->
      prepared_closure_formals
  val closure_formals_environment: prepared_closure_formals -> URust_Resolution.environment
  val closure_formal_abstractions: prepared_closure_formals -> (term -> term) list
  val destructure_closure_formals: prepared_closure_formals -> term -> term

  val select_match_flavour:
    Proof.context ->
      URust_AST.match_flavour ->
      URust_AST.ur_arm list ->
      Position.T ->
      URust_AST.match_flavour

  val prepare_switch_arm: Proof.context -> URust_AST.ur_arm -> term list * URust_AST.ur_expr

  val prepare_case_arms:
    Proof.context ->
      Position.T ->
      URust_Resolution.environment ->
      URust_AST.ur_arm list ->
      prepared_case_arm list
  val prepared_environment: prepared_case_arm -> URust_Resolution.environment
  val prepared_guard: prepared_case_arm -> (URust_AST.ur_expr * Position.T) option
  val prepared_body: prepared_case_arm -> URust_AST.ur_expr
  val prepared_direct_abstraction: prepared_case_arm -> (term -> term) option
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
Constructor identities are resolved before any binder is allocated, the complete binder set of a
pattern is validated before allocation, and all alternatives of one source or-pattern share one
environment. The case compiler consumes only prepared arms; it does not resolve or classify source
patterns again.
\<close>

ML\<open>
(*
  URust_Patterns elaborates URust_AST patterns for recursive expression translation. It owns
  use-site validation, binder-versus-constructor decisions, pattern-local environment allocation,
  bare-match classification, switch-key preparation and conservative coverage; it hands prepared
  case arms to URust_Case_Compiler, which compiles them to shallow case terms. URust_AST owns the
  source representation, URust_Resolution the name and constructor metadata, URust_Shallow_Terms
  the shallow-term vocabulary, and URust_Translate the recursive lowering of expressions, guards
  and bodies.

  Pipeline of a case match. Stages 1-5 run in prepare_case_arms, once per source arm and in arm
  order; stages 6-10 run in URust_Case_Compiler.compile_case, except the typing-witness erasure of
  stage 10, which runs in its stage-99 term-check phase urust_pattern_typing. The module comment of
  URust_Case_Compiler describes these stages and tabulates the root rules.

  1. Resolve. resolve_pattern maps each identifier to a constructor or a binder and each path to
     a constructor or a value, under the site's resolution policy; it checks constructor arities,
     rejects unknown constructors and unsupported forms, and defers the constructor, struct and
     field reports. Case patterns treat a reference pattern as a wrapper around its inner pattern.
     One constructor resolver serves every arm of a match.
  2. Validate binders. collect_bindings rejects duplicate binders and or-alternatives that bind
     different names, before any binder is allocated.
  3. Allocate. R.allocate_locals allocates the arm's binders once; every alternative of the arm
     shares that environment.
  4. Expand. expand_resolved_pattern multiplies out nested or-patterns into the arm's
     alternatives, in source order with the leftmost or-pattern varying slowest.
  5. Case patterns. prepare_case_pattern turns each alternative into a case_pattern: it reports
     wildcards and binders, lowers literal values, takes constructor heads from
     R.constructor_term, and encodes slices as list constructor chains, slice suffixes and list
     type constraints. The arm also records its binder Frees, its direct abstraction and its
     conservative totality. The deferred reports of every arm are emitted once all arms are
     prepared.
  The caller then lowers each guard and body in its arm's environment, and compile_case passes the
  arms on for 6. clauses, 7. decision rows, 8. the root plan, 9. emission and 10. typing
  witnesses.

  A binding site runs a shorter pipeline in prepare_binding: reference patterns are rejected; the
  pattern is resolved and its binders validated; a mutable binding's head form and the pattern's
  irrefutability are checked; the binders are allocated; and the direct abstraction is built,
  reporting wildcards, before the deferred reports are emitted.

  The public binder_site constructors select the contract enforced by prepare_binding:
  Let_Binder admits directly irrefutable patterns, including recursive aliases and rest-only
  slices; Let_Const_Binder admits only identifiers, wildcards and non-empty tuples built from them;
  Mutable_Let_Binder additionally restricts the source head to an identifier, wildcard or
  top-level tuple and carries the mutable keyword position; and For_Binder resolves known
  constructors before enforcing irrefutability while admitting the same aliases and rest-only
  slices as Let_Binder. prepare_binding returns an abstract prepared_binding.
  binding_environment is the exact environment in which the caller must lower the binding body.
  binding_abstraction closes such a lowered body over the matched RHS for consumers such as
  `for`. bind_prepared takes an already-lowered outer-scope RHS and inner-scope body, performs any
  mutable scalar/wildcard allocation selected during preparation, and constructs the shallow bind.
  The caller lowers both expressions in those environments.

  prepare_closure_formals prepares one closure formal list under the For_Binder contract: known
  constructors are resolved before binder classification, as Rust resolves every parameter
  pattern, and the same aliases and rest-only slices as Let_Binder are admitted. Every formal is
  resolved and its own binders are validated; then a binder repeated anywhere in the list is
  rejected, as Rust does for one parameter list (E0415); only then must each formal be directly
  irrefutable. The binders of all formals are allocated together after these checks.
  closure_formals_environment is the environment in which the caller must lower the closure body.
  closure_formal_abstractions returns one source-ordered value abstraction per formal. An identifier
  or `_` formal abstracts its own binder or an anonymous binder, exactly as an identifier-only
  closure did. Every other formal abstracts a fresh value slot, and destructure_closure_formals binds
  each such slot inside the closure body exactly as `let PATTERN = slot;` would, first formal
  outermost. The caller wraps the destructured body in FunctionBody before applying the
  abstractions. Function parameters still accept only identifiers and `_`; their first pattern form
  should reuse this entry point.

  select_match_flavour keeps an explicit MF_Case or MF_Switch (rejecting switch guards) and
  resolves MF_Auto with classify_match; it never returns MF_Auto. The auto query is contextual only
  for exact literal registrations: authentic registered constructors are case-only, registered
  nonconstructors support both lowerings, switch wins when every arm is binder-free, guard-free
  and value/wildcard compatible, and any guard forces case. Every arm and or-alternative is
  classified before the guard test, because classification can raise errors. This is not general
  type-directed matching. prepare_switch_arm accepts an unguarded numeral/wildcard/registered-value
  pattern or an or-pattern composed from those forms, preserves alternative order, and returns the
  encoded option keys (Some value or None wildcard) with the unchanged source body for lowering in
  the outer environment.

  prepare_case_arms returns source-ordered abstract prepared_case_arm values. prepared_environment
  is the environment in which both prepared_guard and prepared_body must be lowered.
  prepared_direct_abstraction is SOME only when the complete pattern can bind a scrutinee directly
  without case compilation. prepared_is_total is a conservative certificate that the supported
  coverage analysis found the arm total; false means partial or unknown, not necessarily
  non-total.

  compile_case takes a compilation mode, the source positions that scope navigation, an optional
  explicit fallback, the scrutinee, and source-ordered triples of a prepared_case_arm, its lowered
  optional guard and its lowered body, each lowered in that arm's prepared_environment. The result
  evaluates the scrutinee once, tries arms and or-alternatives in source order, and binds pattern
  variables before guards and bodies run. A failed generated test continues with the next
  alternative and a false guard with the next arm. With NONE an unmatched value gives undefined;
  SOME term appends a final wildcard row with that term and also uses it as the terminal result.
  Parser_Matcher_Stability_Tests fixes the term shape. Ordinary_Case_Compilation, used by
  `if let`, `while let`, `let ... else` and `matches!`, gives the source positions only to case
  selectors that have a constructor clause. Source_Match_Compilation, used by `match`, also gives a
  match whose rows all have wild shapes an explicit navigation target, without placing generated
  comparison predicates under the match keyword. compile_case converts each triple into a
  URust_Case_Compiler.case_arm and delegates to URust_Case_Compiler.compile_case.

  The representations of prepared_binding and prepared_case_arm are abstract. Pattern-position
  inspection, resolution policies, the resolved pattern datatypes, or-pattern expansion,
  generated names, the exact coverage representation, and everything inside URust_Case_Compiler
  (case and clause patterns, normalization and the decision compiler) are implementation details.
  Callers may rely only on the signature and the scoping, ordering, validation, fallback and
  term-shape contracts above.
*)
structure URust_Patterns :> URUST_PATTERNS =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure R = URust_Resolution
  structure Navigation = Micro_Rust_Semantic_Navigation

  datatype case_compilation_mode = datatype URust_Case_Compiler.case_compilation_mode

  val word_type_name =
    (case \<^typ>\<open>64 word\<close> of
       Type (name, _) => name
     | _ => error "urust_expr: internal word type is not a type constructor")

  fun literal_positions payload =
    (case payload of
       LP_Integer integer => [integer_literal_numeric_position integer]
     | LP_Bool (_, pos) => [pos]
     | LP_String (_, pos) => [pos]
     | LP_ValAntiq antiquotation =>
         source_tokens (value_antiquotation_source_layout antiquotation) |> map #2)

  fun lower_literal_value ctxt environment payload =
    let
      val _ =
        (case payload of
           LP_Integer integer =>
             Option.app (fn suffix_pos => Navigation.defer_type ctxt suffix_pos word_type_name)
               (integer_literal_suffix_position integer)
         | _ => ())
      fun lower () = R.literal_value ctxt environment payload
    in
      (case literal_positions payload of
         [] => lower ()
       | positions =>
           Navigation.with_source positions (fn () =>
             Navigation.annotate Navigation.Primary
               (Const (\<^const_name>\<open>Core_Expression.literal\<close>, dummyT))
               (lower ())))
    end

  type binding_signature = URust_Case_Compiler.binding_signature

  val signature_name = URust_Case_Compiler.signature_name
  val signature_position = URust_Case_Compiler.signature_position

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
    | position (P_Borrow (_, _, layout)) = the_source_token_position layout Operator_Token
    | position (P_Alias (_, _, _, layout)) = the_source_token_position layout Operator_Token
    | position (P_Range (_, _, _, layout)) = the_source_token_position layout Operator_Token
    | position (P_Slice (_, layout)) = source_span layout
    | position (P_Struct (path, _, _)) = path_position path
    | position (P_Or (_, layout)) = the_source_token_position layout Operator_Token

  fun reject_reference_patterns pattern =
    let
      fun reject (P_Borrow (_, _, layout)) =
            error ("urust_expr: reference patterns are not implemented" ^
              Position.here (the_source_token_position layout Operator_Token))
        | reject (P_Constr (_, arguments, _)) = List.app reject arguments
        | reject (P_Tuple (arguments, _)) = List.app reject arguments
        | reject (P_Group (inner, _)) = reject inner
        | reject (P_Alias (_, _, inner, _)) = reject inner
        | reject (P_Range (_, lower, upper, _)) = (reject lower; reject upper)
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
         | P_Ident identifier => registered_switch_capability (make_single_path identifier)
         | P_Path path => registered_switch_capability path
         | P_Wild _ => true
         | P_Or (alternatives, _) =>
             (* Map before List.all: every alternative is classified, and can raise, even after
                an earlier one is false. *)
             List.all I (map switch_capability alternatives)
         | _ => false)
      (* Classify every arm and every or-alternative before the guard test: constructor resolution
         and literal classification can raise errors. Each List.all only combines results that its
         map has already computed, so no classification is skipped. *)
      val capabilities = map (switch_capability o arm_pattern) arms
    in
      if List.exists (is_some o arm_guard) arms then MF_Case
      else if List.all I capabilities then MF_Switch
      else MF_Case
    end

  fun first_guard_position [] = NONE
    | first_guard_position (UR_Arm (_, SOME (_, pos), _, _) :: _) = SOME pos
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
    | Resolved_Constructor of R.constructor_info * Position.T * resolved_pattern list
    | Resolved_Tuple of resolved_pattern list * Position.T
    | Resolved_Alias of binding_signature * resolved_pattern * Position.T
    | Resolved_Value of literal_payload
    | Resolved_Path of ur_path
    | Resolved_Range of range_kind * resolved_value * resolved_value * Position.T
    | Resolved_Slice of resolved_slice_item list * Position.T
    | Resolved_Navigated of Position.T list * resolved_pattern
    | Resolved_Or of resolved_pattern list * Position.T
  and resolved_slice_item =
      Resolved_Slice_Pattern of resolved_pattern
    | Resolved_Slice_Rest of Position.T
    | Resolved_Slice_Bound_Rest of binding_signature * Position.T * Position.T

  datatype resolved_coverage =
      Coverage_Total
    | Coverage_Family of {name: string, members: term list, covered: term list}
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
    | resolved_position (Resolved_Navigated (_, inner)) = resolved_position inner
    | resolved_position (Resolved_Or (_, pos)) = pos

  fun coverage_is_total Coverage_Total = true
    | coverage_is_total _ = false

  fun family_complete members covered =
    List.all (fn member => List.exists (fn constructor => constructor aconv member) covered)
      members

  fun family_coverage name members covered =
    let
      val covered' = fold (fn constructor => insert (op aconv) constructor) covered []
    in
      if family_complete members covered'
      then Coverage_Total
      else Coverage_Family {name = name, members = members, covered = covered'}
    end

  fun same_coverage_family
      ({name = left_name, members = left_members, covered = _},
       {name = right_name, members = right_members, covered = _}) =
    left_name = right_name andalso eq_list (op aconv) (left_members, right_members)

  fun resolved_coverage pattern =
    let
      fun coverage (Resolved_Wild _) = Coverage_Total
        | coverage (Resolved_Bind _) = Coverage_Total
        | coverage (Resolved_Constructor (info, _, arguments)) =
            if List.all (coverage_is_total o coverage) arguments
            then
              (case R.constructor_family info of
                 SOME (name, members) => family_coverage name members [R.constructor_term info]
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
        | coverage (Resolved_Slice ([Resolved_Slice_Rest _], _)) = Coverage_Total
        | coverage (Resolved_Slice ([Resolved_Slice_Bound_Rest _], _)) = Coverage_Total
        | coverage (Resolved_Slice _) = Coverage_Partial
        | coverage (Resolved_Navigated (_, inner)) = coverage inner
        | coverage (Resolved_Or (alternatives, _)) =
            let
              val alternatives' = map coverage alternatives
              val total = List.exists coverage_is_total alternatives'
              val partial = List.exists (fn Coverage_Partial => true | _ => false) alternatives'
              val families =
                map_filter (fn Coverage_Family family => SOME family | _ => NONE) alternatives'
            in
              if total then Coverage_Total
              else if partial orelse null families
              then Coverage_Partial
              else
                let
                  val first = hd families
                in
                  if List.all (fn family => same_coverage_family (first, family)) (tl families)
                  then family_coverage (#name first) (#members first) (maps #covered families)
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
        error ("urust_expr: constructor " ^ quote name ^ " expects " ^ string_of_int expected ^
          " pattern argument(s), but got " ^ string_of_int actual ^ Position.here pos)
    end

  fun resolve_pattern resolver ctxt policy pattern =
    let
      val pending_reports = Unsynchronized.ref ([]: (unit -> unit) list)
      fun defer report = pending_reports := report :: !pending_reports

      fun resolve source_pattern =
        (case source_pattern of
           P_Wild pos => Resolved_Wild pos
         | P_Ident (name, pos) =>
             (case policy of
                Always_Binder => Resolved_Bind (binding name pos)
              | _ =>
                  (case R.resolve_constructor ctxt resolver (make_single_path (name, pos)) of
                     NONE => Resolved_Bind (binding name pos)
                   | SOME info =>
                       (check_constructor_arity name pos info [];
                        defer (fn () =>
                          R.report_constructor ctxt (make_single_path (name, pos)) info);
                        Resolved_Constructor (info, pos, []))))
         | P_Literal payload => Resolved_Value payload
         | P_Path path =>
             (case R.resolve_constructor ctxt resolver path of
                SOME info =>
                  let
                    val (name, pos) = segment_identifier (final_segment path)
                  in
                    check_constructor_arity name pos info [];
                    defer (fn () => R.report_constructor ctxt path info);
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
                    error ("urust_expr: `" ^ name ^ "` is not a known constructor" ^
                      Position.here pos)
                | SOME info =>
                    (check_constructor_arity name pos info arguments;
                     defer (fn () => R.report_constructor ctxt path info);
                     Resolved_Constructor (info, pos, map resolve arguments)))
             end
         | P_Tuple (arguments, layout) => Resolved_Tuple (map resolve arguments, source_span layout)
         | P_Group (inner, _) => resolve inner
         | P_Borrow (_, inner, _) =>
             (* Binding sites reject every reference pattern before resolution, so only case
                patterns reach this point; they treat the reference as a syntax-only wrapper. *)
             resolve inner
         | P_Alias ("_", pos, _, _) =>
             error ("urust_expr: alias pattern binder cannot be `_`" ^ Position.here pos)
         | P_Alias (name, pos, inner, layout) =>
             Resolved_Alias
               (binding name pos, resolve inner, the_source_token_position layout Operator_Token)
         | P_Range (_, P_Range _, _, layout) =>
             error ("urust_expr: range patterns are non-associative" ^
               Position.here (the_source_token_position layout Operator_Token))
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
                      Resolved_Slice_Bound_Rest (binding name name_pos, alias_pos, rest_pos) ::
                        resolve_items true rest)
                 | resolve_items seen_rest (SI_Pat nested :: rest) =
                     Resolved_Slice_Pattern (resolve nested) :: resolve_items seen_rest rest
               val punctuation_positions =
                 source_token_positions_for layout
                   [Delimiter_Token "[", Operator_Token, Delimiter_Token "..", Delimiter_Token "]"]
             in
               Resolved_Navigated
                 (punctuation_positions,
                  Resolved_Slice (resolve_items false items, source_span layout))
             end
         | P_Struct (path, fields, _) =>
             let
               val pos = #2 (segment_identifier (final_segment path))
             in
               (case R.resolve_struct_pattern ctxt resolver (path, fields) of
                  R.Resolved_Constructor_Struct (info, ordered) =>
                    let
                      val _ = defer (fn () => R.report_struct_constructor ctxt path info)
                      fun resolve_field
                          {selector, field_reference, source_position, pattern, shorthand} =
                        (* Generated Rust fields have their own source identity even at shorthand
                           binders. Native HOL shorthand keeps its binder-only navigation
                           policy. *)
                        (case if shorthand andalso is_none field_reference
                              then NONE else source_position of
                           SOME source_pos =>
                             defer (fn () =>
                               R.report_field ctxt source_pos selector field_reference)
                         | NONE => ();
                         resolve pattern)
                    in
                      Resolved_Constructor (info, pos, map resolve_field ordered)
                    end
                | R.Resolved_Record_Struct (record_name, _) =>
                    error ("urust_expr: HOL record pattern " ^
                      quote (Long_Name.base_name record_name) ^
                      " requires selector-based lowering" ^ Position.here pos))
             end
         | P_Or (alternatives, layout) =>
             Resolved_Or
               (map resolve alternatives, the_source_token_position layout Operator_Token))
    in
      (case policy of
         Resolve_Constructor_Case => ()
       | _ => reject_reference_patterns pattern);
      (resolve pattern, rev (!pending_reports))
    end

  fun emit_semantic_reports reports = List.app (fn report => report ()) reports

  fun duplicate_binder name pos original_pos =
    error ("urust_expr: duplicate pattern binder " ^ quote name ^ Position.here pos ^
      "\nThe original binder is here" ^ Position.here original_pos)

  fun validate_unique signatures =
    let
      fun add binder_sig table =
        let
          val name = signature_name binder_sig
          val pos = signature_position binder_sig
        in
          (case Symtab.lookup table name of
             NONE => Symtab.update (name, binder_sig) table
           | SOME original => duplicate_binder name pos (signature_position original))
        end
      val _ = fold add signatures Symtab.empty
    in signatures end

  fun signature_table signatures =
    Symtab.make (map (fn binder_sig => (signature_name binder_sig, binder_sig)) signatures)

  fun compare_or_alternative or_pos first_signatures alternative_signatures =
    let
      val first = signature_table first_signatures
      val alternative = signature_table alternative_signatures
      fun check_first (name, original) =
        (case Symtab.lookup alternative name of
           NONE =>
             error ("urust_expr: or-pattern alternative is missing binder " ^ quote name ^
               Position.here or_pos ^ "\nThe first alternative binds it here" ^
               Position.here (signature_position original))
         | SOME _ => ())
      fun check_extra (name, current) =
        if Symtab.defined first name then ()
        else
          error ("urust_expr: or-pattern alternative has extra binder " ^ quote name ^
            Position.here (signature_position current))
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
        | collect (Resolved_Tuple (arguments, _)) = validate_unique (maps collect arguments)
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
                  | Resolved_Slice_Bound_Rest (binder_sig, _, _) => [binder_sig]) items)
        | collect (Resolved_Navigated (_, inner)) = collect inner
        | collect (Resolved_Or ([], pos)) =
            error ("urust_expr: internal empty or-pattern" ^ Position.here pos)
        | collect (Resolved_Or (first :: rest, pos)) =
            let
              val first_signatures = collect first
              val rest_signatures = map collect rest
              val _ = List.app (compare_or_alternative pos first_signatures) rest_signatures
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
           error ("urust_expr: internal unallocated pattern binder " ^ quote name ^
             Position.here pos))
    end

  (* The Free is the binder's identity; the abstraction keeps its source spelling. *)
  fun abstract_signature environment binder_sig =
    Term.lambda_name
      (signature_name binder_sig, lookup_signature environment binder_sig)

  fun directly_irrefutable allow_extended pattern =
    let
      fun direct (Resolved_Bind _) = true
        | direct (Resolved_Wild _) = true
        | direct (Resolved_Tuple (patterns, _)) =
            not (null patterns) andalso List.all direct patterns
        | direct (Resolved_Alias (_, inner, _)) = allow_extended andalso direct inner
        | direct (Resolved_Slice ([Resolved_Slice_Rest _], _)) = allow_extended
        | direct (Resolved_Slice ([Resolved_Slice_Bound_Rest _], _)) = allow_extended
        | direct (Resolved_Navigated (_, inner)) = direct inner
        | direct _ = false
    in direct pattern end

  val constrain_pattern_abstraction = URust_Case_Compiler.constrain_pattern_abstraction

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
            SOME (abstract_signature environment binder_sig)
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
                        T.case_product (abstraction (R.anonymous_abstraction body))
                    | tuple_abstraction (abstraction :: rest) body =
                        T.case_product (abstraction (tuple_abstraction rest body))
                    | tuple_abstraction [] _ = error "urust_expr: internal empty tuple pattern"
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
                     val alias_abstraction =
                       abstract_signature environment binder_sig
                     val matched = Free ("_urust_while_let_" ^ string_of_int (serial ()), dummyT)
                     fun abstraction body =
                       Term.lambda matched
                         (Navigation.with_source [at_pos] (fn () =>
                           T.bind (T.literal matched)
                             (alias_abstraction
                               (Term.betapply (inner_abstraction body, matched)))))
                   in SOME abstraction end)
            else NONE
        | direct (Resolved_Slice ([Resolved_Slice_Rest rest_pos], pos)) =
            if allow_extended
            then list_abstraction pos (direct (Resolved_Wild rest_pos))
            else NONE
        | direct (Resolved_Slice ([Resolved_Slice_Bound_Rest (binder_sig, _, _)], pos)) =
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

  fun binder_site_description Let_Binder = "an irrefutable (let/const) binder position"
    | binder_site_description Let_Const_Binder = "an irrefutable (let/const) binder position"
    | binder_site_description (Mutable_Let_Binder _) = "a mutable binding position"
    | binder_site_description For_Binder = "a `for` binder position"

  datatype prepared_binding =
    Prepared_Binding of
      {environment: R.environment, abstraction: term -> term, rhs_wrapper: term -> term}

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
      val resolver = R.make_constructor_resolver ctxt (position pattern)
      val (resolved, reports) = resolve_pattern resolver ctxt policy pattern
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
            binder_site_description diagnostic_site ^ Position.here (resolved_position resolved))
      val environment' = R.allocate_locals ctxt environment signatures
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
        {environment = environment', abstraction = abstraction, rhs_wrapper = rhs_wrapper}
    end

  fun binding_environment (Prepared_Binding {environment, ...}) = environment
  fun binding_abstraction (Prepared_Binding {abstraction, ...}) = abstraction
  fun bind_prepared (Prepared_Binding {abstraction, rhs_wrapper, ...}) rhs body =
    T.bind (rhs_wrapper rhs) (abstraction body)

  datatype prepared_closure_formals =
    Prepared_Closure_Formals of
      {environment: R.environment,
       abstractions: (term -> term) list,
       destructure: term -> term}

  fun prepare_closure_formals ctxt environment formals =
    let
      fun resolve formal =
        let
          val resolver = R.make_constructor_resolver ctxt (position formal)
          val (resolved, reports) =
            resolve_pattern resolver ctxt Resolve_Constructor_Binding formal
        in (resolved, reports, collect_bindings resolved) end
      val resolved_formals = map resolve formals
      (* Rust reports a repeated parameter binder before a refutable parameter pattern. *)
      val signatures = validate_unique (maps #3 resolved_formals)
      (* Reject refutable formals before allocating or reporting any local identity. *)
      val _ =
        List.app
          (fn (resolved, _, _) =>
            if directly_irrefutable true resolved then ()
            else
              error ("urust_expr: unsupported or refutable pattern in a closure formal position" ^
                Position.here (resolved_position resolved)))
          resolved_formals
      val environment' = R.allocate_locals ctxt environment signatures
      fun prepare (resolved, _, _) =
        let
          val abstraction =
            (case direct_abstraction ctxt true true environment' resolved of
               SOME abstraction => abstraction
             | NONE =>
                 error ("urust_expr: internal irrefutable closure formal without a direct" ^
                   " abstraction" ^ Position.here (resolved_position resolved)))
        in
          (case resolved of
             Resolved_Bind _ => (abstraction, I)
           | Resolved_Wild _ => (abstraction, I)
           | _ =>
               let
                 val slot = Free ("_urust_closure_formal_" ^ string_of_int (serial ()), dummyT)
               in
                 (Term.lambda_name ("formal", slot),
                  fn body => T.bind (T.literal slot) (abstraction body))
               end)
        end
      val prepared = map prepare resolved_formals
      val _ = List.app (emit_semantic_reports o #2) resolved_formals
    in
      Prepared_Closure_Formals
        {environment = environment',
         abstractions = map #1 prepared,
         destructure = fn body => fold_rev (fn (_, destructure) => destructure) prepared body}
    end

  fun closure_formals_environment (Prepared_Closure_Formals {environment, ...}) = environment
  fun closure_formal_abstractions (Prepared_Closure_Formals {abstractions, ...}) = abstractions
  fun destructure_closure_formals (Prepared_Closure_Formals {destructure, ...}) = destructure

  fun switch_keys resolver ctxt pattern =
    (case strip_groups pattern of
       P_Or (alternatives, _) => maps (switch_keys resolver ctxt) alternatives
     | P_Literal (payload as LP_Integer _) =>
         [T.option_some (lower_literal_value ctxt R.empty_environment payload)]
     | P_Wild pos => (R.report_wildcard ctxt pos; [T.option_none])
     | P_Path path =>
         (case R.classify_registered_literal ctxt resolver path of
            R.Registered_Value_Literal =>
              [T.option_some (R.literal_path_value ctxt R.empty_environment path)]
          | R.Registered_Constructor_Literal =>
              error ("urust_expr: authentic constructor " ^ quote (render_path path) ^
                " requires case-pattern lowering" ^ Position.here (path_position path))
          | R.Unregistered_Literal =>
              error ("urust_expr: unsupported match_switch key " ^ quote (render_path path) ^
                " (expected an exact registered literal value)" ^
                Position.here (path_position path)))
     | P_Ident (name, pos) =>
         (case R.classify_registered_literal ctxt resolver (make_single_path (name, pos)) of
            R.Unregistered_Literal =>
              error ("urust_expr: unsupported match_switch key " ^ quote name ^
                " (numeral or `_` only; const-id / path keys not yet supported)" ^
                Position.here pos)
          | R.Registered_Value_Literal =>
              [T.option_some (R.literal_identifier_value ctxt R.empty_environment (name, pos))]
          | R.Registered_Constructor_Literal =>
              error ("urust_expr: authentic constructor " ^ quote name ^
                " requires case-pattern lowering" ^ Position.here pos))
     | unsupported =>
         error ("urust_expr: unsupported match_switch pattern" ^
           " (numeral, `_`, or an or-list of those; binding patterns need" ^
           " `match_case`)" ^ Position.here (position unsupported)))

  fun prepare_switch_arm ctxt (UR_Arm (pattern, guard, body, _)) =
    let
      val resolver = R.make_constructor_resolver ctxt (position pattern)
      val _ = reject_reference_patterns pattern
      val _ =
        (case guard of
           NONE => ()
         | SOME (_, pos) =>
             error ("urust_expr: guards are not supported in explicit `match_switch`" ^
               Position.here pos))
    in (switch_keys resolver ctxt pattern, body) end

  datatype case_pattern = datatype URust_Case_Compiler.case_pattern

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
      fun split prefix rest_binding suffix [] = (rev prefix, rest_binding, rev suffix)
        | split prefix NONE suffix (Resolved_Slice_Rest pos :: rest) =
            split prefix (SOME (NONE, pos)) suffix rest
        | split _ (SOME _) _ (Resolved_Slice_Rest pos :: _) =
            error ("urust_expr: internal duplicate slice rest" ^ Position.here pos)
        | split prefix NONE suffix (Resolved_Slice_Bound_Rest (binder_sig, _, pos) :: rest) =
            split prefix (SOME (SOME binder_sig, pos)) suffix rest
        | split _ (SOME _) _ (Resolved_Slice_Bound_Rest (_, _, pos) :: _) =
            error ("urust_expr: internal duplicate slice rest" ^ Position.here pos)
        | split prefix rest_binding suffix (Resolved_Slice_Pattern pattern :: rest) =
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
              maps (fn alternative => map (fn tail => alternative :: tail) tails) alternatives
            end

      fun expand (Resolved_Or (alternatives, _)) = maps expand alternatives
        | expand (Resolved_Constructor (info, pos, arguments)) =
            map (fn expanded => Resolved_Constructor (info, pos, expanded))
              (products (map expand arguments))
        | expand (Resolved_Tuple (arguments, pos)) =
            map (fn expanded => Resolved_Tuple (expanded, pos)) (products (map expand arguments))
        | expand (Resolved_Alias (binder_sig, inner, alias_pos)) =
            map (fn expanded => Resolved_Alias (binder_sig, expanded, alias_pos)) (expand inner)
        | expand (Resolved_Slice (items, pos)) =
            let
              fun item_alternatives (Resolved_Slice_Pattern nested) =
                    map Resolved_Slice_Pattern (expand nested)
                | item_alternatives (Resolved_Slice_Rest rest_pos) = [Resolved_Slice_Rest rest_pos]
                | item_alternatives (rest as Resolved_Slice_Bound_Rest _) = [rest]
            in
              map (fn expanded => Resolved_Slice (expanded, pos))
                (products (map item_alternatives items))
            end
        | expand (Resolved_Navigated (positions, inner)) =
            map (fn expanded => Resolved_Navigated (positions, expanded)) (expand inner)
        | expand source_pattern = [source_pattern]
    in expand pattern end

  fun resolved_value_term ctxt environment value =
    (case value of
       Resolved_Literal_Value payload => T.literal (lower_literal_value ctxt environment payload)
     | Resolved_Identifier_Value identifier => R.literal_identifier ctxt environment identifier
     | Resolved_Path_Value path => R.literal_path ctxt environment path)

  fun report_case_binder ctxt environment binder_sig =
    (case R.use_pattern_binder ctxt environment binder_sig of
       SOME _ => ()
     | NONE =>
         error ("urust_expr: internal unallocated case binder " ^
           quote (signature_name binder_sig) ^ Position.here (signature_position binder_sig)))

  fun prepare_case_pattern ctxt environment pattern =
    (case pattern of
       Resolved_Wild pos => (R.report_wildcard ctxt pos; Case_Wild)
     | Resolved_Bind binder_sig =>
         (report_case_binder ctxt environment binder_sig; Case_Bind binder_sig)
     | Resolved_Value payload =>
         Case_Value (lower_literal_value ctxt environment payload, literal_position payload)
     | Resolved_Path path =>
         Case_Value (R.literal_path_value ctxt environment path, path_position path)
     | Resolved_Constructor (info, _, arguments) =>
         Case_Node
           {head = R.constructor_term info, family_hint = R.constructor_family info,
            arguments = map (prepare_case_pattern ctxt environment) arguments}
     | Resolved_Tuple (arguments, _) =>
         Case_Tuple (map (prepare_case_pattern ctxt environment) arguments)
     | Resolved_Alias (binder_sig, inner, at_pos) =>
         (report_case_binder ctxt environment binder_sig;
          Case_Alias (binder_sig, I, prepare_case_pattern ctxt environment inner, at_pos))
     | Resolved_Range (kind, lower, upper, pos) =>
         Case_Range
           (kind, resolved_value_term ctxt environment lower,
            resolved_value_term ctxt environment upper, pos)
     | Resolved_Slice (items, pos) =>
         let
           val (prefix, rest_binding, suffix) = split_resolved_slice_items items
           fun cons_chain patterns tail =
             fold_rev (fn nested => fn rest =>
                 Case_Node
                   {head = T.list_cons_constructor, family_hint = NONE,
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
                  Case_Alias (binder_sig, T.reverse_list, Case_Wild, Position.none))
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
                    (Case_Slice_Suffix (cons_chain (rev suffix) (rest_tail true binder_sig))))
         end
     | Resolved_Navigated (positions, inner) =>
         Case_Navigated (positions, prepare_case_pattern ctxt environment inner)
     | Resolved_Or (_, pos) =>
         error ("urust_expr: internal unexpanded resolved or-pattern" ^ Position.here pos))

  fun prepare_case_arm resolver ctxt environment (UR_Arm (pattern, guard, body, _)) =
    let
      val (resolved, reports) = resolve_pattern resolver ctxt Resolve_Constructor_Case pattern
      val signatures = collect_bindings resolved
      val arm_environment = R.allocate_locals ctxt environment signatures
      val patterns =
        map (prepare_case_pattern ctxt arm_environment) (expand_resolved_pattern resolved)
      val binders = map (lookup_signature arm_environment) signatures
      val direct = direct_abstraction ctxt false true arm_environment resolved
      val total = coverage_is_total (resolved_coverage resolved)
    in
      (Prepared_Case_Arm
         {patterns = patterns, environment = arm_environment, binders = binders, guard = guard,
          body = body, direct_abstraction = direct, total = total},
       reports)
    end

  fun prepare_case_arms ctxt pos environment arms =
    let
      val resolver = R.make_constructor_resolver ctxt pos
      val prepared = map (prepare_case_arm resolver ctxt environment) arms
      val _ = prepared |> maps snd |> emit_semantic_reports
    in map fst prepared end

  fun prepared_environment (Prepared_Case_Arm {environment, ...}) = environment
  fun prepared_guard (Prepared_Case_Arm {guard, ...}) = guard
  fun prepared_body (Prepared_Case_Arm {body, ...}) = body
  fun prepared_direct_abstraction (Prepared_Case_Arm {direct_abstraction, ...}) =
    direct_abstraction
  fun prepared_is_total (Prepared_Case_Arm {total, ...}) = total

  fun compile_case compilation_mode ctxt source_positions explicit_fallback scrutinee arms =
    let
      fun case_arm (Prepared_Case_Arm {patterns, environment, binders, ...}, source_guard, body)
          : URust_Case_Compiler.case_arm =
        {patterns = patterns, environment = environment, binders = binders,
         source_guard = source_guard, body = body}
    in
      URust_Case_Compiler.compile_case compilation_mode ctxt source_positions explicit_fallback
        scrutinee (map case_arm arms)
    end
end
\<close>

end
