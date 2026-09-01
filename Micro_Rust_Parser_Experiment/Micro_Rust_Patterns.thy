theory Micro_Rust_Patterns
  imports Micro_Rust_Resolution
begin

section\<open> Pattern lowering and case compilation \<close>

ML\<open>
signature URUST_PATTERNS =
sig
  type case_alternative
  type prepared_case_arm
  datatype binder_site =
      Let_Const_Binder
    | For_Binder
    | While_Let_Binder

  val position: URust_AST.ur_pat -> Position.T
  val bind_irrefutable:
    binder_site ->
      Proof.context ->
      URust_Resolution.environment ->
      URust_AST.ur_pat ->
      (term -> term) * URust_Resolution.environment
  val is_while_let_irrefutable:
    Proof.context -> URust_AST.ur_pat -> bool

  val select_match_flavour:
    URust_AST.match_flavour ->
      URust_AST.ur_arm list ->
      Position.T ->
      URust_AST.match_flavour
  val switch_alternatives: URust_AST.ur_pat -> URust_AST.ur_pat list
  val switch_key: Proof.context -> URust_AST.ur_pat -> term

  val case_alternatives: URust_AST.ur_arm list -> case_alternative list
  val prepare_case_arm:
    Proof.context ->
      URust_Resolution.environment ->
      case_alternative ->
      prepared_case_arm
  val prepared_environment:
    prepared_case_arm -> URust_Resolution.environment
  val prepared_guard:
    prepared_case_arm -> (URust_AST.ur_expr * Position.T) option
  val prepared_body: prepared_case_arm -> URust_AST.ur_expr
  val compile_case:
    Proof.context ->
      term ->
      (prepared_case_arm * term option * term) list ->
      term
end
\<close>

text\<open>
This module owns every pattern traversal and the complete Ctr_Sugar case compiler. Source alternatives
are expanded purely, then prepared one at a time so binder allocation, metadata reports, guard
elaboration, and body elaboration retain their existing order. The current repeated resolution and
guarded-case growth are contained here for a later T-26 replacement.
\<close>

ML\<open>
structure URust_Patterns : URUST_PATTERNS =
struct
  open URust_AST
  structure T = URust_Elab_Terms
  structure R = URust_Resolution

  datatype binder_site =
      Let_Const_Binder
    | For_Binder
    | While_Let_Binder

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

  fun strip_groups (P_Group pattern) = strip_groups pattern
    | strip_groups pattern = pattern

  fun strip_case_transparency pattern =
    (case strip_groups pattern of
       P_Borrow (_, inner, _) => strip_case_transparency inner
     | inner => inner)

  fun arm_pattern (UR_Arm (pattern, _, _)) = pattern
  fun arm_guard (UR_Arm (_, guard, _)) = guard

  (* Bare match follows the frontend's syntactic head router. Any guard forces case lowering;
     identifiers and wildcards fit either path, so case lowering wins. *)
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

  fun binder_site_description Let_Const_Binder =
        "an irrefutable (let/const) binder position"
    | binder_site_description For_Binder =
        "a `for` binder position"
    | binder_site_description While_Let_Binder =
        "a `while let` binder position"

  fun bind_irrefutable site ctxt environment pattern =
    (case strip_groups pattern of
       (* A let identifier is always a variable binder. In particular, `let None = ...` must not be
          reclassified as a nullary constructor. *)
       P_Ident binding =>
         let val (free, environment') = R.bind_local ctxt environment binding
         in (fn body => Term.lambda free body, environment') end
     | P_Wild pos =>
         (R.report_wildcard ctxt pos;
          (fn body => R.anonymous_abstraction body, environment))
     | P_Tuple (patterns, _) =>
         let
           val (abstractions, environment') =
             fold_map
               (fn nested => fn nested_environment =>
                 bind_irrefutable site ctxt nested_environment nested)
               patterns environment
           fun tuple_abstraction [abstraction] body =
                 T.case_product (abstraction (R.anonymous_abstraction body))
             | tuple_abstraction (abstraction :: rest) body =
                 T.case_product (abstraction (tuple_abstraction rest body))
             | tuple_abstraction [] _ =
                 error "urust_expr: internal empty tuple pattern"
         in (fn body => tuple_abstraction abstractions body, environment') end
     | P_Borrow (_, inner, _) =>
         (case site of
            While_Let_Binder =>
              bind_irrefutable site ctxt environment inner
          | _ =>
              error ("urust_expr: unsupported or refutable pattern in " ^
                binder_site_description site ^
                Position.here (position pattern)))
     | P_Alias ("_", pos, _, _) =>
         error ("urust_expr: alias pattern binder cannot be `_`" ^
           Position.here pos)
     | P_Alias (name, pos, inner, _) =>
         (case site of
            While_Let_Binder =>
              let
                val matched =
                  Free ("_urust_while_let_" ^ string_of_int (serial ()), dummyT)
                val (alias_free, alias_environment) =
                  R.bind_local ctxt environment (name, pos)
                val (inner_abstraction, environment') =
                  bind_irrefutable site ctxt alias_environment inner
                fun abstraction body =
                  Term.lambda matched
                    (T.bind (T.literal matched)
                      (Term.lambda alias_free
                        (Term.betapply (inner_abstraction body, matched))))
              in (abstraction, environment') end
          | _ =>
              error ("urust_expr: unsupported or refutable pattern in " ^
                binder_site_description site ^
                Position.here (position pattern)))
     | _ =>
         error ("urust_expr: unsupported or refutable pattern in " ^
           binder_site_description site ^
           Position.here (position pattern)))

  fun is_while_let_irrefutable ctxt pattern =
    (case pattern of
       P_Wild _ => true
     | P_Ident (name, _) => is_none (R.resolve_constructor ctxt name)
     | P_Tuple (patterns, _) =>
         List.all (is_while_let_irrefutable ctxt) patterns
     | P_Group inner => is_while_let_irrefutable ctxt inner
     | P_Borrow (_, inner, _) => is_while_let_irrefutable ctxt inner
     | P_Alias (_, _, inner, _) => is_while_let_irrefutable ctxt inner
     | _ => false)

  fun switch_alternatives (P_Or (patterns, _)) =
        maps switch_alternatives patterns
    | switch_alternatives (P_Group pattern) =
        switch_alternatives pattern
    | switch_alternatives pattern = [pattern]

  fun switch_key ctxt pattern =
    (case strip_groups pattern of
       P_Literal (LP_Integer (lexeme, pos)) =>
         T.option_some (T.integer_value pos lexeme)
     | P_Wild pos => (R.report_wildcard ctxt pos; T.option_none)
     | P_Ident (name, pos) =>
         error ("urust_expr: unsupported match_switch key " ^ quote name ^
           " (numeral or `_` only; const-id / path keys not yet supported)" ^
           Position.here pos)
     | unsupported =>
         error ("urust_expr: unsupported match_switch pattern" ^
           " (numeral, `_`, or an or-list of those; binding patterns need" ^
           " `match_case`)" ^ Position.here (position unsupported)))

  datatype basic_case_pattern =
      Basic_Wild of Position.T option
    | Basic_Ident of string * Position.T
    | Basic_Generated of term
    | Basic_Constructor of string * Position.T * basic_case_pattern list
    | Basic_Resolved of term * basic_case_pattern list
    | Basic_Tuple of basic_case_pattern list

  datatype case_pattern =
      Case_Wild of Position.T
    | Case_Ident of string * Position.T
    | Case_Literal of string * Position.T
    | Case_Value of term * Position.T
    | Case_Constructor of string * Position.T * case_pattern list
    | Case_Resolved of term * case_pattern list
    | Case_Tuple of case_pattern list
    | Case_Alias of string * Position.T * case_pattern
    | Case_Range of range_kind * term * term * Position.T
    | Case_Slice_Suffix of case_pattern

  datatype case_pattern_tree =
      Pattern_Constant of term
    | Pattern_Slot of int
    | Pattern_Application of term * case_pattern_tree list

  (* case_guard/case_cons/case_nil/case_elem/case_abs are Ctr_Sugar skeleton markers. The existing
     Case_Translation term-check phase folds them into the datatype's concrete case combinator during
     the one final check_term; this compiler must not construct case_option or case_result directly. *)

  datatype case_alternative =
    Case_Alternative of
      ur_pat * (ur_expr * Position.T) option * ur_expr

  datatype prepared_case_arm =
    Prepared_Case_Arm of
      case_pattern * R.environment * (ur_expr * Position.T) option * ur_expr

  fun split_slice_items items =
    let
      fun split prefix rest_pos suffix [] = (rev prefix, rest_pos, rev suffix)
        | split prefix NONE suffix (SI_Rest pos :: rest) =
            split prefix (SOME pos) suffix rest
        | split _ (SOME _) _ (SI_Rest pos :: _) =
            error ("urust_expr: slice pattern has multiple `..` rest entries" ^
              Position.here pos)
        | split prefix rest_pos suffix (SI_Pat pattern :: rest) =
            if is_some rest_pos
            then split prefix rest_pos (pattern :: suffix) rest
            else split (pattern :: prefix) rest_pos suffix rest
    in split [] NONE [] items end

  (* Abstract mixed named and anonymous slots with the final abstraction indices already known. Named
     source Frees are captured by Term.lambda, which leaves existing Bounds untouched; each anonymous
     Abs binds the loose index 0 in its body. A pre-placed index therefore keeps denoting its slot after
     any number of outer named or anonymous abstractions. *)
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

  (* T-26 boundary: recursive disjunctions still expand through a Cartesian product, in source order. *)
  fun expand_case_pattern pattern =
    let
      fun products [] = [[]]
        | products (alternatives :: rest) =
            let val tails = products rest
            in
              maps (fn alternative =>
                map (fn tail => alternative :: tail) tails) alternatives
            end

      fun expand (P_Or (patterns, _)) = maps expand patterns
        | expand (P_Constr (name, pos, arguments)) =
            map (fn expanded => P_Constr (name, pos, expanded))
              (products (map expand arguments))
        | expand (P_Tuple (arguments, pos)) =
            map (fn expanded => P_Tuple (expanded, pos))
              (products (map expand arguments))
        | expand (P_Group inner) = map P_Group (expand inner)
        | expand (P_Borrow (mode, inner, pos)) =
            map (fn expanded => P_Borrow (mode, expanded, pos)) (expand inner)
        | expand (P_Alias (name, name_pos, inner, alias_pos)) =
            map (fn expanded => P_Alias (name, name_pos, expanded, alias_pos))
              (expand inner)
        | expand (P_Range (kind, lower, upper, pos)) =
            maps (fn expanded_lower =>
              map (fn expanded_upper =>
                P_Range (kind, expanded_lower, expanded_upper, pos))
                (expand upper)) (expand lower)
        | expand (P_Slice (items, pos)) =
            let
              fun item_alternatives (SI_Pat nested) =
                    map SI_Pat (expand nested)
                | item_alternatives (SI_Rest rest_pos) =
                    [SI_Rest rest_pos]
            in
              map (fn expanded => P_Slice (expanded, pos))
                (products (map item_alternatives items))
            end
        | expand (P_Struct (name, name_pos, fields)) =
            let
              fun field_alternatives (SF_Field (field, field_pos, nested)) =
                    map (fn expanded =>
                      SF_Field (field, field_pos, expanded)) (expand nested)
                | field_alternatives (SF_Shorthand field) =
                    [SF_Shorthand field]
                | field_alternatives (SF_Rest rest_pos) =
                    [SF_Rest rest_pos]
            in
              map (fn expanded => P_Struct (name, name_pos, expanded))
                (products (map field_alternatives fields))
            end
        | expand source_pattern = [source_pattern]
    in expand pattern end

  fun case_alternatives arms =
    maps (fn UR_Arm (pattern, guard, body) =>
      map (fn expanded => Case_Alternative (expanded, guard, body))
        (expand_case_pattern pattern)) arms

  (* Each expanded alternative gets independent source binder identities, exactly as in the frontend. *)
  fun bind_case_variables ctxt pattern environment =
    (case strip_case_transparency pattern of
       P_Wild _ => environment
     | P_Literal _ => environment
     | P_Ident (name, pos) =>
         (case R.resolve_constructor ctxt name of
            SOME _ => environment
          | NONE => #2 (R.bind_local ctxt environment (name, pos)))
     | P_Constr (name, pos, arguments) =>
         (case R.resolve_constructor ctxt name of
            NONE =>
              error ("urust_expr: `" ^ name ^ "` is not a known constructor" ^
                Position.here pos)
          | SOME _ => fold (bind_case_variables ctxt) arguments environment)
     | P_Tuple (arguments, _) =>
         fold (bind_case_variables ctxt) arguments environment
     | P_Alias ("_", pos, _, _) =>
         error ("urust_expr: alias pattern binder cannot be `_`" ^
           Position.here pos)
     | P_Alias (name, pos, inner, _) =>
         bind_case_variables ctxt inner
           (#2 (R.bind_local ctxt environment (name, pos)))
     | P_Range _ => environment
     | P_Slice (items, _) =>
         let
           val _ = split_slice_items items
           fun bind_item (SI_Pat nested) nested_environment =
                 bind_case_variables ctxt nested nested_environment
             | bind_item (SI_Rest _) nested_environment =
                 nested_environment
         in fold bind_item items environment end
     | P_Struct (name, pos, fields) =>
         (case R.resolve_struct_pattern ctxt (name, pos, fields) of
            R.Resolved_Constructor_Struct (_, ordered) =>
              fold (fn (_, _, nested) => bind_case_variables ctxt nested)
                ordered environment
          | R.Resolved_Record_Struct (record_name, _) =>
              R.unsupported_record_pattern record_name pos)
     | P_Or (_, pos) =>
         error ("urust_expr: internal unexpanded case or-pattern" ^
           Position.here pos))

  (* Value payloads are elaborated after all source binders for this alternative have been registered. *)
  fun pattern_value_expression ctxt environment pattern =
    (case strip_groups pattern of
       P_Literal payload =>
         T.literal (R.literal_value ctxt environment payload)
     | P_Ident identifier =>
         R.literal_identifier ctxt environment identifier
     | _ =>
         error ("urust_expr: invalid range-pattern endpoint" ^
           Position.here (position pattern)))

  fun prepare_case_pattern ctxt environment pattern =
    (case strip_case_transparency pattern of
       P_Wild pos => Case_Wild pos
     | P_Ident identifier => Case_Ident identifier
     | P_Literal (LP_Integer literal) => Case_Literal literal
     | P_Literal payload =>
         Case_Value
           (R.literal_value ctxt environment payload,
            literal_position payload)
     | P_Constr (name, pos, arguments) =>
         Case_Constructor
           (name, pos, map (prepare_case_pattern ctxt environment) arguments)
     | P_Tuple (arguments, _) =>
         Case_Tuple (map (prepare_case_pattern ctxt environment) arguments)
     | P_Alias (name, pos, inner, _) =>
         Case_Alias (name, pos, prepare_case_pattern ctxt environment inner)
     | P_Range (_, P_Range _, _, pos) =>
         error ("urust_expr: range patterns are non-associative" ^
           Position.here pos)
     | P_Range (kind, lower, upper, pos) =>
         Case_Range
           (kind,
            pattern_value_expression ctxt environment lower,
            pattern_value_expression ctxt environment upper,
            pos)
     | P_Slice (items, _) =>
         let
           val (prefix, rest_pos, suffix) = split_slice_items items
           fun cons_chain patterns tail =
             fold_rev (fn nested => fn rest =>
                 Case_Resolved
                   (T.list_cons_constructor,
                    [prepare_case_pattern ctxt environment nested, rest]))
               patterns tail
           val nil_pattern = Case_Resolved (T.list_nil_constructor, [])
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
     | P_Struct (name, pos, fields) =>
         (case R.resolve_struct_pattern ctxt (name, pos, fields) of
            R.Resolved_Constructor_Struct (constructor, ordered) =>
              let
                val _ = R.report_constructor ctxt pos constructor
                fun prepare_field (selector, field_pos, field_pattern) =
                  (case field_pos of
                     SOME source_pos =>
                       R.report_constructor ctxt source_pos selector
                   | NONE => ();
                   prepare_case_pattern ctxt environment field_pattern)
              in Case_Resolved (constructor, map prepare_field ordered) end
          | R.Resolved_Record_Struct (record_name, _) =>
              R.unsupported_record_pattern record_name pos)
     | P_Or (_, pos) =>
         error ("urust_expr: internal unexpanded case or-pattern" ^
           Position.here pos))

  fun prepare_case_arm ctxt environment
      (Case_Alternative (pattern, guard, body)) =
    let
      val arm_environment = bind_case_variables ctxt pattern environment
      val prepared_pattern =
        prepare_case_pattern ctxt arm_environment pattern
    in Prepared_Case_Arm (prepared_pattern, arm_environment, guard, body) end

  fun prepared_environment
      (Prepared_Case_Arm (_, environment, _, _)) = environment
  fun prepared_guard
      (Prepared_Case_Arm (_, _, guard, _)) = guard
  fun prepared_body
      (Prepared_Case_Arm (_, _, _, body)) = body

  fun normalize_basic_pattern pattern =
    (case pattern of
       Case_Wild pos => Basic_Wild (SOME pos)
     | Case_Ident identifier => Basic_Ident identifier
     | Case_Literal (lexeme, pos) =>
         error ("urust_expr: numeric pattern in match_case: " ^ lexeme ^
           Position.here pos)
     | Case_Value (_, pos) =>
         error ("urust_expr: internal unnormalized value pattern" ^
           Position.here pos)
     | Case_Constructor (name, pos, arguments) =>
         Basic_Constructor
           (name, pos, map normalize_basic_pattern arguments)
     | Case_Resolved (constructor, arguments) =>
         Basic_Resolved (constructor, map normalize_basic_pattern arguments)
     | Case_Tuple arguments =>
         Basic_Tuple (map normalize_basic_pattern arguments)
     | Case_Alias (_, pos, _) =>
         error ("urust_expr: internal unnormalized alias pattern" ^
           Position.here pos)
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

  (* The Ctr_Sugar skeleton abstracts slots in depth-first source order. Named slots reuse the exact
     source Free registered for this alternative; wildcard slots are anonymous. *)
  fun bind_basic_pattern ctxt environment pattern =
    let
      fun add_slot slot (slots_rev, count) =
        (Pattern_Slot count, (slot :: slots_rev, count + 1))

      fun walk (Basic_Wild pos) state =
            (case pos of
               SOME source_pos => R.report_wildcard ctxt source_pos
             | NONE => ();
             add_slot NONE state)
        | walk (Basic_Ident (name, pos)) state =
            (case R.resolve_constructor ctxt name of
               SOME constructor =>
                 (R.report_constructor ctxt pos constructor;
                  (Pattern_Constant constructor, state))
             | NONE =>
                 (case R.lookup_local environment name of
                    SOME free => add_slot (SOME free) state
                  | NONE =>
                      error ("urust_expr: internal unregistered case binder " ^
                        quote name ^ Position.here pos)))
        | walk (Basic_Generated free) state =
            add_slot (SOME free) state
        | walk (Basic_Constructor (name, pos, arguments)) state =
            (case R.resolve_constructor ctxt name of
               NONE =>
                 error ("urust_expr: `" ^ name ^ "` is not a known constructor" ^
                   Position.here pos)
             | SOME constructor =>
                 let
                   val _ = R.report_constructor ctxt pos constructor
                   val (trees, state') = fold_map walk arguments state
                 in (Pattern_Application (constructor, trees), state') end)
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
                        (T.pair_constructor, [argument_tree, rest_tree]),
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

  fun alias_wrapper environment expression name pos rhs =
    (case R.lookup_local environment name of
       SOME free => T.bind expression (Term.lambda free rhs)
     | NONE =>
         error ("urust_expr: internal unregistered alias binder " ^
           quote name ^ Position.here pos))

  fun compile_nested_case compiler ctxt environment expression pattern success fallback =
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
                      Free ("_urust_pat_" ^ string_of_int (serial ()), dummyT)
                    val temporary_expression = T.literal temporary
                    val (matched_expression, matched_pattern) =
                      (case argument of
                         Case_Slice_Suffix reversed_suffix =>
                           (T.reverse_list temporary_expression, reversed_suffix)
                       | _ => (temporary_expression, argument))
                    val guard =
                      compile_nested_case compiler ctxt environment
                        matched_expression matched_pattern
                        (T.literal T.true_value) (T.literal T.false_value)
                    fun wrapper rhs =
                      compile_nested_case compiler ctxt environment
                        matched_expression matched_pattern
                        rhs T.undefined_value
                  in (Basic_Generated temporary, [guard], [wrapper]) end
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
       Case_Constructor (name, pos, arguments) =>
         let
           val (arguments', guards, wrappers) =
             normalize_arguments arguments
         in
           (Basic_Constructor (name, pos, arguments'), guards, wrappers)
         end
     | Case_Resolved (constructor, arguments) =>
         let
           val (arguments', guards, wrappers) =
             normalize_arguments arguments
         in (Basic_Resolved (constructor, arguments'), guards, wrappers) end
     | Case_Tuple arguments =>
         let
           val (arguments', guards, wrappers) =
             normalize_arguments arguments
         in (Basic_Tuple arguments', guards, wrappers) end
     | _ => (normalize_basic_pattern pattern, [], []))
    end

  fun normalize_extended_pattern compiler ctxt environment expression pattern =
    (case pattern of
       Case_Alias (name, pos, inner) =>
         let
           val (basic, guards, wrappers) =
             normalize_extended_pattern
               compiler ctxt environment expression inner
           fun wrap rhs =
             alias_wrapper environment expression name pos rhs
         in (basic, guards, wrappers @ [wrap]) end
     | Case_Value (literal, _) =>
         (Basic_Wild NONE,
          [T.binary Eq expression (T.literal literal)],
          [])
     | Case_Range (kind, lower, upper, _) =>
         let
           val upper_guard =
             T.binary
               (case kind of RK_Exclusive => Lt | RK_Inclusive => Le)
               expression upper
         in
           (Basic_Wild NONE,
            [T.binary And (T.binary Ge expression lower) upper_guard],
            [])
         end
     | Case_Slice_Suffix reversed_suffix =>
         let
           val reversed_expression = T.reverse_list expression
           val guard =
             compile_nested_case compiler ctxt environment
               reversed_expression reversed_suffix
               (T.literal T.true_value) (T.literal T.false_value)
           fun wrap rhs =
             compile_nested_case compiler ctxt environment
               reversed_expression reversed_suffix rhs T.undefined_value
         in (Basic_Wild NONE, [guard], [wrap]) end
     | _ =>
         normalize_pattern_for_nested compiler ctxt environment pattern)

  fun normalize_case_arm compiler ctxt value
      (pattern, environment, source_guard, rhs) =
    let
      val (basic_pattern, generated_guards, wrappers) =
        normalize_extended_pattern
          compiler ctxt environment (T.literal value) pattern
      val abstraction =
        bind_basic_pattern ctxt environment basic_pattern
      val guard = fold extend_guard generated_guards source_guard
      val rhs' =
        fold_rev (fn wrapper => fn body => wrapper body) wrappers rhs
      val wild =
        (case basic_pattern of Basic_Wild _ => true | _ => false)
    in (wild, abstraction, guard, rhs') end

  (* Guarded fall-through intentionally retains the current frontend-shaped tree, including the T-26
     repeated fallback. Nested normalizers receive this recursive compiler as a private callback. *)
  fun compile_pattern_case ctxt scrutinee arms =
    let
      val value =
        Free ("_urust_case_value_" ^ string_of_int (serial ()), dummyT)
      val normalized =
        map (normalize_case_arm compile_pattern_case ctxt value) arms

      fun case_term branches =
        T.case_guard T.true_value value
          (fold_rev T.case_cons branches T.case_nil)

      fun generated_wild rhs =
        bind_basic_pattern ctxt R.empty_environment (Basic_Wild NONE) rhs

      val undefined = T.undefined_value

      fun compile_branches [] =
            error "urust_expr: internal empty case branch list"
        | compile_branches [(wild, abstraction, NONE, rhs)] =
            if wild then rhs else case_term [abstraction rhs]
        | compile_branches [(wild, abstraction, SOME guard, rhs)] =
            let val guarded = T.conditional guard rhs undefined
            in
              if wild then guarded
              else case_term [abstraction guarded, generated_wild undefined]
            end
        | compile_branches
            ((wild, abstraction, guard, rhs) :: rest) =
            let
              val fallback = compile_branches rest
              val rhs' =
                (case guard of
                   SOME condition => T.conditional condition rhs fallback
                 | NONE => rhs)
            in
              if wild then rhs'
              else case_term [abstraction rhs', generated_wild fallback]
            end

      val selector =
        if List.exists (fn (_, _, guard, _) => is_some guard) normalized
        then compile_branches normalized
        else
          case_term
            (map (fn (_, abstraction, _, rhs) => abstraction rhs) normalized)
    in T.bind scrutinee (Term.lambda value selector) end

  fun compile_case ctxt scrutinee arms =
    compile_pattern_case ctxt scrutinee
      (map (fn
          (Prepared_Case_Arm (pattern, environment, _, _),
           source_guard, rhs) =>
            (pattern, environment, source_guard, rhs))
        arms)
end
\<close>

end
