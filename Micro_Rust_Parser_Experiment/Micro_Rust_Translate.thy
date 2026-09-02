theory Micro_Rust_Translate
  imports Micro_Rust_Patterns
begin

section\<open> Expression elaboration \<close>

ML\<open>
signature URUST_TRANSLATE =
sig
  type result
  val make_result: Proof.context -> URust_AST.ur_expr -> result
  val result_term: result -> term
  val legacy_compatible: result -> bool
  val compatibility_diagnostic: result -> string * Position.T
  val linear_nodes: result -> int
  val predicted_legacy_nodes: result -> int
  val maximum_legacy_copies: result -> int
  val mk_closed: Proof.context -> URust_AST.ur_expr -> term
end
\<close>

text\<open>
Expression lowering orchestrates the term, resolution, and pattern layers. Terms remain based on
\<open>dummyT\<close>, and the command performs the single final \<open>Syntax.check_term\<close>.
\<close>

ML\<open>
structure URust_Translate : URUST_TRANSLATE =
struct
  open URust_AST
  structure T = URust_Elab_Terms
  structure R = URust_Resolution
  structure P = URust_Patterns

  val legacy_copy_limit = 256

  type analysis =
    {linear_nodes: int,
     predicted_nodes: int,
     maximum_copies: int,
     maximum_copy_position: Position.T option,
     expansion_overflow: Position.T option}

  datatype lowered =
    Lowered of {term: term, analysis: analysis}

  datatype compatibility =
      Legacy_Compatible
    | Scalable_Only of string * Position.T

  datatype result =
    Result of
      {term: term,
       analysis: analysis,
       compatibility: compatibility}

  fun lowered_term (Lowered {term, ...}) = term
  fun lowered_analysis (Lowered {analysis, ...}) = analysis

  fun saturating_add limit left right =
    if left >= limit orelse right >= limit - left
    then limit
    else left + right

  fun saturating_multiply limit left right =
    if left = 0 orelse right = 0 then 0
    else if left >= limit orelse right >= limit orelse
        left > limit div right
    then limit
    else left * right

  fun first_some [] = NONE
    | first_some (NONE :: rest) = first_some rest
    | first_some (SOME value :: _) = SOME value

  fun largest_copy analyses =
    fold
      (fn analysis => fn (largest, position) =>
        if #maximum_copies analysis > largest
        then
          (#maximum_copies analysis,
           #maximum_copy_position analysis)
        else (largest, position))
      analyses (1, NONE)

  fun make_analysis local_position local_linear local_predicted
      local_copies local_copy_position child_analyses =
    let
      val linear_nodes =
        local_linear +
          fold (fn analysis =>
            Integer.add (#linear_nodes analysis))
            child_analyses 0
      val limit = legacy_copy_limit * linear_nodes + 1
      val predicted_nodes =
        fold (fn analysis => fn total =>
          saturating_add limit total
            (#predicted_nodes analysis))
          child_analyses
          (Int.min (local_predicted, limit))
      val (child_copies, child_copy_position) =
        largest_copy child_analyses
      val (maximum_copies, maximum_copy_position) =
        if local_copies > child_copies
        then (local_copies, local_copy_position)
        else (child_copies, child_copy_position)
      val inherited_overflow =
        first_some (map #expansion_overflow child_analyses)
      val expansion_overflow =
        (case inherited_overflow of
           SOME position => SOME position
         | NONE =>
             if predicted_nodes >
                 legacy_copy_limit * linear_nodes
             then local_position
             else NONE)
    in
      {linear_nodes = linear_nodes,
       predicted_nodes = predicted_nodes,
       maximum_copies = maximum_copies,
       maximum_copy_position = maximum_copy_position,
       expansion_overflow = expansion_overflow}
    end

  fun plain term children =
    Lowered
      {term = term,
       analysis =
         make_analysis NONE 1 1 1 NONE
           (map lowered_analysis children)}

  fun leaf term = plain term []

  fun matcher_case_analysis position scrutinee arms =
    let
      fun arm_children (_, guard, body) =
        lowered_analysis body ::
          (case guard of
             NONE => []
           | SOME lowered_guard =>
               [lowered_analysis lowered_guard])
      val child_analyses =
        lowered_analysis scrutinee ::
          maps arm_children arms
      val pattern_linear =
        fold (fn (prepared, _, _) =>
          Integer.add
            (P.prepared_legacy_linear_nodes prepared))
          arms 0
      val local_linear =
        1 + pattern_linear + length arms
      val total_linear =
        local_linear +
          fold (fn analysis =>
            Integer.add (#linear_nodes analysis))
            child_analyses 0
      val limit = legacy_copy_limit * total_linear + 1

      fun arm_cost (prepared, guard, body) continuation =
        let
          val copies = P.prepared_legacy_copies prepared
          val expanded =
            P.prepared_legacy_expanded_nodes prepared
          val guard_cost =
            (case guard of
               NONE => 0
             | SOME lowered_guard =>
                 #predicted_nodes
                   (lowered_analysis lowered_guard))
          val body_cost =
            #predicted_nodes (lowered_analysis body)
          val own_cost =
            saturating_add limit expanded
              (saturating_multiply limit copies
                (2 + guard_cost + body_cost))
          val continuation_copies =
            saturating_multiply limit copies
              (if is_some guard then 2 else 1)
        in
          saturating_add limit own_cost
            (saturating_multiply limit
              continuation_copies continuation)
        end

      val predicted_case = fold_rev arm_cost arms 1
      val local_predicted =
        saturating_add limit 1 predicted_case

      fun largest_pattern
          (prepared, _, _) (largest, largest_position) =
        let val copies = P.prepared_legacy_copies prepared in
          if copies > largest
          then
            (copies,
             SOME (P.prepared_pattern_position prepared))
          else (largest, largest_position)
        end
      val (pattern_copies, pattern_position) =
        fold largest_pattern arms (1, NONE)
      val (child_copies, child_copy_position) =
        largest_copy child_analyses
      val (maximum_copies, maximum_copy_position) =
        if pattern_copies > child_copies
        then (pattern_copies, pattern_position)
        else (child_copies, child_copy_position)
      val predicted_nodes =
        saturating_add limit local_predicted
          (#predicted_nodes
            (lowered_analysis scrutinee))
      val inherited_overflow =
        first_some
          (map #expansion_overflow child_analyses)
      val expansion_overflow =
        (case inherited_overflow of
           SOME overflow_position =>
             SOME overflow_position
         | NONE =>
             if predicted_nodes >
                 legacy_copy_limit * total_linear
             then SOME position
             else NONE)
    in
      {linear_nodes = total_linear,
       predicted_nodes = predicted_nodes,
       maximum_copies = maximum_copies,
       maximum_copy_position = maximum_copy_position,
       expansion_overflow = expansion_overflow}
    end

  fun classify analysis =
    if #maximum_copies analysis > legacy_copy_limit
    then
      Scalable_Only
        ("legacy frontend expansion would exceed " ^
          string_of_int legacy_copy_limit ^
          " Cartesian pattern copies",
         the_default Position.none
           (#maximum_copy_position analysis))
    else
      (case #expansion_overflow analysis of
         SOME position =>
           Scalable_Only
             ("legacy frontend normalization would exceed " ^
               string_of_int legacy_copy_limit ^
               " times the scalable term's linear size",
              position)
       | NONE => Legacy_Compatible)

  fun result_term (Result {term, ...}) = term
  fun legacy_compatible
      (Result {compatibility = Legacy_Compatible, ...}) = true
    | legacy_compatible _ = false
  fun compatibility_diagnostic
      (Result
        {compatibility = Scalable_Only diagnostic, ...}) =
        diagnostic
    | compatibility_diagnostic _ =
        error
          "urust_expr: internal compatibility diagnostic requested for a legacy-compatible term"
  fun linear_nodes
      (Result {analysis = {linear_nodes, ...}, ...}) =
        linear_nodes
  fun predicted_legacy_nodes
      (Result {analysis = {predicted_nodes, ...}, ...}) =
        predicted_nodes
  fun maximum_legacy_copies
      (Result {analysis = {maximum_copies, ...}, ...}) =
        maximum_copies

  fun lower_place lower ctxt environment place =
    (case place of
       UP_Ident identifier =>
         leaf (R.literal_identifier ctxt environment identifier)
     | UP_Deref (expression, _) =>
         lower environment expression
     | UP_Field (base, name, pos) =>
         let
           val lowered_base =
             lower_place lower ctxt environment base
         in
           plain
             (R.field_expression ctxt
               (lowered_term lowered_base) name pos)
             [lowered_base]
         end
     | UP_Antiq source =>
         leaf (R.parse_antiquotation ctxt environment source))

  fun lower_binding lower ctxt site wrap_rhs environment
      (pattern, rhs, body) =
    let
      val lowered_rhs = lower environment rhs
      val prepared =
        P.prepare_binding site ctxt environment pattern
      val body_environment = P.binding_environment prepared
      val lowered_body = lower body_environment body
    in
      plain
        (T.bind (wrap_rhs (lowered_term lowered_rhs))
          (P.binding_abstraction prepared
            (lowered_term lowered_body)))
        [lowered_rhs, lowered_body]
    end

  fun lower_fuel ctxt environment source =
    leaf (R.parse_antiquotation ctxt environment source)

  fun lower_prepared_case ctxt position scrutinee
      lower_result prepared_arms =
    let
      fun lower_arm (tag, prepared) =
        let
          val arm_environment = P.prepared_environment prepared
          val (lowered_guard, lowered_body) =
            lower_result tag arm_environment prepared
        in (prepared, lowered_guard, lowered_body) end
      val lowered_arms = map lower_arm prepared_arms
      val term =
        P.compile_case ctxt (lowered_term scrutinee)
          (map
            (fn (prepared, guard, body) =>
              (prepared,
               Option.map lowered_term guard,
               lowered_term body))
            lowered_arms)
    in
      Lowered
        {term = term,
         analysis =
           matcher_case_analysis position
             scrutinee lowered_arms}
    end

  fun lower_case_arms ctxt environment position
      scrutinee lower_result arms =
    let
      val resolver =
        R.make_constructor_resolver ctxt position
      val prepared =
        map (fn (tag, arm) =>
          (tag,
           P.prepare_case_arm resolver ctxt
             environment arm)) arms
    in
      lower_prepared_case ctxt position scrutinee
        lower_result prepared
    end

  fun lower_for lower ctxt environment (pattern, iterable, body) =
    let
      val lowered_iterable = lower environment iterable
      val prepared =
        P.prepare_binding P.For_Binder ctxt environment pattern
      val body_environment = P.binding_environment prepared
      val lowered_body = lower body_environment body
    in
      plain
        (T.for_loop
          (T.into_iterator (lowered_term lowered_iterable))
          (P.binding_abstraction prepared
            (lowered_term lowered_body)))
        [lowered_iterable, lowered_body]
    end

  fun lower_while_let lower ctxt environment
      (fuel, pattern, scrutinee, body, position) =
    let
      val lowered_fuel = lower_fuel ctxt environment fuel
      val lowered_scrutinee = lower environment scrutinee
      val resolver =
        R.make_constructor_resolver ctxt position
      val prepared =
        P.prepare_case_arm resolver ctxt environment
          (UR_Arm (pattern, NONE, body))
      val body_environment =
        P.prepared_environment prepared
      val lowered_body = lower body_environment body
      val success =
        T.sequence (lowered_term lowered_body)
          (T.literal T.true_value)
      val lowered_success =
        plain success [lowered_body]
      val condition =
        (case P.prepared_direct_abstraction prepared of
           SOME abstraction =>
             plain
               (T.bind (lowered_term lowered_scrutinee)
                 (abstraction success))
               [lowered_scrutinee, lowered_success]
         | NONE =>
             let
               val arm =
                 (prepared, NONE, lowered_success)
               val term =
                 if P.prepared_is_total prepared
                 then
                   P.compile_case ctxt
                     (lowered_term lowered_scrutinee)
                     [(prepared, NONE, success)]
                 else
                   P.compile_case_with_fallback ctxt
                     (lowered_term lowered_scrutinee)
                     (T.literal T.false_value)
                     [(prepared, NONE, success)]
             in
               Lowered
                 {term = term,
                  analysis =
                    matcher_case_analysis position
                      lowered_scrutinee [arm]}
             end)
    in
      plain
        (T.bounded_while
          (lowered_term lowered_fuel)
          (lowered_term condition) T.skip)
        [lowered_fuel, condition]
    end

  (* Mutable scalar bindings allocate one store reference. Top-level tuple mutability remains erased,
     matching the frontend, and no binder-kind metadata is introduced. *)
  fun lower_mutable_binding lower ctxt environment
      (pattern, rhs, body, mutable_pos) =
    let
      val prepared =
        P.prepare_binding P.Mutable_Let_Binder
          ctxt environment pattern
      val lowered_rhs =
        (case P.mutable_rhs_mode prepared of
           P.Allocate_Rhs =>
             let val lowered = lower environment rhs
             in
               plain
                 (T.allocate_reference mutable_pos
                   (lowered_term lowered))
                 [lowered]
             end
         | P.Plain_Rhs => lower environment rhs)
      val body_environment = P.binding_environment prepared
      val lowered_body = lower body_environment body
    in
      plain
        (T.bind (lowered_term lowered_rhs)
          (P.binding_abstraction prepared
            (lowered_term lowered_body)))
        [lowered_rhs, lowered_body]
    end

  fun lower_match lower ctxt environment (flavour, scrutinee, arms, pos) =
    let
      val selected = P.select_match_flavour flavour arms pos
      val lowered_scrutinee = lower environment scrutinee
    in
      (case selected of
         MF_Switch =>
           let
             fun arm_pairs arm =
                   let
                     val prepared = P.prepare_switch_arm ctxt arm
                     val body = P.prepared_switch_body prepared
                     val lowered_body = lower environment body
                   in
                     (map (fn alternative =>
                        T.pair alternative
                          (lowered_term lowered_body))
                        (P.prepared_switch_keys prepared),
                      lowered_body)
                   end
             val pairs_and_bodies = map arm_pairs arms
             val pairs = maps #1 pairs_and_bodies
           in
             plain
               (T.bind (lowered_term lowered_scrutinee)
                 (T.numeral_case_selector
                   (fold_rev T.list_cons pairs T.list_nil)))
               (lowered_scrutinee ::
                 map #2 pairs_and_bodies)
           end
       | MF_Case =>
           let
             val alternatives = map (fn arm => ((), arm)) arms
             fun lower_result () arm_environment prepared =
               (Option.map
                  (fn (guard, _) => lower arm_environment guard)
                  (P.prepared_guard prepared),
                lower arm_environment (P.prepared_body prepared))
           in
             lower_case_arms ctxt environment pos
               lowered_scrutinee lower_result alternatives
           end
       | MF_Auto =>
           error "urust_expr: internal unresolved auto match flavour")
    end

  (* Lexical scope is explicit: a let RHS uses the outer environment, while its body uses the exact
     environment returned by pattern binding. Case alternatives follow the same rule independently. *)
  fun lower_expression ctxt environment expression =
    (case expression of
       UE_Unit _ =>
         leaf (T.literal HOLogic.unit)
     | UE_Tuple (arguments, _) =>
         let
           val lowered =
             map (lower_expression ctxt environment) arguments
         in
           plain (T.tuple (map lowered_term lowered)) lowered
         end
     | UE_Ident identifier =>
         leaf (R.literal_identifier ctxt environment identifier)
     | UE_Literal payload =>
         leaf (R.literal_expression ctxt environment payload)
     | UE_ExprAntiq source =>
         leaf (R.parse_antiquotation ctxt environment source)
     | UE_Seq (first, second) =>
         let
           val lowered_first =
             lower_expression ctxt environment first
           val lowered_second =
             lower_expression ctxt environment second
         in
           plain
             (T.sequence
               (lowered_term lowered_first)
               (lowered_term lowered_second))
             [lowered_first, lowered_second]
         end
     | UE_Return (value, _) =>
         let
           val lowered =
             (case value of
                SOME nested =>
                  lower_expression ctxt environment nested
              | NONE => leaf (T.literal HOLogic.unit))
         in
           plain (T.return_value (lowered_term lowered))
             [lowered]
         end
     | UE_Bin (operator, left, right, _) =>
         let
           val lowered_left =
             lower_expression ctxt environment left
           val lowered_right =
             lower_expression ctxt environment right
         in
           plain
             (T.binary operator
               (lowered_term lowered_left)
               (lowered_term lowered_right))
             [lowered_left, lowered_right]
         end
     | UE_Unary (operator, operand, pos) =>
         let
           val lowered_operand =
             lower_expression ctxt environment operand
         in
           plain
             (T.unary operator pos
               (lowered_term lowered_operand))
             [lowered_operand]
         end
     | UE_Group (inner, _) =>
         lower_expression ctxt environment inner
     | UE_Block (inner, _) =>
         lower_expression ctxt environment inner
     | UE_If (condition, then_branch, else_branch, _) =>
         let
           val lowered_condition =
             lower_expression ctxt environment condition
           val lowered_then =
             lower_expression ctxt environment then_branch
           val lowered_else =
             (case else_branch of
                SOME branch =>
                  lower_expression ctxt environment branch
              | NONE => leaf (T.literal HOLogic.unit))
         in
           plain
             (T.conditional
               (lowered_term lowered_condition)
               (lowered_term lowered_then)
               (lowered_term lowered_else))
             [lowered_condition, lowered_then, lowered_else]
         end
     | UE_While (fuel, condition, body, _) =>
         let
           val lowered_fuel =
             lower_fuel ctxt environment fuel
           val lowered_condition =
             lower_expression ctxt environment condition
           val lowered_body =
             lower_expression ctxt environment body
         in
           plain
             (T.bounded_while
               (lowered_term lowered_fuel)
               (lowered_term lowered_condition)
               (lowered_term lowered_body))
             [lowered_fuel, lowered_condition, lowered_body]
         end
     | UE_Loop (fuel, body, _) =>
         let
           val lowered_fuel =
             lower_fuel ctxt environment fuel
           val lowered_body =
             lower_expression ctxt environment body
         in
           plain
             (T.bounded_loop
               (lowered_term lowered_fuel)
               (lowered_term lowered_body))
             [lowered_fuel, lowered_body]
         end
     | UE_For (pattern, iterable, body, _) =>
         lower_for (lower_expression ctxt) ctxt environment
           (pattern, iterable, body)
     | UE_WhileLet
         (fuel, pattern, scrutinee, body, position) =>
         lower_while_let (lower_expression ctxt) ctxt environment
           (fuel, pattern, scrutinee, body, position)
     | UE_Let binding =>
         lower_binding (lower_expression ctxt) ctxt
           P.Let_Const_Binder I environment binding
     | UE_LetMut binding =>
         lower_mutable_binding (lower_expression ctxt) ctxt environment binding
     | UE_Const binding =>
         lower_binding (lower_expression ctxt) ctxt
           P.Let_Const_Binder I environment binding
     | UE_Call (name, name_pos, arguments, call_pos) =>
         let
           val function =
             R.function_identifier ctxt environment (name, name_pos)
           val lowered_arguments =
             map (lower_expression ctxt environment) arguments
         in
           plain
             (T.function_call call_pos function
               (map lowered_term lowered_arguments))
             lowered_arguments
         end
     | UE_Field (receiver, name, pos) =>
         let
           val lowered_receiver =
             lower_expression ctxt environment receiver
         in
           plain
             (R.field_expression ctxt
               (lowered_term lowered_receiver) name pos)
             [lowered_receiver]
         end
     | UE_Assign (operator, place, rhs, pos) =>
         let
           val lowered_place =
             lower_place (lower_expression ctxt) ctxt environment place
           val lowered_rhs = lower_expression ctxt environment rhs
           val term =
             (case operator of
                Assign =>
                  T.update pos
                    (lowered_term lowered_place)
                    (lowered_term lowered_rhs)
              | AssignAdd =>
                  T.assign_add pos
                    (lowered_term lowered_place)
                    (lowered_term lowered_rhs)
              | AssignBin binary_operator =>
                  T.update pos
                    (lowered_term lowered_place)
                    (T.assignment_binary binary_operator
                      (T.unary U_Deref pos
                        (lowered_term lowered_place))
                      (lowered_term lowered_rhs)))
         in
           plain term [lowered_place, lowered_rhs]
         end
     | UE_Match match =>
         lower_match (lower_expression ctxt) ctxt environment match)

  fun make_result ctxt expression =
    let
      val Lowered {term, analysis} =
        lower_expression ctxt R.empty_environment expression
    in
      Result
        {term = term,
         analysis = analysis,
         compatibility = classify analysis}
    end

  fun mk_closed ctxt expression =
    result_term (make_result ctxt expression)
end
\<close>

end
