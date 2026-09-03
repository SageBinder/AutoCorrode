theory Parser_Impl_Matching
  imports Parser_Impl_Patterns
begin

section\<open> Match lowering \<close>

ML\<open>
signature URUST_MATCHING =
sig
  val lower_match:
    (URust_Resolution.environment -> URust_AST.ur_expr -> term) ->
      Proof.context ->
      URust_Resolution.environment ->
      URust_AST.match_flavour * URust_AST.ur_expr *
        URust_AST.ur_arm list * Position.T ->
      term
  val lower_while_let:
    (URust_Resolution.environment -> URust_AST.ur_expr -> term) ->
      Proof.context ->
      URust_Resolution.environment ->
      Input.source * URust_AST.ur_pat * URust_AST.ur_expr *
        URust_AST.ur_expr * Position.T ->
      term
  val lower_if_let:
    (URust_Resolution.environment -> URust_AST.ur_expr -> term) ->
      Proof.context ->
      URust_Resolution.environment ->
      URust_AST.ur_pat * URust_AST.ur_expr * URust_AST.ur_expr *
        URust_AST.ur_expr option * Position.T ->
      term
  val lower_let_else:
    (URust_Resolution.environment -> URust_AST.ur_expr -> term) ->
      Proof.context ->
      URust_Resolution.environment ->
      URust_AST.ur_pat * URust_AST.ur_expr * URust_AST.ur_expr *
        URust_AST.ur_expr * Position.T ->
      term
  val lower_boolean_match:
    (URust_Resolution.environment -> URust_AST.ur_expr -> term) ->
      Proof.context ->
      URust_Resolution.environment ->
      URust_AST.ur_expr * URust_AST.ur_pat * Position.T ->
      term
end
\<close>

text\<open>
This layer owns case-arm orchestration and the five consumers of prepared case patterns. Recursive
expression lowering remains a callback supplied by \<open>URust_Translate\<close>; pattern resolution,
normalization, coverage, and case-term compilation remain sealed behind \<open>URust_Patterns\<close>.
\<close>

ML\<open>
(*
  URust_Matching is the orchestration boundary between recursive expression traversal and prepared
  pattern compilation. It owns the control-flow-specific sequencing for ordinary matches, `if let`,
  `let ... else`, `while let`, and boolean pattern matches, but does not resolve names directly,
  expose prepared-pattern representations, recursively traverse arbitrary expressions itself,
  type-check terms, or install definitions. URust_Patterns remains responsible for pattern
  resolution, validation, normalization, coverage, and exact case-term construction.

  All five public operations take the same lowering callback first. The callback must lower one
  URust_AST.ur_expr in the supplied URust_Resolution.environment and return an unchecked shallow HOL
  term. Callers must provide the callback closed over the same Proof.context passed separately to the
  matching operation. URust_Matching invokes it exactly at the source-expression boundaries described
  below; it never re-walks a pattern or expression AST. Results may contain dummy types and remain
  unchecked until the command layer's sole Syntax.check_term.

  The public interface is:

  - lower_match lower ctxt environment (flavour, scrutinee, arms, position) validates and resolves the
    match flavour before lowering the scrutinee. Switch lowering prepares each source arm and lowers
    its body in the unchanged outer environment, preserving alternative and arm order. Case lowering
    prepares all source arms before lowering any guard or body; each guard and body is lowered once in
    that prepared arm's exact environment. The resulting term evaluates the lowered scrutinee once and
    preserves the existing frontend-shaped handler and fallback expansion.

  - lower_while_let lower ctxt environment (fuel, pattern, scrutinee, body, position) lowers fuel and
    scrutinee in the outer environment, in that order, before preparing the pattern. Only the loop body
    is lowered in the prepared pattern environment. Directly irrefutable patterns use the prepared
    abstraction; refutable patterns use case compilation with a false fallback unless conservative
    prepared-pattern coverage proves the pattern total. Success sequences the body with literal true,
    and bounded_while receives skip as its body.

  - lower_if_let and lower_let_else lower their scrutinee once in the outer environment, prepare one
    unguarded source pattern, lower success in the prepared environment, and lower fallback in the
    outer environment. One-armed `if let` supplies skip. Ordinary patterns always install the
    frontend-shaped explicit wildcard fallback, including total patterns; the frontend's syntactic
    top-level tuple exception instead uses its direct irrefutable abstraction and ignores fallback.

  - lower_boolean_match lower ctxt environment (scrutinee, pattern, position) lowers the scrutinee in
    the outer environment, prepares one unguarded arm, and compiles a literal-true result with an
    explicit literal-false fallback. It deliberately applies no macro-specific pattern restrictions;
    callers such as URust_Macros must enforce those before invoking this operation.

  Pattern, flavour, and resolution errors retain their existing source positions and propagate to the
  caller. lower_prepared_case, lower_case_arms, arm tags, preparation order plumbing, module aliases,
  and the choice of shallow-term builders are private implementation details. URUST_MATCHING exposes
  no prepared-pattern type, helper representation, or alternate compilation entry point.
*)
structure URust_Matching :> URUST_MATCHING =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure P = URust_Patterns

  fun lower_prepared_case ctxt scrutinee lower_result prepared_arms =
    let
      fun lower_arm (tag, prepared) =
        let
          val arm_environment = P.prepared_environment prepared
          val (lowered_guard, lowered_body) =
            lower_result tag arm_environment prepared
        in (prepared, lowered_guard, lowered_body) end
    in
      P.compile_case ctxt NONE scrutinee
        (map lower_arm prepared_arms)
    end

  fun lower_case_arms ctxt environment position scrutinee lower_result arms =
    let
      val prepared =
        P.prepare_case_arms ctxt position environment
          (map snd arms)
      val tagged = map2 pair (map fst arms) prepared
    in
      lower_prepared_case ctxt scrutinee lower_result tagged
    end

  fun lower_while_let lower ctxt environment
      (fuel, pattern, scrutinee, body, position) =
    let
      val lowered_fuel =
        URust_Resolution.parse_antiquotation ctxt environment fuel
      val lowered_scrutinee = lower environment scrutinee
      val prepared =
        the_single
          (P.prepare_case_arms ctxt position environment
            [UR_Arm (pattern, NONE, body)])
      val body_environment =
        P.prepared_environment prepared
      val success =
        T.sequence (lower body_environment body)
          (T.literal T.true_value)
      val condition =
        (case P.prepared_direct_abstraction prepared of
           SOME abstraction =>
             T.bind lowered_scrutinee (abstraction success)
         | NONE =>
             let
               val arm = (prepared, NONE, success)
             in
               if P.prepared_is_total prepared
               then P.compile_case ctxt NONE lowered_scrutinee [arm]
               else
                 P.compile_case ctxt
                   (SOME (T.literal T.false_value))
                   lowered_scrutinee [arm]
             end)
    in T.bounded_while lowered_fuel condition T.skip end

  fun lower_pattern_branch lower ctxt environment
      (pattern, scrutinee, success, fallback, position) =
    let
      val lowered_scrutinee = lower environment scrutinee
    in
      (case pattern of
         P_Tuple _ =>
           let
             val prepared =
               P.prepare_binding P.Let_Const_Binder ctxt environment pattern
             val success_environment =
               P.binding_environment prepared
             val lowered_success =
               lower success_environment success
           in
             P.bind_prepared prepared lowered_scrutinee lowered_success
           end
       | _ =>
           let
             val prepared =
               the_single
                 (P.prepare_case_arms ctxt position environment
                   [UR_Arm (pattern, NONE, success)])
             val success_environment =
               P.prepared_environment prepared
             val lowered_success =
               lower success_environment success
             val lowered_fallback =
               lower environment fallback
           in
             P.compile_case ctxt
               (SOME lowered_fallback)
               lowered_scrutinee
               [(prepared, NONE, lowered_success)]
           end)
    end

  fun lower_if_let lower ctxt environment
      (pattern, scrutinee, success, fallback, position) =
    lower_pattern_branch lower ctxt environment
      (pattern, scrutinee, success,
       the_default (UE_Unit position) fallback, position)

  fun lower_let_else lower ctxt environment
      (pattern, scrutinee, fallback, continuation, position) =
    lower_pattern_branch lower ctxt environment
      (pattern, scrutinee, continuation, fallback, position)

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
                     val (keys, body) = P.prepare_switch_arm ctxt arm
                     val lowered_body = lower environment body
                   in
                     map (fn alternative =>
                       T.pair alternative lowered_body)
                       keys
                   end
             val pairs = maps arm_pairs arms
           in
             T.bind lowered_scrutinee
               (T.numeral_case_selector
                 (fold_rev T.list_cons pairs T.list_nil))
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
             lower_case_arms ctxt environment pos lowered_scrutinee
               lower_result alternatives
           end
       | MF_Auto =>
           error "urust_expr: internal unresolved auto match flavour")
    end

  fun lower_boolean_match lower ctxt environment
      (scrutinee, pattern, position) =
    let
      val lowered_scrutinee = lower environment scrutinee
      val prepared =
        the_single
          (P.prepare_case_arms ctxt position environment
            [UR_Arm (pattern, NONE, UE_Unit position)])
    in
      P.compile_case ctxt
        (SOME (T.literal T.false_value))
        lowered_scrutinee
        [(prepared, NONE, T.literal T.true_value)]
    end
end
\<close>

end
