theory Parser_Impl_Translate
  imports Parser_Impl_Patterns
begin

section\<open> Expression elaboration \<close>

ML\<open>
signature URUST_TRANSLATE =
sig
  val mk_closed: Proof.context -> URust_AST.ur_expr -> term
end
\<close>

text\<open>
Expression lowering orchestrates the term, resolution, and pattern layers. Terms remain based on
\<open>dummyT\<close>, and the command performs the single final \<open>Syntax.check_term\<close>.
\<close>

ML\<open>
(* Final expression-translation boundary. This structure owns recursive lowering of a complete
   URust_AST.ur_expr, including place translation and the orchestration of bindings, loops, and
   matches. It delegates shallow-term vocabulary to URust_Elab_Terms, name and antiquotation
   resolution to URust_Resolution, and pattern preparation and case compilation to URust_Patterns;
   it does not parse source, type-check terms, or install definitions.

   The sole public operation is mk_closed: given the Proof.context in which the source is being
   elaborated and an expression AST, it lowers the expression from
   URust_Resolution.empty_environment and returns one unchecked HOL term. The result may contain
   dummy types and must be passed to Syntax.check_term exactly once by the command layer in the same
   context. Successful lowering preserves lexical scope and the existing shallow-embedding term
   shape; for syntax shared with the old frontend, callers may rely on alpha-identical checked
   output after the documented administrative-let unfolding. Resolution and pattern-validation
   failures are propagated with their source positions. The signature exposes no public types or
   constructors.

   All lower_* functions, the recursive traversal order, the T/R/P aliases, and the division of work
   among helper functions are implementation details hidden by URUST_TRANSLATE. *)
structure URust_Translate : URUST_TRANSLATE =
struct
  open URust_AST
  structure T = URust_Elab_Terms
  structure R = URust_Resolution
  structure P = URust_Patterns

  fun lower_place lower ctxt environment place =
    (case place of
       UP_Ident identifier =>
         R.literal_identifier ctxt environment identifier
     | UP_Deref (expression, _) =>
         lower environment expression
     | UP_Field (base, name, pos) =>
         R.field_expression ctxt
           (lower_place lower ctxt environment base) name pos
     | UP_Antiq source =>
         R.parse_antiquotation ctxt environment source)

  fun lower_binding lower ctxt site wrap_rhs environment
      (pattern, rhs, body) =
    let
      val lowered_rhs = wrap_rhs (lower environment rhs)
      val prepared =
        P.prepare_binding site ctxt environment pattern
      val body_environment = P.binding_environment prepared
      val lowered_body = lower body_environment body
    in
      T.bind lowered_rhs
        (P.binding_abstraction prepared lowered_body)
    end

  fun lower_fuel ctxt environment source =
    R.parse_antiquotation ctxt environment source

  fun lower_prepared_case ctxt scrutinee lower_result prepared_arms =
    let
      fun lower_arm (tag, prepared) =
        let
          val arm_environment = P.prepared_environment prepared
          val (lowered_guard, lowered_body) =
            lower_result tag arm_environment prepared
        in (prepared, lowered_guard, lowered_body) end
    in
      P.compile_case ctxt scrutinee (map lower_arm prepared_arms)
    end

  fun lower_case_arms ctxt environment position scrutinee lower_result arms =
    let
      val resolver =
        R.make_constructor_resolver ctxt position
      val prepared =
        map (fn (tag, arm) =>
          (tag,
           P.prepare_case_arm resolver ctxt
             environment arm)) arms
    in
      lower_prepared_case ctxt scrutinee lower_result prepared
    end

  fun lower_for lower ctxt environment (pattern, iterable, body) =
    let
      val lowered_iterable = lower environment iterable
      val prepared =
        P.prepare_binding P.For_Binder ctxt environment pattern
      val body_environment = P.binding_environment prepared
      val lowered_body = lower body_environment body
    in
      T.for_loop (T.into_iterator lowered_iterable)
        (P.binding_abstraction prepared lowered_body)
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
               then P.compile_case ctxt lowered_scrutinee [arm]
               else
                 P.compile_case_with_fallback ctxt lowered_scrutinee
                   (T.literal T.false_value) [arm]
             end)
    in T.bounded_while lowered_fuel condition T.skip end

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
             T.allocate_reference mutable_pos
               (lower environment rhs)
         | P.Plain_Rhs => lower environment rhs)
      val body_environment = P.binding_environment prepared
      val lowered_body = lower body_environment body
    in
      T.bind lowered_rhs
        (P.binding_abstraction prepared lowered_body)
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
                     map (fn alternative =>
                       T.pair alternative lowered_body)
                       (P.prepared_switch_keys prepared)
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

  (* Lexical scope is explicit: a let RHS uses the outer environment, while its body uses the exact
     environment returned by pattern binding. Case alternatives follow the same rule independently. *)
  fun lower_expression ctxt environment expression =
    (case expression of
       UE_Unit _ =>
         T.literal HOLogic.unit
     | UE_Tuple (arguments, _) =>
         T.tuple (map (lower_expression ctxt environment) arguments)
     | UE_Ident identifier =>
         R.literal_identifier ctxt environment identifier
     | UE_Literal payload =>
         R.literal_expression ctxt environment payload
     | UE_ExprAntiq source =>
         R.parse_antiquotation ctxt environment source
     | UE_Seq (first, second) =>
         T.sequence
           (lower_expression ctxt environment first)
           (lower_expression ctxt environment second)
     | UE_Return (value, _) =>
         T.return_value
           (case value of
              SOME expression => lower_expression ctxt environment expression
            | NONE => T.literal HOLogic.unit)
     | UE_Bin (operator, left, right, _) =>
         T.binary operator
           (lower_expression ctxt environment left)
           (lower_expression ctxt environment right)
     | UE_Unary (operator, operand, pos) =>
         T.unary operator pos (lower_expression ctxt environment operand)
     | UE_Group (inner, _) =>
         lower_expression ctxt environment inner
     | UE_Block (inner, _) =>
         lower_expression ctxt environment inner
     | UE_If (condition, then_branch, else_branch, _) =>
         T.conditional
           (lower_expression ctxt environment condition)
           (lower_expression ctxt environment then_branch)
           (case else_branch of
              SOME branch => lower_expression ctxt environment branch
            | NONE => T.literal HOLogic.unit)
     | UE_While (fuel, condition, body, _) =>
         T.bounded_while
           (lower_fuel ctxt environment fuel)
           (lower_expression ctxt environment condition)
           (lower_expression ctxt environment body)
     | UE_Loop (fuel, body, _) =>
         T.bounded_loop
           (lower_fuel ctxt environment fuel)
           (lower_expression ctxt environment body)
     | UE_For (pattern, iterable, body, _) =>
         lower_for (lower_expression ctxt) ctxt environment
           (pattern, iterable, body)
     | UE_WhileLet (fuel, pattern, scrutinee, body, pos) =>
         lower_while_let (lower_expression ctxt) ctxt environment
           (fuel, pattern, scrutinee, body, pos)
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
         in T.function_call call_pos function lowered_arguments end
     | UE_Field (receiver, name, pos) =>
         R.field_expression ctxt
           (lower_expression ctxt environment receiver) name pos
     | UE_Assign (operator, place, rhs, pos) =>
         let
           val lowered_place =
             lower_place (lower_expression ctxt) ctxt environment place
           val lowered_rhs = lower_expression ctxt environment rhs
         in
           (case operator of
              Assign => T.update pos lowered_place lowered_rhs
            | AssignAdd => T.assign_add pos lowered_place lowered_rhs
            | AssignBin binary_operator =>
                T.update pos lowered_place
                  (T.assignment_binary binary_operator
                    (T.unary U_Deref pos lowered_place) lowered_rhs))
         end
     | UE_Match match =>
         lower_match (lower_expression ctxt) ctxt environment match)

  fun mk_closed ctxt expression =
    lower_expression ctxt R.empty_environment expression
end
\<close>

end
