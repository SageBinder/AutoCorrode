theory Micro_Rust_Translate
  imports Micro_Rust_Patterns
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

  fun lower_binding lower ctxt wrap_rhs environment (pattern, rhs, body) =
    let
      val lowered_rhs = wrap_rhs (lower environment rhs)
      val (abstraction, body_environment) =
        P.bind_irrefutable ctxt environment pattern
      val lowered_body = lower body_environment body
    in T.bind lowered_rhs (abstraction lowered_body) end

  (* Mutable scalar bindings allocate one store reference. Top-level tuple mutability remains erased,
     matching the frontend, and no binder-kind metadata is introduced. *)
  fun lower_mutable_binding lower ctxt environment
      (pattern, rhs, body, mutable_pos) =
    (case pattern of
       P_Ident _ =>
         lower_binding lower ctxt (T.allocate_reference mutable_pos) environment
           (pattern, rhs, body)
     | P_Wild _ =>
         lower_binding lower ctxt (T.allocate_reference mutable_pos) environment
           (pattern, rhs, body)
     | P_Tuple _ =>
         lower_binding lower ctxt I environment (pattern, rhs, body)
     | _ =>
         error ("urust_expr: invalid mutable binding pattern" ^
           " (expected identifier, `_`, or top-level tuple destructuring)" ^
           Position.here (P.position pattern)))

  fun lower_match lower ctxt environment (flavour, scrutinee, arms, pos) =
    let
      val selected = P.select_match_flavour flavour arms pos
      val lowered_scrutinee = lower environment scrutinee
    in
      (case selected of
         MF_Switch =>
           let
             fun arm_pairs (UR_Arm (pattern, NONE, body)) =
                   let
                     val lowered_body = lower environment body
                   in
                     map (fn alternative =>
                       T.pair (P.switch_key ctxt alternative) lowered_body)
                       (P.switch_alternatives pattern)
                   end
               | arm_pairs (UR_Arm (_, SOME (_, guard_pos), _)) =
                   error ("urust_expr: guards are not supported in explicit `match_switch`" ^
                     Position.here guard_pos)
             val pairs = maps arm_pairs arms
           in
             T.bind lowered_scrutinee
               (T.numeral_case_selector
                 (fold_rev T.list_cons pairs T.list_nil))
           end
       | MF_Case =>
           let
             fun lower_arm alternative =
               let
                 val prepared =
                   P.prepare_case_arm ctxt environment alternative
                 val arm_environment = P.prepared_environment prepared
                 val lowered_guard =
                   Option.map
                     (fn (guard, _) => lower arm_environment guard)
                     (P.prepared_guard prepared)
                 val lowered_body =
                   lower arm_environment (P.prepared_body prepared)
               in (prepared, lowered_guard, lowered_body) end
             val lowered_arms =
               map lower_arm (P.case_alternatives arms)
           in P.compile_case ctxt lowered_scrutinee lowered_arms end
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
     | UE_Let binding =>
         lower_binding (lower_expression ctxt) ctxt I environment binding
     | UE_LetMut binding =>
         lower_mutable_binding (lower_expression ctxt) ctxt environment binding
     | UE_Const binding =>
         lower_binding (lower_expression ctxt) ctxt I environment binding
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
