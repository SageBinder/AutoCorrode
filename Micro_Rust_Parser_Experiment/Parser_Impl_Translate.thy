theory Parser_Impl_Translate
  imports Parser_Impl_Macros
begin

section\<open> Expression elaboration \<close>

ML\<open>
signature URUST_TRANSLATE =
sig
  val mk_closed: Proof.context -> URust_AST.ur_expr -> term
end
\<close>

text\<open>
Expression lowering orchestrates recursive traversal across the feature-specific elaboration layers.
Terms remain based on \<open>dummyT\<close>, and the command performs the single final
\<open>Syntax.check_term\<close>.
\<close>

ML\<open>
(* Final expression-translation boundary. This structure owns recursive lowering of a complete
   URust_AST.ur_expr, including place translation and the orchestration of bindings and regular loops.
   It delegates matching and macro lowering to their sealed feature layers; it does not parse source,
   type-check terms, or install definitions.

   The sole public operation is mk_closed: given the Proof.context in which the source is being
   elaborated and an expression AST, it lowers the expression from
   URust_Resolution.empty_environment and returns one unchecked HOL term. The result may contain
   dummy types and must be passed to Syntax.check_term exactly once by the command layer in the same
   context. Successful lowering preserves lexical scope and the existing shallow-embedding term
   shape; for syntax shared with the old frontend, callers may rely on alpha-identical checked
   output directly. The conformance command unfolds only the generated NAME_def before closing by
   reflexivity. Resolution and pattern-validation failures are propagated with their source
   positions. The signature exposes no public types or constructors.

   All lower_* functions, the recursive traversal order, module aliases, and the division of work among
   helper functions are implementation details hidden by URUST_TRANSLATE. *)
structure URust_Translate :> URUST_TRANSLATE =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure R = URust_Resolution
  structure P = URust_Patterns
  structure M = URust_Matching
  structure X = URust_Macros

  fun lower_place lower ctxt environment place =
    (case place of
       UP_Ident identifier =>
         R.literal_identifier ctxt environment identifier
     | UP_Deref (expression, _) =>
         lower environment expression
     | UP_Field (base, name, pos) =>
         R.field_expression ctxt environment
           (lower_place lower ctxt environment base) name pos
     | UP_Index (base, index, _) =>
         T.index
           (lower_place lower ctxt environment base)
           (lower environment index)
     | UP_Antiq source =>
         R.parse_antiquotation ctxt environment source)

  fun lower_binding lower ctxt site environment
      (pattern, rhs, body) =
    let
      val lowered_rhs = lower environment rhs
      val prepared =
        P.prepare_binding site ctxt environment pattern
      val body_environment = P.binding_environment prepared
      val lowered_body = lower body_environment body
    in P.bind_prepared prepared lowered_rhs lowered_body end

  fun lower_fuel ctxt environment source =
    R.parse_antiquotation ctxt environment source

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

  fun lower_closure lower ctxt environment (formals, body) =
    let
      fun formal_signature (P_Ident formal) = formal
        | formal_signature (P_Wild pos) =
            error
              ("urust_expr: closure formal must be an identifier" ^
                Position.here pos)
        | formal_signature _ =
            error "urust_expr: internal non-identifier closure formal"
      val signatures = map formal_signature formals
      val (formal_terms, body_environment) =
        R.allocate_closure_formals ctxt environment signatures
      val lowered_body = lower body_environment body
    in T.closure formal_terms lowered_body end

  (* Lexical scope is explicit: a let RHS uses the outer environment, while its body uses the exact
     environment returned by pattern binding. Closure bodies use the final duplicate-permitting formal
     environment, while every formal still contributes its own ordered abstraction. Case alternatives
     follow the same rule independently. *)
  fun lower_expression ctxt environment expression =
    (case expression of
       UE_Unit _ =>
         T.literal HOLogic.unit
     | UE_Tuple (arguments, _) =>
         T.tuple (map (lower_expression ctxt environment) arguments)
     | UE_Array (elements, _) =>
         T.array_literal
           (map (lower_expression ctxt environment) elements)
     | UE_Ident identifier =>
         R.literal_identifier ctxt environment identifier
     | UE_Literal payload =>
         R.literal_expression ctxt environment payload
     | UE_ExprAntiq source =>
         R.parse_antiquotation ctxt environment source
     | UE_Closure (formals, body, _) =>
         lower_closure (lower_expression ctxt) ctxt environment
           (formals, body)
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
     | UE_Range (kind, lower, upper, _) =>
         T.bounded_range kind
           (lower_expression ctxt environment lower)
           (lower_expression ctxt environment upper)
     | UE_Unary
         (U_Borrow _, UE_Array (elements, _), _) =>
         T.array_literal
           (map (lower_expression ctxt environment) elements)
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
     | UE_IfLet if_let =>
         M.lower_if_let (lower_expression ctxt) ctxt environment if_let
     | UE_LetElse let_else =>
         M.lower_let_else (lower_expression ctxt) ctxt environment let_else
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
         M.lower_while_let (lower_expression ctxt) ctxt environment
           (fuel, pattern, scrutinee, body, pos)
     | UE_Let binding =>
         lower_binding (lower_expression ctxt) ctxt
           P.Let_Const_Binder environment binding
     | UE_LetMut (pattern, rhs, body, mutable_pos) =>
         lower_binding (lower_expression ctxt) ctxt
           (P.Mutable_Let_Binder mutable_pos) environment
           (pattern, rhs, body)
     | UE_Const binding =>
         lower_binding (lower_expression ctxt) ctxt
           P.Let_Const_Binder environment binding
     | UE_Call (name, name_pos, arguments, call_pos) =>
         let
           val function =
             R.function_identifier ctxt environment (name, name_pos)
           val lowered_arguments =
             map (lower_expression ctxt environment) arguments
         in T.function_call call_pos function lowered_arguments end
     | UE_Field (receiver, name, pos) =>
         R.field_expression ctxt environment
           (lower_expression ctxt environment receiver) name pos
     | UE_Index (receiver, index, _) =>
         T.index
           (lower_expression ctxt environment receiver)
           (lower_expression ctxt environment index)
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
     | UE_Macro macro =>
         X.lower_macro (lower_expression ctxt) ctxt environment macro
     | UE_Match match =>
         M.lower_match (lower_expression ctxt) ctxt environment match)

  fun mk_closed ctxt expression =
    lower_expression ctxt R.empty_environment expression
end
\<close>

end
