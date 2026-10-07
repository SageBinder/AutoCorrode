(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Denotation_Tests
  imports Frontend_Common.Frontend_Common
begin

ML_val\<open>
local
  structure P = Frontend_Declaration_Plan
  structure X = Frontend_Transaction
  structure T = Frontend_HOL_Term

  val pos = \<^here>

  fun assert message condition =
    if condition then ()
    else error ("frontend plan test: " ^ message)

  fun rejects label fragment thunk =
    ((thunk ();
      error ("frontend plan test: accepted " ^ label))
     handle ERROR message =>
       assert
         ("wrong rejection for " ^ label ^ ": " ^ message)
         (String.isSubstring fragment message))

  val fresh_binding =
    T.qualified_binding "Planned_Unit" "fresh_constant" pos
  val plan =
    P.empty
    |> P.declare P.Constant fresh_binding
    |> P.require_term "planned right-hand side" pos (T.mk_nat 7)
  val lthy =
    Named_Target.theory_init (Proof_Context.theory_of \<^context>)
  val checked = P.preflight lthy plan
  val checked_declarations = P.checked_declarations checked
  val _ =
    assert "preflight lost a declaration"
      (length checked_declarations = 1)
  val _ =
    assert "preflight lost a checked term"
      (length (P.checked_terms checked) = 1)

  val _ =
    rejects "duplicate plan claim" "duplicate constant"
      (fn () =>
        P.empty
        |> P.declare P.Constant fresh_binding
        |> P.declare P.Constant fresh_binding
        |> K ())

  fun define_constant binding rhs lthy0 =
    let
      val (_, lthy1) =
        Local_Theory.define
          ((binding, NoSyn),
           ((Thm.def_binding binding, []), rhs)) lthy0
    in
      ((), lthy1)
    end

  val existing_binding =
    T.qualified_binding "Planned_Unit" "existing_constant" pos
  val (_, lthy_with_existing) =
    define_constant existing_binding (T.mk_nat 0) lthy
  val _ =
    rejects "existing constant" "already exists"
      (fn () =>
        P.empty
        |> P.declare P.Constant existing_binding
        |> P.preflight lthy_with_existing
        |> K ())

  val _ =
    rejects "bad term obligation" "ill-formed HOL term"
      (fn () =>
        P.empty
        |> P.require_term "bad obligation" pos
             (Const ("Frontend_Common.not_declared", dummyT))
        |> P.preflight lthy
        |> K ())

  val transaction_binding =
    T.qualified_binding "Transaction_Unit" "committed" pos
  val transaction_name =
    Local_Theory.full_name lthy transaction_binding
  val transaction =
    define_constant transaction_binding (T.mk_nat 11)
  val (_, committed_lthy) =
    X.preflight_then_commit transaction lthy
  val _ =
    assert "transaction changed its input theory"
      (not (Sign.declared_const
        (Proof_Context.theory_of lthy) transaction_name))
  val _ =
    assert "transaction did not commit after preflight"
      (Sign.declared_const
        (Proof_Context.theory_of committed_lthy) transaction_name)

  val rollback_binding =
    T.qualified_binding "Transaction_Unit" "rolled_back" pos
  val rollback_name =
    Local_Theory.full_name lthy rollback_binding
  fun failing_transaction lthy0 =
    let
      val (_, lthy1) =
        define_constant rollback_binding (T.mk_nat 0) lthy0
      val _ = Frontend_Diagnostics.error_at pos "planned failure"
    in
      ((), lthy1)
    end
  val failure =
    Exn.capture
      (X.preflight_then_commit failing_transaction) lthy
  val _ =
    (case failure of
       Exn.Exn (ERROR message) =>
         assert "wrong transaction failure"
           (String.isSubstring "planned failure" message)
     | Exn.Exn exn => Exn.reraise exn
     | Exn.Res _ =>
         error "frontend plan test: failing transaction succeeded")
  val _ =
    assert "failed transaction changed its input theory"
      (not (Sign.declared_const
        (Proof_Context.theory_of lthy) rollback_name))
in
  val _ = ()
end
\<close>

end
