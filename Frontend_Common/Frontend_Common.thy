(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Frontend_Common
  imports Main
begin

section \<open>Language-neutral frontend support\<close>

text \<open>
This session contains small, immutable building blocks shared by source frontends.  It has no
dependency on a language profile or parser.
\<close>

ML_file \<open>diagnostics.ML\<close>
ML_file \<open>hol_term.ML\<close>
ML_file \<open>declaration_plan.ML\<close>
ML_file \<open>transaction.ML\<close>

ML_val \<open>
  val lthy =
    Named_Target.theory_init
      (Proof_Context.theory_of \<^context>)
  val full_name =
    Context.theory_name {long = false} (Proof_Context.theory_of \<^context>) ^
    ".frontend_plan_probe"
  val checked =
    Frontend_Declaration_Plan.empty
    |> Frontend_Declaration_Plan.declare_full
         Frontend_Declaration_Plan.Constant
         full_name \<^here>
    |> Frontend_Declaration_Plan.preflight lthy
  val _ =
    if map #full_name
         (Frontend_Declaration_Plan.checked_declarations checked) =
       [full_name]
    then ()
    else error "Frontend_Common: absolute declaration plan check failed"
  val (value, _) =
    Frontend_Transaction.preflight_then_commit_with
      (fn result => fn _ =>
        if result = 7 then ()
        else error "Frontend_Common: transaction preview validation failed")
      (Frontend_Transaction.pure 7)
      lthy
  val _ =
    if value = 7 then ()
    else error "Frontend_Common: transaction commit result changed"
\<close>

end
