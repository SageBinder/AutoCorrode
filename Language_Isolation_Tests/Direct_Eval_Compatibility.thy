(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Direct_Eval_Compatibility
  imports
    Shallow_Micro_Rust.Eval_Profile
    Dependency_Audit
begin

term Eval.evaluates_to_return
term Eval.evaluates_to_value
term Eval.evaluates_to_abort

thm Eval.evaluates_to_return_eq
thm Eval.urust_eval_action_bind
thm Eval.urust_eval_predicate_literal
thm Eval.urust_eval_action_get

lemma isolation_eval_predicate_rule [urust_eval_predicate_simps]:
  shows True
  by simp

lemma isolation_eval_action_rule [urust_eval_action_simps]:
  shows \<open>id x = x\<close>
  by simp

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun member collection thm =
      exists (Thm.equiv_thm thy o pair thm) (Named_Theorems.get ctxt collection)
    fun theorem name = Proof_Context.get_thm ctxt name
    fun assert message condition =
      if condition then () else error ("direct evaluation compatibility: " ^ message)
  in
    val _ = assert "predicate registry remains writable"
      (member \<^named_theorems>\<open>urust_eval_predicate_simps\<close>
        (theorem "isolation_eval_predicate_rule"))
    val _ = assert "action registry remains writable"
      (member \<^named_theorems>\<open>urust_eval_action_simps\<close>
        (theorem "isolation_eval_action_rule"))
  end
\<close>

end
