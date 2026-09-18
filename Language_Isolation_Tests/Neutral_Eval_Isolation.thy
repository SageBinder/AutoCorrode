(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Neutral_Eval_Isolation
  imports
    Shallow_Computation.Eval
    Dependency_Audit
begin

term Eval.evaluates_to_return
term Eval.evaluates_to_value
term Eval.evaluates_to_abort

thm Eval.evaluates_to_return_eq
thm Eval.urust_eval_action_bind
thm Eval.urust_eval_predicate_literal
thm Eval.urust_eval_action_get

lemma isolation_neutral_eval_predicate_rule [shallow_computation_eval_predicate_simps]:
  shows True
  by simp

lemma isolation_neutral_eval_action_rule [shallow_computation_eval_action_simps]:
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
      if condition then () else error ("neutral evaluation isolation: " ^ message)
  in
    val _ =
      Language_Isolation_Dependency_Audit.assert_context
        "Shallow_Computation.Eval"
        ["Micro_Rust_Parsing_Legacy_Frontend",
         "Micro_Rust_Parser_Impl",
         "Shallow_Micro_Rust_Base",
         "Shallow_Micro_Rust",
         "Isabelle_C",
         "C"]
        ctxt
    val _ = assert "neutral predicate registry is not writable"
      (member \<^named_theorems>\<open>shallow_computation_eval_predicate_simps\<close>
        (theorem "isolation_neutral_eval_predicate_rule"))
    val _ = assert "neutral action registry is not writable"
      (member \<^named_theorems>\<open>shallow_computation_eval_action_simps\<close>
        (theorem "isolation_neutral_eval_action_rule"))
    val _ = assert "legacy evaluation registry leaked"
      (not (can (Proof_Context.get_thms ctxt) "urust_eval_predicate_simps"))
    val _ = assert "profile assertion rule leaked"
      (not (can (Proof_Context.get_thm ctxt) "Eval.urust_eval_action_assert"))
    val _ = assert "profile numeric rule leaked"
      (not (can (Proof_Context.get_thm ctxt) "Eval.urust_eval_action_add_no_wrap"))
  end
\<close>

end
