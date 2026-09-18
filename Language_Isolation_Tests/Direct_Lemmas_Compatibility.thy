(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Direct_Lemmas_Compatibility
  imports
    Shallow_Micro_Rust.Core_Expression_Lemmas
    Dependency_Audit
begin

thm Core_Expression_Lemmas.expression_eqI
thm Core_Expression_Lemmas.bind_assoc
thm Core_Expression_Lemmas.evaluate_literal
thm Core_Expression_Lemmas.evaluate_panic

lemma isolation_intro_registry_rule [micro_rust_intros]:
  shows True
  by simp

lemma isolation_elim_registry_rule [micro_rust_elims]:
  assumes False
  shows P
  using assms by simp

lemma isolation_ssa_registry_rule [micro_rust_ssa]:
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
      if condition then () else error ("direct lemma compatibility: " ^ message)
  in
    val _ = assert "micro_rust_intros remains writable"
      (member \<^named_theorems>\<open>micro_rust_intros\<close>
        (theorem "isolation_intro_registry_rule"))
    val _ = assert "micro_rust_elims remains writable"
      (member \<^named_theorems>\<open>micro_rust_elims\<close>
        (theorem "isolation_elim_registry_rule"))
    val _ = assert "micro_rust_ssa remains writable"
      (member \<^named_theorems>\<open>micro_rust_ssa\<close>
        (theorem "isolation_ssa_registry_rule"))
  end
\<close>

end
