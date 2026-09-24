(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Neutral_Lemmas_Isolation
  imports
    Shallow_Computation.Core_Expression_Lemmas
    Dependency_Audit
begin

thm Core_Expression_Lemmas.expression_eqI
thm Core_Expression_Lemmas.bind_assoc
thm Core_Expression_Lemmas.sequence_assoc
thm Core_Expression_Lemmas.get_merge
thm Core_Expression_Lemmas.call_literal
thm Core_Expression_Lemmas.abort_sequence_zero

lemma isolation_neutral_lemma_simp [shallow_computation_simps]:
  shows \<open>id x = x\<close>
  by simp

lemma isolation_neutral_lemma_intro [shallow_computation_intros]:
  shows True
  by simp

lemma isolation_neutral_lemma_elim [shallow_computation_elims]:
  assumes False
  shows P
  using assms by simp

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then () else error ("neutral lemma isolation: " ^ message)
  in
    val _ =
      Language_Isolation_Dependency_Audit.assert_context
        "Shallow_Computation.Core_Expression_Lemmas"
        ["Micro_Rust_Parsing_Legacy_Frontend",
         "Micro_Rust_Parser_Impl",
         "Shallow_Micro_Rust_Base",
         "Shallow_Micro_Rust",
         "Micro_C_Isabelle_C_Adapter",
         "Isabelle_C",
         "C"]
        ctxt
    val _ = assert "legacy introduction registry leaked"
      (not (can (Proof_Context.get_thms ctxt) "micro_rust_intros"))
    val _ = assert "panic-specific lemma leaked"
      (not (can (Proof_Context.get_thm ctxt) "Core_Expression_Lemmas.evaluate_panic"))
  end
\<close>

end
