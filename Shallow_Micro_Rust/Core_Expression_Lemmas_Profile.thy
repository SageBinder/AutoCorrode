(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Core_Expression_Lemmas_Profile
  imports
    Shallow_Computation.Core_Expression_Lemmas
    Core_Expression_Profile
begin

named_theorems micro_rust_intros
named_theorems micro_rust_elims
named_theorems micro_rust_ssa

declare shallow_computation_simps[micro_rust_simps]
declare shallow_computation_intros[micro_rust_intros]
declare shallow_computation_elims[micro_rust_elims]

setup \<open>Sign.root_path #> Sign.add_path "Core_Expression_Lemmas"\<close>

lemma evaluate_panicE [micro_rust_elims]:
  assumes \<open>evaluate (panic m) \<sigma> = k\<close>
    and \<open>k = Abort (Panic m) \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (auto simp: evaluate_def abort_def)

lemma evaluate_panic [micro_rust_simps]:
  shows \<open>evaluate (panic msg) \<sigma> = Abort (Panic msg) \<sigma>\<close>
  by (simp add: Core_Expression_Lemmas.evaluate_abort)

lemma panic_sequence_zero [micro_rust_simps]:
  fixes msg :: \<open>String.literal\<close>
  shows \<open>sequence (panic msg) e = panic msg\<close>
  by (simp only: Core_Expression_Lemmas.abort_sequence_zero)

setup \<open>Sign.local_path\<close>

end
