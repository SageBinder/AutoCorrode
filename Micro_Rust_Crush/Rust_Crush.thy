(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Rust_Crush
  imports
    Crush.Crush
    Shallow_Micro_Rust_Logic.Rust_Weakest_Precondition
    Micro_Rust_Interfaces_Core.References
begin

text \<open>
This theory is the profile boundary between neutral Crush automation and Micro Rust.
It reattaches Rust expression simplification, SSA normalization, and generated-record focus
rules to the corresponding neutral Crush registries.
\<close>

setup \<open>Crush_Expression_Simps.register
  \<^named_theorems>\<open>micro_rust_simps\<close>\<close>
setup \<open>Crush_Focus_Intros.register
  \<^named_theorems>\<open>micro_rust_record_intros\<close>\<close>

lemma rust_crush_normalization_control:
  \<open>MICRO_RUST_SSA_CONTROL e \<equiv> crush_expression_normalization_control e\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def crush_expression_normalization_control_def)

text \<open>
Rust's established SSA rules use a Rust-local control wrapper. The neutral normalizer uses its
own wrapper, so registration first rewrites the existing rule collection to the neutral wrapper.
The transformed rules are registered anonymously; no compatibility theorem aliases are created.
\<close>

setup \<open>
  fn thy =>
    let
      val ctxt = Proof_Context.init_global thy
      val replace_control =
        Conv.bottom_conv
          (K (Conv.try_conv
            (Conv.rewr_conv @{thm rust_crush_normalization_control}))) ctxt
      val rules =
        Named_Theorems.get ctxt \<^named_theorems>\<open>micro_rust_ssa\<close>
        |> map (Conv.fconv_rule replace_control)
      fun register rule =
        Context.theory_map
          (Named_Theorems.add_thm
            \<^named_theorems>\<open>crush_expression_normalization\<close> rule)
    in
      fold register rules thy
    end
\<close>

end
