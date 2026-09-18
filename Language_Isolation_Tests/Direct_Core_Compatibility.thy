(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Direct_Core_Compatibility
  imports
    Shallow_Micro_Rust_Base.Basic_Case_Expression
    Shallow_Micro_Rust_Base.Core_Expression
    Dependency_Audit
begin

datatype isolation_choice =
    Isolation_None
  | Isolation_Some nat

definition isolation_choice_value :: \<open>isolation_choice \<Rightarrow> nat\<close> where
  \<open>isolation_choice_value value =
    (bcase value of
       Isolation_None \<Rightarrow> 0
     | Isolation_Some n \<Rightarrow> n)\<close>

lemma isolation_choice_value_some:
  shows \<open>isolation_choice_value (Isolation_Some n) = n\<close>
  by (simp add: isolation_choice_value_def)

term Core_Expression.Expression
term Core_Expression.Success
term Core_Expression.Return
term Core_Expression.Abort
term Core_Expression.Yield
term Core_Expression.bind
term Core_Expression.call_function_body
term Core_Expression.funcall16

thm Core_Expression.bind.simps
thm Core_Expression.call_function_body.simps
thm Core_Expression.function_body_simp

lemma isolation_core_registry_rule [micro_rust_simps]:
  shows \<open>id x = x\<close>
  by simp

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val simps = Named_Theorems.get ctxt \<^named_theorems>\<open>micro_rust_simps\<close>

    fun member thm = exists (Thm.equiv_thm thy o pair thm) simps
    fun theorem name = Proof_Context.get_thm ctxt name
    fun assert message condition =
      if condition then () else error ("direct core compatibility: " ^ message)
  in
    val _ = assert "function_body_simp is registered"
      (member (theorem "Core_Expression.function_body_simp"))
    val _ = assert "legacy simplification registry remains writable"
      (member (theorem "isolation_core_registry_rule"))
    val _ = @{const_name Core_Expression.bind}
    val _ = @{thm Core_Expression.bind.simps}
  end
\<close>

end
