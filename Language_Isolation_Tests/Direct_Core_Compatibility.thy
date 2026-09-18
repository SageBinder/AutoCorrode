(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Direct_Core_Compatibility
  imports
    Shallow_Computation.Case_Term_Backend
    Shallow_Computation.Core_Expression
    Dependency_Audit
begin

text\<open>The neutral owner changes the session-qualified import path. The globally visible
declaration names remain unchanged, including generated equations and named-theorem
registrations.\<close>

ML_val\<open>
  val _ = Case_Term_Backend.case_nil
  val _ = Case_Term_Backend.make_case
\<close>

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
