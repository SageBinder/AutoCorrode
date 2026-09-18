(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Neutral_Core_Isolation
  imports
    Shallow_Computation.Shallow_Computation
    Dependency_Audit
begin

term Core_Expression.Expression
term Core_Expression.bind
thm Core_Expression.bind.simps
thm Core_Expression.function_body_simp

lemma isolation_neutral_simp_rule [shallow_computation_simps]:
  shows \<open>id x = x\<close>
  by simp

lemma isolation_neutral_intro_rule [shallow_computation_intros]:
  shows True
  by simp

lemma isolation_neutral_elim_rule [shallow_computation_elims]:
  assumes False
  shows P
  using assms by simp

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun assert message condition =
      if condition then () else error ("neutral core isolation: " ^ message)
    fun absent_fact name = not (can (Proof_Context.get_thms ctxt) name)
  in
    val _ =
      Language_Isolation_Dependency_Audit.assert_context
        "Shallow_Computation"
        ["Micro_Rust_Parsing_Legacy_Frontend",
         "Micro_Rust_Parser_Impl",
         "Shallow_Micro_Rust_Base",
         "Shallow_Micro_Rust",
         "Isabelle_C",
         "C"]
        ctxt
    val _ = assert "legacy simplification registry leaked"
      (absent_fact "micro_rust_simps")
    val _ = assert "panic profile helper leaked"
      (not (Sign.declared_const thy "Core_Expression.panic"))
    val _ = assert "unimplemented profile helper leaked"
      (not (Sign.declared_const thy "Core_Expression.unimplemented"))
    val _ = assert "binary-operation profile synonym leaked"
      (not (Sign.declared_tyname thy "Core_Expression.urust_binop"))
  end
\<close>

end
