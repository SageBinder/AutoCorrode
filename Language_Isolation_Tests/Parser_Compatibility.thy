(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Compatibility
  imports
    Shallow_Micro_Rust.Eval_Profile
    Dependency_Audit
begin

declare [[urust_conformance = true]]

urust_expr [attrs = [micro_rust_simps]] isolation_parser_literal
  (x)
  \<open> x \<close>

lemma isolation_parser_literal_evaluates:
  shows \<open>evaluate (isolation_parser_literal x) \<sigma> = Success x \<sigma>\<close>
  by (simp add: isolation_parser_literal_def micro_rust_simps)

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val simps = Named_Theorems.get ctxt \<^named_theorems>\<open>micro_rust_simps\<close>
    val definition = Proof_Context.get_thm ctxt "isolation_parser_literal_def"
  in
    val _ =
      if exists (Thm.equiv_thm thy o pair definition) simps then ()
      else error "parser compatibility: generated definition was not added to micro_rust_simps"
  end
\<close>

end
