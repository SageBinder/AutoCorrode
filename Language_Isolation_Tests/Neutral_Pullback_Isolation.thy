(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Neutral_Pullback_Isolation
  imports
    Shallow_Computation.Pullback
    Dependency_Audit
begin

term Pullback.expression_pull_back
term Pullback.function_pull_back
term Pullback.canonical_pull_back_yield_handler

thm Pullback.expression_pull_back_bind
thm Pullback.expression_pull_back_eval_value
thm Pullback.canonical_pull_back_yield_handler_is_lift
thm Pullback.canonical_pull_back_yield_handler_nondet_order_preserving
thm Pullback.canonical_pull_back_yield_handler_transparent_preserving

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then () else error ("neutral pullback isolation: " ^ message)
  in
    val _ =
      Language_Isolation_Dependency_Audit.assert_context
        "Shallow_Computation.Pullback"
        ["Micro_Rust_Parsing_Legacy_Frontend",
         "Micro_Rust_Parser_Impl",
         "Shallow_Micro_Rust_Base",
         "Shallow_Micro_Rust",
         "Micro_C_Isabelle_C_Adapter",
         "Isabelle_C",
         "C"]
        ctxt
    val _ = assert "log-policy pullback lemma leaked"
      (not (can (Proof_Context.get_thm ctxt)
        "Pullback.canonical_pull_back_yield_handler_log_preserving"))
  end
\<close>

end
