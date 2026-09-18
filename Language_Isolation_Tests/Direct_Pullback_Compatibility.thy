(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Direct_Pullback_Compatibility
  imports
    Shallow_Micro_Rust.Pullback_Profile
    Dependency_Audit
begin

term Pullback.expression_pull_back
term Pullback.function_pull_back
term Pullback.canonical_pull_back_yield_handler

thm Pullback.expression_pull_back_bind
thm Pullback.expression_pull_back_eval_value
thm Pullback.canonical_pull_back_yield_handler_no_yield
thm Pullback.canonical_pull_back_yield_handler_log_preserving
thm Pullback.canonical_pull_back_yield_handler_nondet_order_preserving

end
