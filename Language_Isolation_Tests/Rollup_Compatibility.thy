(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Rollup_Compatibility
  imports
    Shallow_Micro_Rust.Shallow_Micro_Rust
    Dependency_Audit
begin

term Core_Expression.bind
thm Core_Expression.bind.simps
thm Core_Expression_Lemmas.bind_assoc
thm Eval.eval_action_bind
thm Pullback.expression_pull_back_bind

end
