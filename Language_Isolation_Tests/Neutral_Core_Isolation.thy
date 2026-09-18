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

ML_val\<open>
  Language_Isolation_Dependency_Audit.assert_context
    "Shallow_Computation"
    ["Micro_Rust_Parsing_Legacy_Frontend",
     "Micro_Rust_Parser_Impl",
     "Shallow_Micro_Rust_Base",
     "Shallow_Micro_Rust",
     "Isabelle_C",
     "C"]
    \<^context>
\<close>

end
