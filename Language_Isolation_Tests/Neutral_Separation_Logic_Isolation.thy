(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Neutral_Separation_Logic_Isolation
  imports
    Shallow_Separation_Logic.Shallow_Separation_Logic
    Dependency_Audit
begin

term striple
term sstriple
term make_function_contract
thm striple_literal
thm sstriple_literalI
thm wp_literal

ML_val \<open>
  Language_Isolation_Dependency_Audit.assert_context
    "Shallow_Separation_Logic"
    ["Micro_Rust_Parsing_Legacy_Frontend",
     "Micro_Rust_Parser_Impl",
     "Shallow_Micro_Rust_Base",
     "Shallow_Micro_Rust",
     "Micro_C_Isabelle_C_Adapter",
     "Micro_C_Parsing_Frontend",
     "Shallow_Micro_C",
     "Isabelle_C",
     "C"]
    \<^context>
\<close>

end
