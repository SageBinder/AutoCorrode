(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Neutral_State_Logic_Isolation
  imports
    Shallow_State_Logic.Shallow_State_Logic
    Dependency_Audit
begin

term State_References.make_untyped_ref
term store_reference_const
term reference_contract_pre
term reference_triple

ML_val \<open>
  Language_Isolation_Dependency_Audit.assert_context
    "Shallow_State_Logic"
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
