(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Micro_C_Isabelle_C_Adapter
  imports
    "Isabelle_C.C_Main"
begin

section \<open>Isabelle/C adapter\<close>

text \<open>
This theory is the sole Isabelle/C import and AST boundary. Parsing is followed immediately by
normalization into project-owned datatypes. No Isabelle/C parser environment, context, or AST
constructor crosses the public ML signature.
\<close>

ML_file \<open>adapter.ML\<close>

end
