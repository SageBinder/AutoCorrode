(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Micro_C_Isabelle_C_Adapter
  imports
    "Isabelle_C.C_Main"
begin

section \<open>Isabelle/C adapter\<close>

text \<open>
This theory is the sole Isabelle/C import and parser boundary.  The adapter deliberately exposes
Isabelle/C's translation-unit AST without normalizing, elaborating, or rejecting C constructs.
It additionally retains the original source for positioned diagnostics in later frontend passes.
\<close>

ML_file \<open>adapter.ML\<close>

end
