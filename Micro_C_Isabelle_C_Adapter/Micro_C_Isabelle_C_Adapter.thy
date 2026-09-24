(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Micro_C_Isabelle_C_Adapter
  imports
    "Isabelle_C.C_Main"
begin

section \<open>Isabelle/C adapter baseline\<close>

text \<open>
This session is the sole boundary for importing Isabelle/C. The baseline checks only that the
pinned and compatibility-patched frontend parses representative complete C translation units.
It deliberately exposes no C AST traversal, scalar semantics, or lowering API yet.
\<close>

C \<open>
int main(void) { return 0; }
\<close>

C \<open>
unsigned long long baseline_identity(unsigned long long value) {
  return value;
}
\<close>

end
