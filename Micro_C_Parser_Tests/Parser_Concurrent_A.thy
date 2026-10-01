(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Concurrent_A
  imports Micro_C_Parsing_Frontend.C_Translation
begin

c_translate \<open>
int concurrent_left(int x) {
  return x + 1;
}
\<close>

thm c_concurrent_left_def

end
