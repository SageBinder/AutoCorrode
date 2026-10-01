(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Concurrent_B
  imports Micro_C_Parsing_Frontend.C_Translation
begin

c_translate \<open>
int concurrent_right(int y) {
  return 1 + y;
}
\<close>

thm c_concurrent_right_def

end
