(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Logging_Fixtures
  imports Micro_Rust_Std_Lib.StdLib_Logging
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open>Logging parser fixture\<close>

text\<open>
The dedicated parser reads logging macros directly from the neutral notation
registry supplied by the production standard library.
\<close>

end
