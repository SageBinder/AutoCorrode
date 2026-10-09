(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory References
  imports
    Shallow_Reference_Logic.Expression_References
    Shallow_Micro_Rust.Prompts_And_Responses
begin

locale rust_reference =
  Expression_References.reference reference_types update_raw_fun
    dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store
    new_gref_can_store can_alloc_reference
  for reference_types ::
      \<open>'s::sepalg \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow>
        'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
    and update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw'
      gref_can_store new_gref_can_store can_alloc_reference

end
