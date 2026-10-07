(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Reference_Interface
  imports
    State_References
    Shallow_Computation.Core_Expression
begin

section\<open>Reference-operation vocabulary\<close>

consts
  store_update_const :: \<open>('a, 'b, 'v) State_References.ref \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
  store_reference_const :: \<open>'v \<Rightarrow> ('s, ('a, 'b, 'v) State_References.ref, 'abort, 'i, 'o) function_body\<close>
  store_dereference_const :: \<open>'a \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close>

end
