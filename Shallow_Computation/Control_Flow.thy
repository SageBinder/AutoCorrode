(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Control_Flow
  imports Core_Expression
begin

section\<open>Language-neutral control flow\<close>

definition two_armed_conditional ::
    \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
  where
    \<open>two_armed_conditional test this that \<equiv>
      bind test (\<lambda>condition. if condition then this else that)\<close>

abbreviation one_armed_conditional ::
    \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
  where
    \<open>one_armed_conditional test this \<equiv>
      two_armed_conditional test this skip\<close>

definition raw_for_loop ::
    \<open>'a list \<Rightarrow>
      ('a \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression) \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
  where
    \<open>raw_for_loop values body \<equiv>
      foldr sequence (List.map body values) skip\<close>

fun bounded_while ::
    \<open>nat \<Rightarrow>
      ('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
  where
    \<open>bounded_while 0 condition body = skip\<close>
  | \<open>bounded_while (Suc fuel) condition body =
      bind condition
        (\<lambda>continue.
          if continue
          then sequence body (bounded_while fuel condition body)
          else skip)\<close>

end
