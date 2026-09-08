(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Result_Type
  imports Core_Expression Bool_Type Misc.Result
begin
(*>*)

section\<open>Core material related to the \<^emph>\<open>Result\<close> type\<close>

text\<open>This is an embedding of the \<^verbatim>\<open>Result::Ok\<close> constructor of Rust, using \<^term>\<open>Inr\<close> as the
underlying representation in HOL:\<close>

definition ok :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, ('v, 'e) result, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>ok \<equiv> bindlift1 Ok\<close>

text\<open>This is an embedding of the \<^verbatim>\<open>Result::Err\<close> constructor of Rust, using \<^term>\<open>Inl\<close> as the
underlying representation in HOL:\<close>

definition err :: \<open>('s, 'e, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, ('v,'e) result, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>err \<equiv> bindlift1 Err\<close>

definition propagate_result :: \<open>('s, ('a, 'e) result, ('r, 'e) result, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'a, ('r, 'e) result, 'abort, 'i, 'o) expression\<close> where
  \<open>propagate_result expr \<equiv> bind expr (\<lambda>x.
     case x of
       Err e \<Rightarrow> return_func (literal (Err e))
     | Ok v  \<Rightarrow> literal v)\<close>

(*<*)
end
(*>*)