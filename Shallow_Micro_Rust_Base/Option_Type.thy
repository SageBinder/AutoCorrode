(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Option_Type
  imports Core_Expression Bool_Type
begin
(*>*)

section\<open>The \<^emph>\<open>Option\<close> type\<close>

subsection\<open>Core material related to the \<^emph>\<open>Option\<close> type\<close>

text\<open>This is the embedding of the \<^emph>\<open>Some\<close> constructor.  Note that if the argument panics, or
returns, or similar, then the entire expression does, too.\<close>
definition some :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>some \<equiv> bindlift1 Some\<close>

text\<open>This is the embedding of the \<^emph>\<open>None\<close> constructor.\<close>
definition none :: \<open>('s, 'v option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>none \<equiv> literal None\<close>

text\<open>This is an internal definition. User-level uRust code should use the \<^emph>\<open>function\<close> \<^verbatim>\<open>unwrap()\<close>
from the Micro Rust Standard Library instead.\<close>
definition option_unwrap_expr :: \<open>String.literal \<Rightarrow> 'v option \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>option_unwrap_expr msg v_opt \<equiv> 
     case v_opt of 
       Some v \<Rightarrow> literal v
     | None \<Rightarrow> panic msg\<close>

definition propagate_option :: \<open>('s, 'v option, 'r option, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'r option, 'abort, 'i, 'o) expression\<close> where
  \<open>propagate_option expr \<equiv> bind expr (\<lambda>x.
     case x of
       None   \<Rightarrow> return_func (literal None)
     | Some v \<Rightarrow> literal v)\<close>

(*<*)
end
(*>*)