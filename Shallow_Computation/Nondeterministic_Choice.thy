(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Nondeterministic_Choice
  imports Core_Expression
begin

section\<open>Language-neutral nondeterministic choice prompts\<close>

text\<open>
Shallow computations represent externally resolved choices by yielding a distinguished
prompt and inspecting the response.  Languages choose their own prompt and response
datatypes and instantiate the following interfaces; the computation combinators do not
depend on any language profile.
\<close>

class nondeterministic_prompt =
  fixes nondeterministic_choice_prompt :: \<open>'a\<close>
    and transparent_prompt :: \<open>'a \<Rightarrow> bool\<close>
  assumes nondeterministic_choice_prompt_not_transparent [simp]:
    \<open>\<not> transparent_prompt nondeterministic_choice_prompt\<close>

class nondeterministic_response =
  fixes nondeterministic_left_response :: \<open>'a\<close>
    and nondeterministic_right_response :: \<open>'a\<close>
    and transparent_response :: \<open>'a\<close>
  assumes nondeterministic_responses_distinct:
    \<open>nondeterministic_left_response \<noteq> nondeterministic_right_response\<close>

definition nondet_choice ::
  \<open>('s, 'v, 'r, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response) expression \<Rightarrow>
   ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  where [shallow_computation_simps]:
  \<open>nondet_choice l r \<equiv>
     bind (yield nondeterministic_choice_prompt) (\<lambda>response.
       if response = nondeterministic_left_response then l else r)\<close>

definition bind2_unseq ::
  \<open>('arg0 \<Rightarrow> 'arg1 \<Rightarrow>
      ('s, 'v, 'c, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response) expression) \<Rightarrow>
   ('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close>
  where [shallow_computation_simps]:
  \<open>bind2_unseq f e0 e1 \<equiv>
     nondet_choice
       (bind e0 (\<lambda>v0. bind e1 (\<lambda>v1. f v0 v1)))
       (bind e1 (\<lambda>v1. bind e0 (\<lambda>v0. f v0 v1)))\<close>

definition is_nondet_order_yield_handler ::
  \<open>('s, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response)
      yield_handler_nondet_basic \<Rightarrow> bool\<close>
  where
  \<open>is_nondet_order_yield_handler handler \<equiv>
     \<forall>\<sigma>. handler nondeterministic_choice_prompt \<sigma> =
       {YieldContinue (nondeterministic_left_response, \<sigma>),
        YieldContinue (nondeterministic_right_response, \<sigma>)}\<close>

definition is_transparent_yield_handler ::
  \<open>('s, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response)
      yield_handler_nondet_basic \<Rightarrow> bool\<close>
  where
  \<open>is_transparent_yield_handler handler \<equiv>
     \<forall>\<sigma> prompt. transparent_prompt prompt \<longrightarrow>
       handler prompt \<sigma> = {YieldContinue (transparent_response, \<sigma>)}\<close>

end
