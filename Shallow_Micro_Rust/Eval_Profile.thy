(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Eval_Profile
  imports
    Shallow_Computation.Eval
    Core_Expression_Lemmas_Profile
    "HOL-Library.Datatype_Records"
    Numeric_Types_Lemmas
    Prompts_And_Responses
begin

named_theorems urust_eval_predicate_defs
named_theorems urust_eval_action_via_predicate
named_theorems urust_eval_predicate_via_action
named_theorems urust_eval_predicate_simps
named_theorems urust_eval_action_simps

declare shallow_computation_eval_predicate_defs[urust_eval_predicate_defs]
declare shallow_computation_eval_action_via_predicate[urust_eval_action_via_predicate]
declare shallow_computation_eval_predicate_via_action[urust_eval_predicate_via_action]
declare shallow_computation_eval_predicate_simps[urust_eval_predicate_simps]
declare shallow_computation_eval_action_simps[urust_eval_action_simps]

setup \<open>Sign.root_path #> Sign.add_path "Eval"\<close>

text\<open>The assert operator\<close>

lemma urust_eval_action_assert [urust_eval_action_simps]:
  shows \<open>(\<Gamma>, assert_val r) \<diamondop>\<^sub>a \<sigma> = (if r then {} else {(AssertionFailed, \<sigma>)})\<close>
    and \<open>(\<Gamma>, assert_val r) \<diamondop>\<^sub>v \<sigma> = (if r then {((),\<sigma>)} else {})\<close>
    and \<open>(\<Gamma>, assert_val r) \<diamondop>\<^sub>r \<sigma> = {}\<close>
by (auto simp add: assert_val_def urust_eval_action_simps)

corollary urust_eval_predicate_assert [urust_eval_predicate_simps]:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,assert_val r\<rangle> (v,\<sigma>') \<longleftrightarrow> r \<and> \<sigma>' = \<sigma> \<and> v = ()\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,assert_val r\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,assert_val r\<rangle> (a, \<sigma>') \<longleftrightarrow> \<not>r \<and> a = AssertionFailed \<and> \<sigma>=\<sigma>'\<close>
by (auto simp add: urust_eval_action_assert urust_eval_predicate_via_action)

text\<open>The pause operator\<close>

lemma urust_eval_action_pause [urust_eval_action_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>(\<Gamma>, pause) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      and \<open>(\<Gamma>, pause) \<diamondop>\<^sub>v \<sigma> = {((), \<sigma>)}\<close>
      and \<open>(\<Gamma>, pause) \<diamondop>\<^sub>r \<sigma> = {}\<close>
using assms by (auto simp add: pause_def urust_eval_action_via_predicate urust_eval_predicate_defs
  is_log_transparent_yield_handler_def deep_evaluates_nondet_basic.simps evaluate_def literal_def)

lemma urust_eval_predicate_pause [urust_eval_predicate_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, pause\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, pause\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma>' = \<sigma>\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, pause\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
using assms by (simp add: urust_eval_predicate_via_action urust_eval_action_simps)+

text\<open>The log operator\<close>

lemma urust_eval_action_log [urust_eval_action_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>(\<Gamma>, log p l) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      and \<open>(\<Gamma>, log p l) \<diamondop>\<^sub>v \<sigma> = {((), \<sigma>)}\<close>
      and \<open>(\<Gamma>, log p l) \<diamondop>\<^sub>r \<sigma> = {}\<close>
using assms by (auto simp add: log_def urust_eval_action_via_predicate urust_eval_predicate_defs
  is_log_transparent_yield_handler_def deep_evaluates_nondet_basic.simps evaluate_def literal_def)

lemma urust_eval_predicate_log [urust_eval_predicate_simps]:
  assumes \<open>is_log_transparent_yield_handler \<Gamma>\<close>
    shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, log p l\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, log p l\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma>' = \<sigma>\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, log p l\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
using assms by (simp add: urust_eval_predicate_via_action urust_eval_action_simps)+

text\<open>The fatal operator\<close>

lemma urust_eval_action_fatal [urust_eval_action_simps]:
  assumes \<open>is_aborting_yield_handler \<Gamma>\<close>
    shows \<open>(\<Gamma>, fatal msg) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      and \<open>(\<Gamma>, fatal msg) \<diamondop>\<^sub>v \<sigma> = {}\<close>
      and \<open>(\<Gamma>, fatal msg) \<diamondop>\<^sub>r \<sigma> = {}\<close>
using assms by (auto simp add: pause_def urust_eval_action_via_predicate urust_eval_predicate_defs
  deep_evaluates_nondet_basic.simps evaluate_def literal_def is_aborting_yield_handler_def fatal_def)

lemma urust_eval_predicate_fatal [urust_eval_predicate_simps]:
  assumes \<open>is_aborting_yield_handler \<Gamma>\<close>
    shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, fatal msg\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, fatal msg\<rangle> (v, \<sigma>') \<longleftrightarrow> False\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, fatal msg\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
  using assms by (simp add: urust_eval_predicate_via_action urust_eval_action_simps)+

text\<open>Conditionals\<close>

corollary urust_eval_action_two_armed_conditional [urust_eval_action_simps]:
  shows \<open>(\<Gamma>,two_armed_conditional cond then_branch else_branch) \<diamondop>\<^sub>v \<sigma> =
            (\<Union>(v, \<sigma>') \<in> (\<Gamma>,cond) \<diamondop>\<^sub>v \<sigma>. if v then (\<Gamma>,then_branch) \<diamondop>\<^sub>v \<sigma>'
                                     else (\<Gamma>, else_branch) \<diamondop>\<^sub>v \<sigma>')\<close> (is ?g1)
    and \<open>(\<Gamma>,two_armed_conditional cond then_branch else_branch) \<diamondop>\<^sub>r \<sigma> =
            ((\<Gamma>,cond) \<diamondop>\<^sub>r \<sigma>) \<union>
            (\<Union>(v, \<sigma>') \<in> (\<Gamma>,cond) \<diamondop>\<^sub>v \<sigma>. if v then (\<Gamma>,then_branch) \<diamondop>\<^sub>r \<sigma>'
                                     else (\<Gamma>, else_branch) \<diamondop>\<^sub>r \<sigma>')\<close> (is ?g2)
    and \<open>(\<Gamma>,two_armed_conditional cond then_branch else_branch) \<diamondop>\<^sub>a \<sigma> =
            ((\<Gamma>,cond) \<diamondop>\<^sub>a \<sigma>) \<union>
            (\<Union>(v, \<sigma>') \<in> (\<Gamma>,cond) \<diamondop>\<^sub>v \<sigma>. if v then (\<Gamma>,then_branch) \<diamondop>\<^sub>a \<sigma>'
                                     else (\<Gamma>, else_branch) \<diamondop>\<^sub>a \<sigma>')\<close> (is ?g3)
proof -
  have A: \<open>\<And>x a b. (case x of (v, t) \<Rightarrow> if v then a t else b t)
              = (case x of (True, t) \<Rightarrow> a t | (False, t) \<Rightarrow> b t)\<close>
    by auto
  have E1: \<open>\<And>\<Gamma> \<sigma> v a b. ((\<Gamma>,(if v then a else b)) \<diamondop>\<^sub>v \<sigma>) =
            (if v then ((\<Gamma>,a) \<diamondop>\<^sub>v \<sigma>) else ((\<Gamma>,b) \<diamondop>\<^sub>v \<sigma>))\<close> by auto
  have E2: \<open>\<And>\<Gamma> \<sigma> v a b. ((\<Gamma>,(if v then a else b)) \<diamondop>\<^sub>r \<sigma>) =
            (if v then ((\<Gamma>,a) \<diamondop>\<^sub>r \<sigma>) else ((\<Gamma>,b) \<diamondop>\<^sub>r \<sigma>))\<close> by auto
  have E3: \<open>\<And>\<Gamma> \<sigma> v a b. ((\<Gamma>,(if v then a else b)) \<diamondop>\<^sub>a \<sigma>) =
            (if v then ((\<Gamma>,a) \<diamondop>\<^sub>a \<sigma>) else ((\<Gamma>,b) \<diamondop>\<^sub>a \<sigma>))\<close> by auto
  show ?g1 ?g2 ?g3 by (auto simp add: two_armed_conditional_def
    urust_eval_action_bind E1 E2 E3)
qed

corollary urust_eval_predicate_two_armed_conditional [urust_eval_predicate_simps]:
  shows \<open>(\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,two_armed_conditional cond then_branch else_branch\<rangle> (v,\<sigma>'')) =
          ((\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (True,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>v \<langle>\<Gamma>,then_branch\<rangle> (v,\<sigma>''))) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (False,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>v \<langle>\<Gamma>,else_branch\<rangle> (v,\<sigma>''))))\<close> (is ?g1)
    and \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,two_armed_conditional cond then_branch else_branch\<rangle> (r,\<sigma>'')) =
            ((\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,cond\<rangle> (r, \<sigma>'')) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (True,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>r \<langle>\<Gamma>,then_branch\<rangle> (r,\<sigma>''))) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (False,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>r \<langle>\<Gamma>,else_branch\<rangle> (r,\<sigma>''))))\<close> (is ?g2)
    and \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,two_armed_conditional cond then_branch else_branch\<rangle> (a, \<sigma>'')) =
          ((\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,cond\<rangle> (a, \<sigma>'')) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (True,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>a \<langle>\<Gamma>,then_branch\<rangle> (a, \<sigma>''))) \<or>
          (\<exists>\<sigma>'. (\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,cond\<rangle> (False,\<sigma>')) \<and> (\<sigma>' \<leadsto>\<^sub>a \<langle>\<Gamma>,else_branch\<rangle> (a, \<sigma>''))))\<close> (is ?g3)
proof -
  show ?g1
    by (auto simp add: urust_eval_action_two_armed_conditional urust_eval_predicate_via_action,
      metis (full_types), force, force)
  show ?g2
    by (auto simp add: urust_eval_action_two_armed_conditional urust_eval_predicate_via_action,
      metis (full_types), force, force)
  show ?g3
    by (auto simp add: urust_eval_action_two_armed_conditional urust_eval_predicate_via_action,
      metis (full_types), force, force)
qed

text\<open>Numeric operators\<close>

lemma urust_eval_action_add_no_wrap [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, word_add_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) =
            (if (unat x + unat y < 2 ^ LENGTH('l)) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    and \<open>((\<Gamma>, word_add_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) =
            (if (unat x + unat y < 2 ^ LENGTH('l)) then {(x + y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, word_add_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
  by (auto simp add: word_add_no_wrap_def urust_eval_action_bind micro_rust_simps
    urust_eval_action_literal urust_eval_action_abort word_add_no_wrap_core_def Let_def
    word_add_no_wrap_as_urust_def urust_eval_action_call word_op_no_wrap_pure_def option_unwrap_expr_def)

corollary urust_eval_predicate_add_no_wrap [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, word_add_no_wrap (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat x + unat y < 2^LENGTH('l)) \<and> \<sigma> = \<sigma>' \<and> v = x + y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, word_add_no_wrap (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, word_add_no_wrap (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat x + unat y \<ge> 2^LENGTH('l)) \<and> a = Panic overflow_err_msg \<and> \<sigma> = \<sigma>'\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_add_no_wrap)

lemma urust_eval_action_mul_no_wrap [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, word_mul_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) =
            (if (unat x * unat y < 2 ^ LENGTH('l)) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    and \<open>((\<Gamma>, word_mul_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) =
            (if (unat x * unat y < 2 ^ LENGTH('l)) then {(x * y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, word_mul_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp add: word_mul_no_wrap_def urust_eval_action_bind micro_rust_simps
  urust_eval_action_literal urust_eval_action_abort word_mul_no_wrap_core_def Let_def
  word_mul_no_wrap_as_urust_def urust_eval_action_call word_op_no_wrap_pure_def option_unwrap_expr_def)

corollary urust_eval_predicate_mul_no_wrap [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, word_mul_no_wrap (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat x * unat y < 2^LENGTH('l)) \<and> \<sigma> = \<sigma>' \<and> v = x * y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, word_mul_no_wrap (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, word_mul_no_wrap (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat x * unat y \<ge> 2^LENGTH('l)) \<and> \<sigma> = \<sigma>' \<and> a = Panic overflow_err_msg\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_mul_no_wrap)

lemma urust_eval_action_sub_no_wrap [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, word_minus_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) =
            (if ( unat y \<le> unat x) then {} else { (Panic overflow_err_msg, \<sigma>) })\<close>
    and \<open>((\<Gamma>, word_minus_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) =
            (if ( unat y \<le> unat x) then {(x - y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, word_minus_no_wrap (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp flip: word_le_nat_alt simp add: word_minus_no_wrap_def urust_eval_action_bind
  micro_rust_simps urust_eval_action_literal urust_eval_action_abort word_minus_no_wrap_core_def
  word_minus_no_wrap_as_urust_def urust_eval_action_call word_op_no_wrap_pure_def
  word_minus_no_wrap_pure_def option_unwrap_expr_def Let_def)

corollary urust_eval_predicate_sub_no_wrap [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, word_minus_no_wrap (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat y \<le> unat x) \<and> \<sigma> = \<sigma>' \<and> v = x - y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, word_minus_no_wrap (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, word_minus_no_wrap (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y > unat x) \<and> a = Panic overflow_err_msg \<and> \<sigma> = \<sigma>'\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_sub_no_wrap)

lemma urust_eval_action_div [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, word_udiv (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) =
            (if ( unat y \<noteq> 0) then {} else { (Panic (String.implode ''division by zero''), \<sigma>) })\<close>
    and \<open>((\<Gamma>, word_udiv (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) =
            (if ( unat y \<noteq> 0) then {(x div y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, word_udiv (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp add: unat_gt_0 word_div_def urust_eval_action_bind micro_rust_simps
  urust_eval_action_literal urust_eval_action_abort word_udiv_core_def word_udiv_def
  urust_eval_action_call)

corollary urust_eval_predicate_div [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, word_udiv (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat y \<noteq> 0) \<and> \<sigma> = \<sigma>' \<and> v = x div y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, word_udiv (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, word_udiv (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y = 0) \<and> \<sigma> = \<sigma>' \<and> a = Panic (String.implode ''division by zero'')\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_div)

lemma urust_eval_action_mod [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, word_umod (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) =
            (if ( unat y \<noteq> 0) then {} else { (Panic (String.implode ''division by zero''), \<sigma>) })\<close>
    and \<open>((\<Gamma>, word_umod (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) =
            (if ( unat y \<noteq> 0) then {(x mod y, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, word_umod (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp add: unat_gt_0 word_mod_def urust_eval_action_bind micro_rust_simps
  urust_eval_action_literal urust_eval_action_abort word_umod_core_def word_umod_def
  urust_eval_action_call)

corollary urust_eval_predicate_mod [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, word_umod (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> (unat y \<noteq> 0) \<and> \<sigma> = \<sigma>' \<and> v = x mod y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, word_umod (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, word_umod (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y = 0) \<and> a = Panic (String.implode ''division by zero'') \<and> \<sigma> = \<sigma>'\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_mod)

lemma urust_eval_action_shift_left [urust_eval_action_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>((\<Gamma>, word_shift_left_shift64 (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) =
            (if unat y < LENGTH('l0) then {} else {(Panic overflow_err_msg, \<sigma>)})\<close>
    and \<open>((\<Gamma>, word_shift_left_shift64 (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) =
            (if unat y < LENGTH('l0) then {(push_bit (unat y) x, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, word_shift_left_shift64 (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp flip: word_le_nat_alt simp add: word_shift_left_pure_def urust_eval_action_bind
  micro_rust_simps urust_eval_action_literal urust_eval_action_abort word_shift_left_core_def
  word_shift_left_as_urust_def urust_eval_action_call word_shift_left_def
  word_shift_left_shift64_def option_unwrap_expr_def Let_def)

corollary urust_eval_predicate_shift_left [urust_eval_predicate_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, word_shift_left_shift64 (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow>
            unat y < LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> v = push_bit (unat y) x\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, word_shift_left_shift64 (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, word_shift_left_shift64 (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y \<ge> LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> a = Panic overflow_err_msg)\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_shift_left)

lemma urust_eval_action_shift_right [urust_eval_action_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>((\<Gamma>, word_shift_right_shift64 (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) =
            (if unat y < LENGTH('l0) then {} else {(Panic overflow_err_msg, \<sigma>)})\<close>
    and \<open>((\<Gamma>, word_shift_right_shift64 (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) =
            (if unat y < LENGTH('l0) then {(drop_bit (unat y) x, \<sigma>)} else {})\<close>
    and \<open>((\<Gamma>, word_shift_right_shift64 (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (auto simp flip: word_le_nat_alt simp add: word_shift_right_pure_def urust_eval_action_bind
  micro_rust_simps urust_eval_action_literal urust_eval_action_abort word_shift_right_core_def
  word_shift_right_as_urust_def urust_eval_action_call word_shift_right_def
  word_shift_right_shift64_def option_unwrap_expr_def Let_def)

corollary urust_eval_predicate_shift_right [urust_eval_predicate_simps]:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, word_shift_right_shift64 (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow>
            unat y < LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> v = drop_bit (unat y) x\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, word_shift_right_shift64 (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, word_shift_right_shift64 (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> (unat y \<ge> LENGTH('l0) \<and> \<sigma> = \<sigma>' \<and> a = Panic overflow_err_msg)\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_shift_right)

lemma urust_eval_action_xor [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, Numeric_Types.word_bitwise_xor (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_xor (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) = {(x XOR y, \<sigma>)}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_xor (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_xor [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, Numeric_Types.word_bitwise_xor (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = x XOR y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, Numeric_Types.word_bitwise_xor (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, Numeric_Types.word_bitwise_xor (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_xor)

lemma urust_eval_action_or [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, Numeric_Types.word_bitwise_or (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_or (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) = {(x OR y, \<sigma>)}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_or (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_or [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, Numeric_Types.word_bitwise_or (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = x OR y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, Numeric_Types.word_bitwise_or (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, Numeric_Types.word_bitwise_or (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_or)

lemma urust_eval_action_and [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, Numeric_Types.word_bitwise_and (literal x) (literal y)) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_and (literal x) (literal y)) \<diamondop>\<^sub>v \<sigma>) = {(x AND y, \<sigma>)}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_and (literal x) (literal y)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_and [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, Numeric_Types.word_bitwise_and (literal x) (literal y)\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = x AND y\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, Numeric_Types.word_bitwise_and (literal x) (literal y)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, Numeric_Types.word_bitwise_and (literal x) (literal y)\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_and)

lemma urust_eval_action_not [urust_eval_action_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>((\<Gamma>, Numeric_Types.word_bitwise_not (literal x)) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_not (literal x)) \<diamondop>\<^sub>v \<sigma>) = {(NOT x, \<sigma>)}\<close>
    and \<open>((\<Gamma>, Numeric_Types.word_bitwise_not (literal x)) \<diamondop>\<^sub>r \<sigma>) = {}\<close>
by (simp add: urust_eval_action_bind micro_rust_simps urust_eval_action_literal
  urust_eval_action_abort urust_eval_action_call)+

corollary urust_eval_predicate_not [urust_eval_predicate_simps]:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, Numeric_Types.word_bitwise_not (literal x)\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> = \<sigma>' \<and> v = NOT x\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>, Numeric_Types.word_bitwise_not (literal x)\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, Numeric_Types.word_bitwise_not (literal x)\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
by (auto simp add: urust_eval_predicate_via_action urust_eval_action_not)

setup \<open>Sign.local_path\<close>

end
