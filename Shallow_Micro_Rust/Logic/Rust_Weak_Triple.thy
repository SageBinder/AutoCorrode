(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Rust_Weak_Triple
  imports
    Shallow_Separation_Logic.Weak_Triple
    Shallow_Micro_Rust.Shallow_Micro_Rust
begin

context sepalg begin

definition is_aborting_striple_context where
  \<open>is_aborting_striple_context \<Gamma> \<equiv> is_aborting_yield_handler (yh \<Gamma>)\<close>

lemma striple_assert_val:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> assert_val v \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
     (v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (\<not>v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
proof (cases v)
  case True
  then show ?thesis
    by (simp add: assert_val_def local.asepconj_comm striple_literal)
next
  case False
  show ?thesis
  proof -
    have \<open>\<phi> \<longlongrightarrow> UNIV \<star> \<theta> AssertionFailed\<close>
      if \<open>\<forall>\<sigma> \<pi>. ucincl \<pi> \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<star> \<pi> \<longrightarrow> \<sigma> \<Turnstile> \<theta> AssertionFailed \<star> \<pi>\<close>
      by (metis aentails_after_all_asepconjs aentails_def local.asepconj_comm that)
    moreover have \<open>\<sigma> \<Turnstile> \<theta> AssertionFailed \<star> \<pi>\<close>
      if \<open>\<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed\<close>
        and \<open>ucincl \<pi>\<close> \<open>\<sigma> \<Turnstile> \<phi> \<star> \<pi>\<close>
      for \<sigma> \<pi>
      using that by (metis aentailsE aentails_after_all_asepconjs local.asepconj_comm)
    ultimately show ?thesis
      using False by (auto simp add: striple_def atriple_def shallow_computation_eval_action_simps asepconj_False_True asepconj_simp)
  qed
qed

lemma striple_assert:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> assert (literal v) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
            (v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (\<not>v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
  by (simp add: assert_def micro_rust_simps striple_assert_val)

lemma striple_assert_eq:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> assert_eq (literal v) (literal w) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
            (v=w \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (v \<noteq> w \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
  by (simp add: assert_eq_def assert_eq_val_def micro_rust_simps striple_assert_val)

corollary striple_noneI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> none \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = None\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (unfold none_def, rule striple_literalI)

corollary striple_trueI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> true \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = True\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (unfold true_def, rule striple_literalI)

corollary striple_falseI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> false \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = False\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (unfold false_def, rule striple_literalI)

corollary striple_someI:
  notes asepconj_simp [simp]
  shows \<open>\<Gamma> ; \<top> \<turnstile> some (literal x) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rv. \<langle>rv = Some x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; simp add: eval_predicate_bind return_func_def micro_rust_simps some_def
  eval_predicate_return eval_predicate_literal apure_def atriple_post_true)

text\<open>Abort and panic terminate execution of the program:\<close>
lemma striple_panic:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> panic msg \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<theta> (Panic msg) \<star> \<top>)\<close>
  by (simp add: striple_abort)

text\<open>Pause / Breakpoint\<close>

lemma striple_pause:
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<top> \<turnstile> pause \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<top> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
using assms by (simp add: striple_def shallow_computation_eval_action_simps atriple_def)

lemma striple_pause':
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<phi> \<turnstile> pause \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> ())\<close>
using assms unfolding is_valid_striple_context_def
  apply (clarsimp simp add: striple_def shallow_computation_eval_action_simps atriple_def)
  using aentails_after_all_asepconjs
  apply (metis aentails_def local.asepconj_strengthenE local.ucincl_UNIV)
  done

text\<open>Various types of log events:\<close>

lemma striple_log:
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> log p l \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<top> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using assms by (simp add: striple_def shallow_computation_eval_action_simps atriple_def)

lemma striple_log':
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<phi> \<turnstile> log p l \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> ())\<close>
using assms
  apply (clarsimp simp add: striple_def shallow_computation_eval_action_simps atriple_def)
  using aentails_after_all_asepconjs
  apply (metis aentails_def local.asepconj_strengthenE local.ucincl_UNIV)
  done

text\<open>Fatal errors\<close>

lemma striple_fatal:
  assumes \<open>is_aborting_striple_context \<Gamma>\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<phi> \<turnstile> fatal msg \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
  using assms
  by (simp add: striple_def shallow_computation_eval_action_simps atriple_def is_aborting_striple_context_def)

lemma striple_word_add_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x + unat y < 2^(LENGTH('l))\<rangle> \<turnstile> word_add_no_wrap (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x + y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_add_no_wrap apure_def asepconj_simp
    atriple_post_true atriple_pre_false)

lemma striple_word_mul_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x * unat y < 2^(LENGTH('l))\<rangle> \<turnstile> word_mul_no_wrap (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x * y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_mul_no_wrap apure_def asepconj_simp
    atriple_post_true atriple_pre_false)

lemma striple_word_sub_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<le> x\<rangle> \<turnstile> word_minus_no_wrap (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x - y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_sub_no_wrap apure_def asepconj_simp
    atriple_post_true atriple_pre_false word_le_nat_alt)

lemma striple_word_udivI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> word_udiv (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x div y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro stripleI; clarsimp simp add: urust_eval_predicate_div apure_def asepconj_simp
    atriple_post_true unat_eq_zero atriple_pre_false)

lemma striple_word_umodI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> word_umod (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x mod y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_mod apure_def asepconj_simp
  atriple_post_true unat_eq_zero atriple_pre_false)

lemma striple_word_shift_leftI:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat y < LENGTH('l0)\<rangle> \<turnstile> word_shift_left_shift64 (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = push_bit (unat y) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: asepconj_simp urust_eval_predicate_shift_left apure_def
  atriple_post_true atriple_pre_false)

lemma striple_word_shift_rightI:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat y < LENGTH('l0)\<rangle> \<turnstile> word_shift_right_shift64 (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = drop_bit (unat y) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_shift_right apure_def asepconj_simp
  atriple_post_true atriple_pre_false)

lemma striple_bitwise_orI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_or (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x OR y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_or apure_def atriple_post_true)

lemma striple_bitwise_andI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_and (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x AND y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_and apure_def atriple_post_true)

lemma striple_bitwise_xorI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_xor (literal x) (literal y) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x XOR y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_xor apure_def atriple_post_true)

lemma striple_bitwise_notI:
  fixes x :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_not (literal x) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = NOT x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro stripleI; clarsimp simp add: urust_eval_predicate_not apure_def atriple_post_true)

lemma gather_spec':
    notes asepconj_simp [simp]
      and aentails_intro [intro]
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>i ls. i < length thunks \<Longrightarrow> length ls = i \<Longrightarrow> (\<Gamma> ; INV i ls \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV (i+1) (ls @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; INV 0 [] \<turnstile> gather' thunks acc \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. \<Squnion>rs'. \<langle>rs = acc @ rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
proof (induction thunks arbitrary: INV acc)
  case Nil
  have \<open>(\<Union>x. (if x = [] then UNIV else {}) \<star> INV 0 x) = (\<Union>x. (if x = [] then UNIV \<star> INV 0 x else {}))\<close>
    by (auto simp: split: if_splits)
  also have \<open>... = UNIV \<star> INV 0 []\<close> by auto
  finally show ?case
    by (auto simp: gather'_nil striple_def apure_def asepconj_swap_top eval_action_literal atriple_refl')
next
  case (Cons t thunks)
  then have first: \<open>\<Gamma> ; INV 0 [] \<turnstile> t \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV 1 [v]) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  have \<open>\<Gamma> ; INV 1 [r0] \<turnstile> gather' thunks (acc @ [r0]) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
        (\<lambda>rs. \<Squnion>rs'. \<langle>rs = (acc @ rs')\<rangle> \<star> INV (length (t # thunks)) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close> for r0
  proof -
    have \<open>\<Gamma> ; INV (i+1) (r0 # ls) \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV ((i+1)+1) ((r0 # ls) @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      if \<open>i < length thunks\<close> \<open>length ls = i\<close> for i and ls :: \<open>'v list\<close>
         using that Cons.prems[where i=\<open>i+1\<close> and ls=\<open>r0 # ls\<close>] by fastforce
    with Cons.IH[where INV=\<open>\<lambda>i ls. INV (i+1) (r0 # ls)\<close> and acc=\<open>acc @ [r0]\<close>]
    have \<open>\<Gamma> ; INV 1 [r0] \<turnstile> gather' thunks (acc @ [r0]) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
          (\<lambda>rs. \<Squnion>rs'. \<langle>rs = (acc @ (r0 # rs'))\<rangle> \<star> INV (length (t # thunks)) (r0 # rs')) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      by simp
    moreover have \<open>\<And>rs. (\<Squnion>rs'. \<langle>rs = (acc @ (r0 # rs'))\<rangle> \<star> INV (Suc (length thunks)) (r0 # rs')) \<longlongrightarrow>
          (\<Squnion>rs'. \<langle>rs = (acc @ rs')\<rangle> \<star> INV (Suc (length thunks)) rs')\<close>
      by blast
    ultimately show ?thesis
      by (meson aentails_refl local.aexists_entailsL local.aexists_entailsR local.striple_consequence)
  qed
  with first
    show ?case by (simp add: gather'_cons local.striple_bindI)
  qed

lemma gather_spec:
    notes aentails_intro [intro]
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>i ls. ucincl (INV i ls)\<close>
      and \<open>\<And>i ls. i < length thunks \<Longrightarrow> length ls = i \<Longrightarrow>
            \<Gamma> ; INV i ls \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV (i+1) (ls @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. INV (length thunks) rs) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  from assms and gather_spec'[where INV=INV and thunks=thunks] have
        \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. \<Squnion>rs'. \<langle>rs = [] @ rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    unfolding gather_def by blast
  from this have \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>rs. \<Squnion>rs'. \<langle>rs = rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  moreover have \<open>\<And>rs. (\<Squnion>rs'. \<langle>rs = rs'\<rangle> \<star> INV (length thunks) rs') \<longlongrightarrow> INV (length thunks) rs\<close>
    using assms by (simp add: asat_simp aentails_def)
  ultimately show ?thesis
    using striple_consequence by blast
qed

lemma striple_gather_framed:
    notes aentails_intro [intro]
    fixes thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>p r. ucincl (INV p r)\<close>
      and \<open>\<And>i res. i < length thunks \<Longrightarrow> length res = i \<Longrightarrow> \<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v. INV (i+1) (res @ [v])) \<bowtie> \<tau>  \<bowtie> \<theta>\<close>
  shows \<open>\<Gamma> ; INV 0 [] \<star> ((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a)) \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a)\<close>
  {
    fix i and res :: \<open>'v list\<close>
    assume \<open>i < length thunks\<close>
       and \<open>length res = i\<close>
    from this have \<open>\<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (i+1) (res @ [r])) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms \<open>i < length thunks\<close> by auto
    moreover have \<open>\<Gamma> ; INV i res \<star> ?pc \<turnstile>
          (thunks ! i) \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (i+1) (res @ [r]) \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using assms calculation by (intro striple_frame_rule, force)
    moreover have \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
    proof -
      have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    moreover have \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
    proof -
      have \<open>\<And>a. \<theta> a \<star> (\<Sqinter>a. \<theta> a \<Zsurj> \<chi> a) \<longlongrightarrow> \<chi> a\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    ultimately have \<open>\<Gamma> ; INV i res \<star> ?pc \<turnstile> thunks ! i \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (i+1) (res @ [r]) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      by - (rule striple_consequence, assumption, rule aentails_refl, rule aentails_refl, force)
  }
  from this have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. INV (length thunks) r \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using assms by (auto intro!: ucincl_intros gather_spec[where INV=\<open>\<lambda>i' res'. INV i' res' \<star> ?pc\<close> and thunks=thunks])
  moreover have \<open>\<And>r. INV (length thunks) r \<star> ?pc
                 \<longlongrightarrow> INV (length thunks) r \<star> (\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r))\<close>
    by (meson aentails_refl local.aentails_int local.asepconj_mono)
  moreover have \<open>\<And>r. INV (length thunks) r \<star> (\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r))  \<longlongrightarrow> \<psi> r\<close>
    by (metis (no_types, lifting) aentails_refl local.aforall_entailsL local.asepconj_AC(1) local.awand_adjoint)
  moreover have \<open>\<And>r. INV (length thunks) r \<star> ?pc \<longlongrightarrow> \<psi> r\<close>
    using calculation by blast
  moreover have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile> gather thunks \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using calculation local.striple_consequence by blast
  from this show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.striple_consequence by fastforce
qed


end

end
