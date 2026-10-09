(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Rust_Weakest_Precondition
  imports
    Shallow_Separation_Logic.Weakest_Precondition
    Rust_Triple
begin

context sepalg begin

lemma wp_pause:
    notes asepconj_simp [simp]
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> pause \<psi> \<rho> \<theta> = \<psi> ()\<close>
  using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_pause')

text\<open>The following is deliberately not marked as \<^verbatim>\<open>separation_logic_wp_intros\<close> so automation does not
silently go over it.\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_pauseI:
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> ()\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> pause \<psi> \<rho> \<theta>\<close>
using assms by (simp add: wp_pause)

lemma wp_log:
    notes asepconj_simp [simp]
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (log p l) \<psi> \<rho> \<theta> = \<psi> ()\<close>
using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_log')

lemma wp_logI [separation_logic_wp_intros]:
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> ()\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (log p l) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: wp_log)

lemma wp_fatalI [separation_logic_wp_intros]:
    notes asepconj_simp [simp]
  assumes \<open>is_aborting_striple_context \<Gamma>\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (fatal msg) \<psi> \<rho> \<theta>\<close>
  using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_fatal)

corollary wp_core_rust_literals [separation_logic_wp_simps]:
  shows \<open>\<And>\<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> true \<psi> \<rho>  \<theta>= \<psi> True\<close>
    and \<open>\<And>\<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> false \<psi> \<rho>  \<theta>= \<psi> False\<close>
    and \<open>\<And>\<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> none \<psi> \<rho>  \<theta>= \<psi> None\<close>
    and \<open>\<And>x \<psi>. (\<And>r. ucincl (\<rho> r)) \<Longrightarrow> (\<And>s. ucincl (\<psi> s)) \<Longrightarrow> \<W>\<P> \<Gamma> (some (literal x)) \<psi> \<rho>  \<theta>= \<psi> (Some x)\<close>
by (auto simp add: true_def false_def none_def some_def wp_literal micro_rust_simps)

corollary wp_panic [separation_logic_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (panic m) \<psi> \<rho> \<theta> = \<theta> (Panic m) \<star> UNIV\<close>
  by (intro wp_abort)

lemma wp_panicI [separation_logic_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (Panic m) \<star> UNIV\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (panic m) \<psi> \<rho> \<theta>\<close>
using assms by (subst wp_panic)

lemma wp_assert [separation_logic_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (assert (literal x)) \<psi> \<rho> \<theta> = (\<langle>x\<rangle> \<Zsurj> (UNIV \<star> \<psi> ())) \<sqinter> (\<langle>\<not>x\<rangle> \<Zsurj> (UNIV \<star> \<theta> AssertionFailed))\<close>
  apply (intro aentails_yonedaI)
  apply (clarsimp simp add: sstriple_wp_iff aentails_simp sstriple_assert apure_def asepconj_simp
    bot_aentails_all)
  apply (meson aentails_refl_eq aentails_trans aentails_top_R' aentails_uc'
    ucincl_UNIV ucincl_asepconjL)
  done

lemma wp_assert_eq [separation_logic_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (assert_eq (literal x) (literal y)) \<psi> \<rho> \<theta> =
     (\<langle>x=y\<rangle> \<Zsurj> (UNIV \<star> \<psi> ())) \<sqinter> (\<langle>x\<noteq>y\<rangle> \<Zsurj> (UNIV \<star> \<theta> AssertionFailed))\<close>
  by (clarsimp simp add: wp_assert[simplified assert_def micro_rust_simps]
    assert_eq_def assert_eq_val_def micro_rust_simps)

thm aentails_frulify_pure

lemma wp_assertI[separation_logic_wp_intros]:
    notes aentails_intro [intro]
  assumes \<open>\<phi> \<longlongrightarrow> (\<langle>x\<rangle> \<star> \<psi> ())\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (assert (literal x)) \<psi> \<rho> \<theta>\<close>
proof -
  have \<open>\<langle>x\<rangle> \<star> \<psi> () \<star> \<langle>x\<rangle> \<longlongrightarrow> UNIV \<star> \<psi> ()\<close>
    by (simp add: aentails_refl apure_entailsL' asepconj_comm asepconj_pure2)
  moreover
  have \<open>\<langle>x\<rangle> \<star> \<psi> () \<star> \<langle>\<not> x\<rangle> \<longlongrightarrow> UNIV \<star> \<theta> AssertionFailed\<close>
    by (metis local.aentails_is_sat local.is_sat_pure local.is_sat_splitE)
  ultimately show ?thesis
    using aentails_trans[OF assms]
    by (simp add: wp_assert aentails_intI asepconj_assoc awand_adjoint)
qed

lemma wp_assert_eqI[separation_logic_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>\<phi> \<longlongrightarrow> (\<langle>x=y\<rangle> \<star> \<psi> ())\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (assert_eq (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp intro!: wp_assertI[simplified assert_def micro_rust_simps]
     simp add: assert_eq_def assert_eq_val_def micro_rust_simps)

lemma wp_assert_neI[separation_logic_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>\<phi> \<longlongrightarrow> (\<langle>x\<noteq>y\<rangle> \<star> \<psi> ())\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (assert_ne (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp intro!: wp_assertI[simplified assert_def micro_rust_simps]
     simp add: assert_ne_def assert_ne_val_def micro_rust_simps)

lemma wp_option_cases: (* [separation_logic_wp_simps]: *)
  shows
    \<open>
      \<W>\<P> \<Gamma>
        (do {
          case_value \<leftarrow> literal x;
          case case_value of None \<Rightarrow> nn | Some s \<Rightarrow> sm s
        })
        \<psi> \<rho> \<theta> =
      (case x of
         None   \<Rightarrow> \<W>\<P> \<Gamma> nn \<psi> \<rho> \<theta>
       | Some s \<Rightarrow> \<W>\<P> \<Gamma> (sm s) \<psi> \<rho> \<theta>)
    \<close>
by (rule asat_semequivI; cases \<open>x\<close>) (auto simp add: micro_rust_simps)

lemma wp_option_cases_none[separation_logic_wp_simps]:
  shows
    \<open>
      \<W>\<P> \<Gamma>
        (do {
          case_value \<leftarrow> literal None;
          case case_value of None \<Rightarrow> nn | Some s \<Rightarrow> sm s
        })
        \<psi> \<rho> \<theta> =
      \<W>\<P> \<Gamma> nn \<psi> \<rho> \<theta>
    \<close>
  by (simp add: wp_option_cases)

lemma wp_option_cases_some[separation_logic_wp_simps]:
  shows
    \<open>
      \<W>\<P> \<Gamma>
        (do {
          case_value \<leftarrow> literal (Some s);
          case case_value of None \<Rightarrow> nn | Some s \<Rightarrow> sm s
        })
        \<psi> \<rho> \<theta> =
      \<W>\<P> \<Gamma> (sm s) \<psi> \<rho> \<theta>
    \<close>
  by (simp add: wp_option_cases)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_option_casesI:
  assumes \<open>x = None \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> nn \<psi> \<rho> \<theta>\<close>
     and \<open>\<And>s. x = Some s \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (sm s) \<psi> \<rho> \<theta>\<close>
   shows
     \<open>
       \<phi> \<longlongrightarrow>
       \<W>\<P> \<Gamma>
         (do {
           case_value \<leftarrow> literal x;
           case case_value of None \<Rightarrow> nn | Some s \<Rightarrow> sm s
         })
         \<psi> \<rho> \<theta>
     \<close>
  using assms by (clarsimp simp add: wp_option_cases split!: option.splits)

lemma wp_result_cases: (* [separation_logic_wp_simps]: *)
  shows
    \<open>
      \<W>\<P> \<Gamma>
        (do {
          case_value \<leftarrow> literal x;
          case case_value of Ok k \<Rightarrow> ok k | Err e \<Rightarrow> err e
        })
        \<psi> \<rho> \<theta> =
      (case x of
         Ok k  \<Rightarrow> \<W>\<P> \<Gamma> (ok k) \<psi> \<rho> \<theta>
       | Err e \<Rightarrow> \<W>\<P> \<Gamma> (err e) \<psi> \<rho> \<theta>)
    \<close>
by (rule asat_semequivI; cases \<open>x\<close>) (auto simp add:micro_rust_simps)

lemma wp_result_cases_ok[separation_logic_wp_simps]:
  shows
    \<open>
      \<W>\<P> \<Gamma>
        (do {
          case_value \<leftarrow> literal (Ok k);
          case case_value of Ok k \<Rightarrow> ok k | Err e \<Rightarrow> err e
        })
        \<psi> \<rho> \<theta> =
      \<W>\<P> \<Gamma> (ok k) \<psi> \<rho> \<theta>
    \<close>
  by (simp add: wp_result_cases)

lemma wp_result_cases_err[separation_logic_wp_simps]:
  shows
    \<open>
      \<W>\<P> \<Gamma>
        (do {
          case_value \<leftarrow> literal (Err e);
          case case_value of Ok k \<Rightarrow> ok k | Err e \<Rightarrow> err e
        })
        \<psi> \<rho> \<theta> =
      \<W>\<P> \<Gamma> (err e) \<psi> \<rho> \<theta>
    \<close>
  by (simp add: wp_result_cases)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_result_casesI:
  assumes \<open>\<And>k. x = Ok k \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (ok k) \<psi> \<rho> \<theta>\<close>
     and \<open>\<And>e. x = Err e \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (err e) \<psi> \<rho> \<theta>\<close>
   shows
     \<open>
       \<phi> \<longlongrightarrow>
       \<W>\<P> \<Gamma>
         (do {
           case_value \<leftarrow> literal x;
           case case_value of Ok k \<Rightarrow> ok k | Err e \<Rightarrow> err e
         })
         \<psi> \<rho> \<theta>
     \<close>
  using assms by (clarsimp simp add: wp_result_cases split!: result.splits)

lemma wp_range_new [separation_logic_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<phi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (funcall2 range_new (literal b) (literal e)) \<phi> \<rho> \<theta> =
      \<phi> (make_range b e False)\<close>
using assms by (clarsimp simp add: range_new_def wp_funliteral)

lemma wp_op_eqs [separation_logic_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (urust_eq (literal e) (literal f)) \<psi> \<rho> \<theta> = \<psi> (e = f)\<close>
using assms by (clarsimp simp add: urust_eq_def separation_logic_wp_simps micro_rust_simps)

lemma wp_word_add_no_wrap [separation_logic_wp_intros]:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x+y))\<close>
    shows \<open>\<langle>unat x + unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x + y) \<longlongrightarrow>
      \<W>\<P> \<Gamma> (word_add_no_wrap (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
      (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>(unat x) + (unat y) < 2^(LENGTH('l))\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile>
      word_add_no_wrap (literal x) (literal y) \<stileturn>
      (\<lambda>r. \<langle>r = x + y\<rangle> \<star> \<psi> (x+y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return; simp add: sstriple_word_add_no_wrapI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile>
      word_add_no_wrap (literal x) (literal y) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_add_no_wrapI [separation_logic_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x + y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat x + unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x + y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (word_add_no_wrap (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_add_no_wrap, auto)

lemma wp_word_mul_no_wrap [separation_logic_wp_intros]:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x*y))\<close>
    shows \<open>\<langle>unat x * unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x * y) \<longlongrightarrow>
      \<W>\<P> \<Gamma> (word_mul_no_wrap (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
      (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>(unat x) * (unat y) < 2^(LENGTH('l))\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile>
      word_mul_no_wrap (literal x) (literal y) \<stileturn>
      (\<lambda>r. \<langle>r = x * y\<rangle> \<star> \<psi> (x*y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_mul_no_wrapI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile>
      word_mul_no_wrap (literal x) (literal y) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]; auto)
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_mul_no_wrapI [separation_logic_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x * y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat x * unat y < 2^LENGTH('l)\<rangle> \<star> \<psi> (x * y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (word_mul_no_wrap (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_mul_no_wrap, auto)

lemma wp_word_sub_no_wrap:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x - y))\<close>
    shows \<open>\<langle>y \<le> x\<rangle> \<star> \<psi> (x - y) \<longlongrightarrow>
      \<W>\<P> \<Gamma> (word_minus_no_wrap (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
      (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>y \<le> x\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile>
      word_minus_no_wrap (literal x) (literal y) \<stileturn>
      (\<lambda>r. \<langle>r = x - y\<rangle> \<star> \<psi> (x - y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_sub_no_wrapI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile>
      word_minus_no_wrap (literal x) (literal y) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_sub_no_wrapI [separation_logic_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x - y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>y \<le> x\<rangle> \<star> \<psi> (x - y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (word_minus_no_wrap (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_sub_no_wrap, auto)

lemma wp_word_udiv:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x div y))\<close>
  shows \<open>\<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x div y) \<longlongrightarrow>
    \<W>\<P> \<Gamma> (word_udiv (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
    (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>y \<noteq> 0\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile>
      word_udiv (literal x) (literal y) \<stileturn>
      (\<lambda>r. \<langle>r = x div y\<rangle> \<star> \<psi> (x div y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_udivI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile>
      word_udiv (literal x) (literal y) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_udivI [separation_logic_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x div y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x div y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (word_udiv (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_udiv, auto)

lemma wp_word_umod:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x mod y))\<close>
    shows \<open>\<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x mod y) \<longlongrightarrow>
      \<W>\<P> \<Gamma> (word_umod (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
      (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>y \<noteq> 0\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have I: \<open>\<Gamma> ; ?asm \<turnstile>
      word_umod (literal x) (literal y) \<stileturn>
      (\<lambda>r. \<langle>r = x mod y\<rangle> \<star> \<psi> (x mod y)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_umodI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile>
      word_umod (literal x) (literal y) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_umodI [separation_logic_wp_intros]:
    fixes x y :: \<open>'l::{len} word\<close>
  assumes \<open>ucincl (\<psi> (x mod y))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x mod y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (word_umod (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_word_umod, auto)

lemma wp_bitwise_or:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (x OR y) \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_or (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_orI)

lemma wp_bitwise_and:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (x AND y) \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_and (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_andI)

lemma wp_bitwise_xor:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (x XOR y) \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_xor (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_xorI)

lemma wp_bitwise_not:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>\<psi> (NOT x) \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_not (literal x)) \<psi> \<rho> \<theta>\<close>
using assms by (intro sstriple_pure_to_wp') (auto intro: sstriple_bitwise_notI)

lemma wp_bitwise_orI [separation_logic_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (x OR y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_or (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_or aentails_trans' by blast

lemma wp_bitwise_andI [separation_logic_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (x AND y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_and (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_and aentails_trans' by blast

lemma wp_bitwise_xorI [separation_logic_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (x XOR y)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_xor (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_xor aentails_trans' by blast

lemma wp_bitwise_notI [separation_logic_wp_intros]:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (NOT x)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (Numeric_Types.word_bitwise_not (literal x)) \<psi> \<rho> \<theta>\<close>
using assms wp_bitwise_not aentails_trans' by blast

lemma wp_word_shift_left:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp[simp]
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (push_bit (unat y) x))\<close>
    shows \<open>\<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (push_bit (unat y) x) \<longlongrightarrow>
      \<W>\<P> \<Gamma> (word_shift_left_shift64 (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
      (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>unat y < LENGTH('l0)\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have
         I: \<open>\<Gamma> ; ?asm \<turnstile> word_shift_left_shift64 (literal x) (literal y) \<stileturn>
           (\<lambda>r. \<langle>r = push_bit (unat y) x\<rangle> \<star> \<psi> (push_bit (unat y) x))
           \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_shift_leftI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile>
      word_shift_left_shift64 (literal x) (literal y) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_shift_leftI [separation_logic_wp_intros]:
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (push_bit (unat y) x))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (push_bit (unat y) x)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (word_shift_left_shift64 (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms wp_word_shift_left aentails_trans' by blast

lemma wp_word_shift_right:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (drop_bit (unat y) x))\<close>
    shows \<open>\<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (drop_bit (unat y) x) \<longlongrightarrow>
      \<W>\<P> \<Gamma> (word_shift_right_shift64 (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
      (is \<open>?asm \<longlongrightarrow> ?GOAL\<close>)
proof -
  have \<open>ucincl (\<langle>unat y < LENGTH('l0)\<rangle>)\<close>
    by (simp add: ucincl_apure)
  moreover from this have \<open>ucincl ?asm\<close>
    by (simp add: assms ucincl_apure ucincl_asepconj)
  moreover from calculation and assms have
         I: \<open>\<Gamma> ; ?asm \<turnstile> word_shift_right_shift64 (literal x) (literal y) \<stileturn>
           (\<lambda>r. \<langle>r = drop_bit (unat y) x\<rangle> \<star> \<psi> (drop_bit (unat y) x))
           \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_frame_rule_no_return) (auto simp add: sstriple_word_shift_rightI)
  moreover from assms have \<open>\<Gamma> ; ?asm \<turnstile>
      word_shift_right_shift64 (literal x) (literal y) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_consequence[OF I]) auto
  ultimately show \<open>?asm \<longlongrightarrow> ?GOAL\<close>
    by (intro wp_is_weakest_precondition)
qed

lemma wp_word_shift_rightI [separation_logic_wp_intros]:
    fixes x :: \<open>'l0::{len} word\<close>
      and y :: \<open>64 word\<close>
  assumes \<open>ucincl (\<psi> (drop_bit (unat y) x))\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>unat y < LENGTH('l0)\<rangle> \<star> \<psi> (drop_bit (unat y) x)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma>
      (word_shift_right_shift64 (literal x) (literal y)) \<psi> \<rho> \<theta>\<close>
using assms wp_word_shift_right aentails_trans' by blast

subsection\<open>Gather\<close>

lemma wp_gather_framedI:
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and \<xi> :: \<open>nat \<Rightarrow> 'v \<Rightarrow> bool\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<And>ls i. ucincl (INV i ls)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV 0 [] \<star> ((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>i res. i < length thunks \<Longrightarrow> length res = i \<Longrightarrow>
              \<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn> (\<lambda>v. INV (i+1) (res @ [v])) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (gather thunks) \<psi> \<rho> \<chi>\<close>
proof -
  let ?pc = \<open>((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  from assms have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile> gather thunks \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (intro sstriple_gather_framed; simp add: local.wp_to_sstriple ucincl_intros)
  from this and assms have \<open>INV 0 [] \<star> ?pc \<longlongrightarrow> \<W>\<P> \<Gamma> (gather thunks) \<psi> \<rho> \<chi>\<close>
    by (intro wp_is_weakest_precondition) (auto intro!: ucincl_asepconj ucincl_inter ucincl_Int
      ucincl_awand)
  from this and assms show ?thesis
    by (meson assms ucincl_asepconj ucincl_awand aentails_trans')
qed

lemma wp_gather_framedI':
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and \<xi> :: \<open>nat \<Rightarrow> 'v \<Rightarrow> bool\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<And>ls i. ucincl (INV i ls)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV 0 [] \<star> ((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>i res. i < length thunks \<Longrightarrow> length res = i \<Longrightarrow>
              INV i res \<longlongrightarrow> \<W>\<P> \<Gamma> (thunks ! i) (\<lambda>v. INV (i+1) (res @ [v])) \<tau> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (gather thunks) \<psi> \<rho> \<chi>\<close>
  using assms by (blast intro: wp_gather_framedI wp_to_sstriple)


end

end
