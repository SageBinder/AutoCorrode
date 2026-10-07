(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Rust_Triple
  imports
    Shallow_Separation_Logic.Triple
    Rust_Weak_Triple
begin

context sepalg begin

lemma sstriple_assert_val:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> assert_val v \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
     ((v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (\<not>v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed))\<close>
  by (auto simp add: sstriple_striple striple_assert_val eval_value_def
    eval_abort_def eval_return_def shallow_computation_eval_predicate_simps is_local_def)

lemma sstriple_assert:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> assert (literal v) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
            (v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (\<not>v \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
  by (simp add: assert_def micro_rust_simps sstriple_assert_val)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_assert_eq:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> assert_eq (literal v) (literal w) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow>
      (v=w \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<psi> ()) \<and> (v \<noteq> w \<longrightarrow> \<phi> \<longlongrightarrow> \<top> \<star> \<theta> AssertionFailed)\<close>
  by (simp add: assert_eq_def assert_eq_val_def sstriple_assert_val micro_rust_simps)

text\<open>The \<^verbatim>\<open>return_func\<close> command always succeeds and returns the given value:\<close>
corollary sstriple_noneI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> none \<stileturn> (\<lambda>rv. \<langle>rv = None\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  unfolding none_def by (rule sstriple_literalI)

corollary sstriple_trueI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> true \<stileturn> (\<lambda>rv. \<langle>rv = True\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  unfolding true_def by (rule sstriple_literalI)

corollary sstriple_falseI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> false \<stileturn> (\<lambda>rv. \<langle>rv = False\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  unfolding false_def by (rule sstriple_literalI)

corollary sstriple_someI:
  notes asepconj_simp [simp]
  shows \<open>\<Gamma> ; \<top> \<turnstile> some (literal x) \<stileturn> (\<lambda>rv. \<langle>rv = Some x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  apply (intro sstriple_from_stripleI striple_someI)
  apply (auto simp add: return_func_def eval_predicate_literal eval_predicate_return
    micro_rust_simps some_def is_local_def eval_value_def eval_return_def eval_abort_def)
  done

text\<open>Abort and panic terminate execution of the program:\<close>
lemma sstriple_panic:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> panic m \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<theta> (Panic m) \<star> \<top>)\<close>
  by (simp add: sstriple_abort)

text\<open>Pause / Breakpoint\<close>

lemma sstriple_pause:
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<top> \<turnstile> pause \<stileturn> \<top> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
  using assms
  by (auto intro!: sstriple_from_stripleI striple_pause
      simp add: is_local_def eval_return_def eval_value_def eval_abort_def shallow_computation_eval_predicate_simps
      is_valid_striple_context_def)

lemma sstriple_pause':
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> pause \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> ())\<close>
proof
  show \<open>\<Gamma> ; \<phi> \<turnstile> pause \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta> \<Longrightarrow> \<phi> \<longlongrightarrow> \<psi> ()\<close>
    using assms by (simp add: striple_pause' sstriple_striple')
  show \<open>\<phi> \<longlongrightarrow> \<psi> () \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> pause \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using assms
    by (auto simp: sstriple_striple striple_pause' is_local_def
        eval_return_def eval_value_def eval_abort_def shallow_computation_eval_predicate_simps)
qed

text\<open>Log\<close>

lemma sstriple_log:
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> log p l \<stileturn> \<top> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (auto intro!: sstriple_from_stripleI striple_log simp add: is_local_def eval_return_def eval_value_def shallow_computation_eval_predicate_simps
    is_valid_striple_context_def eval_abort_def)

lemma sstriple_log':
  assumes \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> log p l \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> ())\<close>
proof
  show \<open>\<Gamma> ; \<phi> \<turnstile> log p l \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta> \<Longrightarrow> \<phi> \<longlongrightarrow> \<psi> ()\<close>
    using assms by (simp add: local.striple_log' sstriple_striple')
  show \<open>\<phi> \<longlongrightarrow> \<psi> () \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> log p l \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using assms by (meson aentails_true is_local_weaken striple_log' sstriple_log sstriple_striple)
qed

text\<open>Fatal errors\<close>

lemma sstriple_fatal:
  assumes \<open>is_aborting_striple_context \<Gamma>\<close>
      and \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>(\<Gamma> ; \<phi> \<turnstile> fatal msg \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
  using assms
  by (auto intro!: sstriple_from_stripleI
      simp add: is_local_def eval_return_def eval_value_def shallow_computation_eval_predicate_simps
      is_aborting_striple_context_def eval_abort_def striple_fatal)

text\<open>Generic yield\<close>

subsection\<open>Defining triples for numeric and bitwise operators\<close>

lemma sstriple_word_add_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x + unat y < 2^(LENGTH('l))\<rangle> \<turnstile> word_add_no_wrap (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x + y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_word_add_no_wrapI simp add: eval_value_def
  eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_word_mul_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x * unat y < 2^(LENGTH('l))\<rangle> \<turnstile> word_mul_no_wrap (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x * y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_word_mul_no_wrapI simp add: eval_value_def
  eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_word_sub_no_wrapI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<le> x\<rangle> \<turnstile> word_minus_no_wrap (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x - y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (auto intro!: sstriple_from_stripleI striple_word_sub_no_wrapI simp add: eval_value_def
    eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_word_udivI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> word_udiv (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x div y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_word_udivI simp add: eval_value_def eval_return_def
  shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_word_umodI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> word_umod (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x mod y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_word_umodI simp add: eval_value_def eval_return_def
  shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_word_shift_leftI:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat y < LENGTH('l0)\<rangle> \<turnstile> word_shift_left_shift64 (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = push_bit (unat y) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_word_shift_leftI simp add: eval_value_def
  eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_word_shift_rightI:
  fixes x :: \<open>'l0::{len} word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat y < LENGTH('l0)\<rangle> \<turnstile> word_shift_right_shift64 (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = drop_bit (unat y) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_word_shift_rightI simp add: eval_value_def
  eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_bitwise_orI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_or (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x OR y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_bitwise_orI simp add: eval_value_def eval_return_def
  shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_bitwise_andI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_and (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x AND y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_bitwise_andI simp add: eval_value_def
  eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_bitwise_xorI:
  fixes x y :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_xor (literal x) (literal y) \<stileturn> (\<lambda>r. \<langle>r = x XOR y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_bitwise_xorI simp add: eval_value_def
  eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_bitwise_notI:
  fixes x :: \<open>'l::{len} word\<close>
  shows \<open>\<Gamma> ; \<top> \<turnstile> Numeric_Types.word_bitwise_not (literal x) \<stileturn> (\<lambda>r. \<langle>r = NOT x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (auto intro!: sstriple_from_stripleI striple_bitwise_notI simp add: eval_value_def
  eval_return_def shallow_computation_eval_predicate_simps is_local_def eval_abort_def)

lemma sstriple_gather_spec':
    notes asepconj_simp [simp]
      and aentails_intro [intro]
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>i ls. i < length thunks \<Longrightarrow> length ls = i \<Longrightarrow> (\<Gamma> ; INV i ls \<turnstile> thunks ! i \<stileturn> (\<lambda>v. INV (i+1) (ls @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; INV 0 [] \<turnstile> gather' thunks acc \<stileturn> (\<lambda>rs. \<Squnion>rs'. \<langle>rs = acc @ rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
proof (induction thunks arbitrary: INV acc)
  case Nil
  then show ?case
    by (auto simp: gather'_nil apure_def eval_predicate_literal
       eval_value_def eval_abort_def eval_return_def sstriple_def atriple_rel_def is_local_def
      local.asepconj_comm local.asepconj_weaken2I)
next
  case (Cons t thunks)
  then have  first: \<open>\<Gamma> ; INV 0 [] \<turnstile> t \<stileturn> (\<lambda>v. INV 1 [v]) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  have \<open>\<Gamma> ; INV 1 [r0] \<turnstile> gather' thunks (acc @ [r0]) \<stileturn>
        (\<lambda>rs. \<Squnion>rs'. \<langle>rs = (acc @ rs')\<rangle> \<star> INV (length (t # thunks)) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close> for r0
  proof -
    have \<open>\<Gamma> ; INV (i+1) (r0 # ls) \<turnstile> thunks ! i \<stileturn> (\<lambda>v. INV ((i+1)+1) ((r0 # ls) @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      if  \<open>i < length thunks\<close> and \<open>length ls = i\<close> for i and ls :: \<open>'v list\<close>
      using that Cons.prems[where i=\<open>i+1\<close> and ls=\<open>r0 # ls\<close>] by fastforce
    with Cons.IH[where INV=\<open>\<lambda>i ls. INV (i+1) (r0 # ls)\<close> and acc=\<open>acc @ [r0]\<close>]
    have \<open>\<Gamma> ; INV 1 [r0] \<turnstile> gather' thunks (acc @ [r0]) \<stileturn>
          (\<lambda>rs. \<Squnion>rs'. \<langle>rs = (acc @ (r0 # rs'))\<rangle> \<star> INV (length (t # thunks)) (r0 # rs')) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      by simp
    moreover
    have \<open>\<And>rs. (\<Squnion>rs'. \<langle>rs = (acc @ (r0 # rs'))\<rangle> \<star> INV (Suc (length thunks)) (r0 # rs')) \<longlongrightarrow>
          (\<Squnion>rs'. \<langle>rs = (acc @ rs')\<rangle> \<star> INV (Suc (length thunks)) rs')\<close>
      by blast
    ultimately show ?thesis
      by (meson aentails_refl local.aexists_entailsL local.aexists_entailsR local.sstriple_consequence)
  qed
  then show ?case
    by (metis (no_types, lifting) first gather'_cons sstriple_bindI)
qed

lemma sstriple_gather_spec:
    notes aentails_intro [intro]
    fixes INV :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'a assert\<close>
      and thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>i ls. ucincl (INV i ls)\<close>
      and \<open>\<And>i ls. i < length thunks \<Longrightarrow> length ls = i \<Longrightarrow>
            \<Gamma> ; INV i ls \<turnstile> thunks ! i \<stileturn> (\<lambda>v. INV (i+1) (ls @ [v])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn> (\<lambda>rs. INV (length thunks) rs) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  from assms and gather_spec'[where INV=INV and thunks=thunks] have
        \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn> (\<lambda>rs. \<Squnion>rs'. \<langle>rs = [] @ rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    unfolding gather_def using sstriple_gather_spec' by blast
  from this have \<open>\<Gamma> ; INV 0 [] \<turnstile> gather thunks \<stileturn> (\<lambda>rs. \<Squnion>rs'. \<langle>rs = rs'\<rangle> \<star> INV (length thunks) rs') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  moreover have \<open>\<And>rs. (\<Squnion>rs'. \<langle>rs = rs'\<rangle> \<star> INV (length thunks) rs') \<longlongrightarrow> INV (length thunks) rs\<close>
    using assms by (simp add: asat_simp aentails_def)
  ultimately show ?thesis
    using sstriple_consequence by blast
qed

lemma sstriple_gather_framed:
    notes aentails_intro [intro]
    fixes thunks :: \<open>('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression list\<close>
  assumes \<open>\<And>p r. ucincl (INV p r)\<close>
      and \<open>\<And>i res. i < length thunks \<Longrightarrow> length res = i \<Longrightarrow> \<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn> (\<lambda>v. INV (i+1) (res @ [v])) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
  shows \<open>\<Gamma> ; INV 0 [] \<star> ((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r)) \<turnstile> gather thunks \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>((\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r)) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  {
    fix i and res :: \<open>'v list\<close>
    assume \<open>i < length thunks\<close>
       and \<open>length res = i\<close>
    from this have \<open>\<Gamma> ; INV i res \<turnstile> thunks ! i \<stileturn> (\<lambda>r. INV (i+1) (res @ [r])) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms \<open>i < length thunks\<close> by auto
    moreover have \<open>\<Gamma> ; INV i res \<star> ?pc \<turnstile>
          (thunks ! i) \<stileturn> (\<lambda>r. INV (i+1) (res @ [r]) \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>r. \<theta> r \<star> ?pc)\<close>
      using assms calculation by (intro sstriple_frame_rule, force)
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
    ultimately have \<open>\<Gamma> ; INV i res \<star> ?pc \<turnstile> thunks ! i \<stileturn> (\<lambda>r. INV (i+1) (res @ [r]) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      by - (rule sstriple_consequence, assumption, rule aentails_refl, rule aentails_refl, force)
  }
  from this have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile>
        gather thunks \<stileturn> (\<lambda>r. INV (length thunks) r \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using assms by (auto intro!: ucincl_intros sstriple_gather_spec[where INV=\<open>\<lambda>i' res'. INV i' res' \<star> ?pc\<close> and thunks=thunks])
  moreover have \<open>\<And>r. INV (length thunks) r \<star>?pc
                 \<longlongrightarrow> INV (length thunks) r \<star> (\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r))\<close>
    by (meson aentails_refl local.aentails_int local.asepconj_mono)
  moreover have \<open>\<And>r. INV (length thunks) r \<star> (\<Sqinter>r. (INV (length thunks) r \<Zsurj> \<psi> r))  \<longlongrightarrow> \<psi> r\<close>
    by (metis (no_types, lifting) aentails_refl local.aforall_entailsL local.asepconj_AC(1) local.awand_adjoint)
  ultimately have \<open>\<Gamma> ; INV 0 [] \<star> ?pc \<turnstile> gather thunks \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (meson aentails_refl aentails_trans sstriple_consequence)
  then show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.sstriple_consequence by fastforce
qed


end

end
