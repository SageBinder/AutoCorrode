(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Weakest_Precondition
  imports
    Shallow_State_Logic.Assertion_Language
    Triple
    Function_Contract
    Shallow_Computation.Shallow_Computation
    Representability
begin
(*>*)

section\<open>A weakest precondition calculus\<close>

(*<*)
context sepalg begin
(*>*)

text\<open>For solving goals related to Separation Logic triples, we introduce a Weakest Precondition (WP)
calculus: A means to convert questions about triples \<^term>\<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close> into questions of
ordinary entailment \<^term>\<open>(\<longlongrightarrow>)\<close>: For \<^emph>\<open>fixed\<close> \<^term>\<open>\<Gamma>\<close>, \<^term>\<open>e\<close>, \<^term>\<open>\<psi>\<close> and \<^term>\<open>\<rho>\<close>, we seek
to find an assertion \<^verbatim>\<open>\<W>\<P> \<Gamma> e \<psi> \<rho>\<close> so that for any \<^term>\<open>\<phi>\<close>, \<^term>\<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close> is equivalent to
 \<^verbatim>\<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho>\<close>.

First, we show that the weakest precondition exists, without explicitly computing it. This is a
consequence of basic triple properties and the abstract representability theorem proved in
\<^file>\<open>Representability.thy\<close>.

Second, we develop rules for computing or approximating the weakest precondition for various language
constructs, proceeding on a case by case basis. Ultimately, this provides the
\<^emph>\<open>weakest precondition calculus\<close> as a syntax-directed way of reasoning about triples.\<close>

subsection\<open>Representability of sstriples\<close>

text\<open>In this section, we show that for fixed \<^term>\<open>\<Gamma>\<close>, \<^term>\<open>e\<close>, \<^term>\<open>\<psi>\<close> and \<^term>\<open>\<rho>\<close>, the functor
 \<^verbatim>\<open>\<Gamma> ; _ \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho>\<close> is representable. The representing object is, by definition, the weakest
precondition for \<^verbatim>\<open>\<Gamma>,e,\<psi>,\<rho>\<close>.\<close>

text\<open>First, the definition of the sstriple as a functor on assertions:\<close>

definition sstriple_functor ::
  \<open>('a, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response) striple_context \<Rightarrow>
                  ('a, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>The expression to compute the WP for\<close>
                  ('v \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The success postcondition to compute the WP relative to\<close>
                  ('r \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The return postcondition to compute the WP relative to\<close>
                  ('abort abort \<Rightarrow> 'a assert) \<Rightarrow>
                  'a assert \<Rightarrow> bool\<close> where
  \<open>sstriple_functor \<Gamma> e \<psi> \<rho> \<theta> \<equiv> (\<lambda>\<phi>. (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>))\<close>

text \<open>From \<^file>\<open>Representability.thy\<close> we know that if the sstriple is representable, the representing
object must be given by \<^term>\<open>afunctor_sup\<close>. Let's give this a name.

Note: It should not be necessary to unfold this definition! Instead, work purely with the
universal property \<^verbatim>\<open>wp_sstriple_iff\<close> established below to reduce properties of \<^verbatim>\<open>\<W>\<P>\<close>
to properties of sstriples. There are plenty of examples below.\<close>

definition wp ::
  \<open>('a, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response) striple_context \<Rightarrow>
                  ('a, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>The expression to compute the WP for\<close>
                  ('v \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The success postcondition to compute the WP relative to\<close>
                  ('r \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The return postcondition to compute the WP relative to\<close>
                  ('abort abort \<Rightarrow> 'a assert) \<Rightarrow>
                  'a assert\<close> ("\<W>\<P>") where
  \<open>\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta> \<equiv> afunctor_sup (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>

text \<open>Next, we check the representability conditions for the sstriple functor.
First, contravariance:\<close>

lemma sstriple_contravariant:
  shows \<open>is_contravariant (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>
by (simp add: aentails_refl is_contravariant_def sstriple_consequence sstriple_functor_def)

text\<open>Second, sup-stability:\<close>

lemma sstriple_is_sup_stable:
  shows \<open>is_sup_stable (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>
by (simp add: aentails_refl is_sup_stable_def sstriple_functor_def aentails_def asat_def
  sstriple_existsI')

text\<open>As a consequence of contravariance and sup-stability, we obtain the representability
of the sstriple functor.\<close>

lemma sstriple_is_representable:
  shows \<open>is_representable (sstriple_functor \<Gamma> e \<psi> \<rho> \<theta>)\<close>
using sstriple_is_sup_stable sstriple_contravariant afunctor_representability_criterion by blast

text\<open>Since we have already spelled out the representability candidate as \<^verbatim>\<open>\<W>\<P>\<close>, representability
can concretely be stated as follows:\<close>

lemma sstriple_wp_iff:
  shows \<open>(\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
proof -
  from afunctor_representability_iff[OF sstriple_is_representable] have
     \<open>(\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) \<longleftrightarrow> sstriple_functor \<Gamma> e \<psi> \<rho> \<theta> \<phi>\<close>
    by (force simp add: wp_def)
  from this show ?thesis
    unfolding sstriple_functor_def by simp
qed

lemma wp_sstriple_iff:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>)\<close>
  by (simp add: sstriple_wp_iff)

corollary wp_to_sstriple:
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    shows \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms wp_sstriple_iff by blast

corollary wp_is_precondition:
    shows \<open>\<Gamma> ; \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (simp add: aentails_refl wp_to_sstriple)

corollary wp_is_weakest_precondition:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
  using assms wp_sstriple_iff by blast

subsection\<open>Transporting general triple properties to WP-rules\<close>

text \<open>In this section, we demonstrate how to transport properties of sstriples to properties
of the weakest precondition. The proofs are purely formal and solely rely on the universal property
of the weakest precondition,  but not its concrete definition.\<close>

text \<open>First, the weakest precondition is always upwards closed:\<close>
lemma ucincl_wp'I [ucincl_intros]:
  shows \<open>ucincl (\<W>\<P> \<Gamma> e \<phi> \<psi> \<theta>)\<close>
  \<comment>\<open>For sake of demonstration, we go through this proof in small steps:\<close>
  \<comment>\<open>First, we need to use a definition of \<^term>\<open>ucincl\<close> which only uses \<^verbatim>\<open>_ \<longlongrightarrow> \<phi>\<close>,
  but not \<^verbatim>\<open>\<phi>\<close> itself. Luckily, \<^verbatim>\<open>ucincl_alt'\<close> provides such:\<close>
  apply (simp add: ucincl_alt')
  \<comment>\<open>Next, we apply the universal property of \<^verbatim>\<open>\<W>\<P>\<close> on both sides:\<close>
  apply (simp add: sstriple_wp_iff)
  \<comment>\<open>This has transformed the goal to an assertion about sstriples that we have proved before.\<close>
  apply (simp flip: sstriple_upwards_closure)
  done

text \<open>The weakest precondition is unchanged when passing to the upwards closure of the
post-conditions:\<close>
lemma wp_upwards_closure:
  shows \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e \<psi> (\<lambda>r. (\<rho> r \<star> \<top>)) \<theta>\<close>
    and \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e (\<lambda>r. (\<psi> r \<star> \<top>)) \<rho> \<theta>\<close>
    and \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e \<psi> \<rho> (\<lambda>a. \<theta> a \<star> \<top>)\<close>
    and \<open>(\<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>) = \<W>\<P> \<Gamma> e (\<lambda>r. (\<psi> r \<star> \<top>)) (\<lambda>r. (\<rho> r \<star> \<top>)) (\<lambda>a. (\<theta> a \<star> \<top>))\<close>
  \<comment>\<open>Here we use \<^verbatim>\<open>aentails_yonedaI\<close> to transform the goals into statements involving only
  \<^verbatim>\<open>_ \<longlongrightarrow> \<W>\<P> _\<close>. This allows us to apply the universal property \<^verbatim>\<open>sstriple_wp_iff\<close>, thereby
  reducing the statement to known upwards closure properties of sstriple:\<close>
  by (auto
    intro!: aentails_yonedaI
    simp add: sstriple_wp_iff
    simp flip: sstriple_upwards_closure)

text\<open>The transitivity/consequence rule for triples yields a similar rule for weakest preconditions.
It allows us to strengthen preconditions and weaken postconditions:\<close>

lemma wp_consequence:
  assumes \<open>\<phi>' \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi>' \<rho>' \<theta>'\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>\<And>r. \<psi>' r \<longlongrightarrow> \<psi> r\<close>
      and \<open>\<And>r. \<rho>' r \<longlongrightarrow> \<rho> r\<close>
      and \<open>\<And>r. \<theta>' r \<longlongrightarrow> \<theta> r\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
  using assms sstriple_consequence wp_is_weakest_precondition wp_to_sstriple by metis

lemma wp_weaken_crule:
  assumes \<open>\<And>x. \<alpha> x \<longlongrightarrow> \<alpha>' x\<close>
      and \<open>\<And>x. \<beta> x \<longlongrightarrow> \<beta>' x\<close>
      and \<open>\<And>x. \<gamma> x \<longlongrightarrow> \<gamma>' x\<close>
    shows \<open>\<W>\<P> \<Gamma> e \<alpha> \<beta> \<gamma> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<alpha>' \<beta>' \<gamma>'\<close>
  using assms by (meson aentails_refl_eq wp_consequence)

text\<open>Using \<^term>\<open>wp_striple_iff\<close>, we can transport some frame rules into the weakest precondition setting:\<close>

theorem wp_frame_ruleI:
  assumes \<open>\<phi>' \<longlongrightarrow> \<W>\<P> \<Gamma> e (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<psi> r) (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<rho> r) (\<lambda>r. (\<phi>' \<Zsurj> \<phi>) \<Zsurj> \<theta> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>' \<star> (\<phi>' \<Zsurj> \<phi>)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
using assms sstriple_frame_ruleI' wp_sstriple_iff by blast

theorem wp_frame_rule_asepconj_multi_singleI:
  assumes \<open>\<xi> (lst ! i) \<star> \<phi> \<longlongrightarrow>
              \<W>\<P> \<Gamma> e (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<psi> r)
                      (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<rho> r)
                      (\<lambda>r. \<star>\<star>{# \<xi> \<Colon> drop_nth i lst #} \<Zsurj> \<theta> r)\<close>
      and \<open>ucincl \<phi>\<close>
      and \<open>i < length lst\<close>
    shows \<open>\<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
using assms sstriple_frame_rule_asepconj_multi_singleI' wp_sstriple_iff by blast

lemma sstriple_pure_to_wp':
    notes asat_simp [simp]
      and asepconj_simp [simp]
  assumes \<open>ucincl (\<psi> x)\<close>
      and \<open>\<Gamma>; \<top> \<turnstile> e \<stileturn> (\<lambda>v. \<langle>v = x\<rangle>) \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
    shows \<open>\<psi> x \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; \<top> \<star> \<psi> x \<turnstile> e \<stileturn> (\<lambda>v. \<langle>v = x\<rangle> \<star> \<psi> x) \<bowtie> (\<lambda>_. \<bottom> \<star> \<psi> x) \<bowtie> (\<lambda>_. \<bottom> \<star> \<psi> x)\<close>
    by (intro sstriple_frame_rule, auto simp add: bot_fun_def)
  from assms and this show \<open>\<psi> x \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    by (intro wp_is_weakest_precondition; clarsimp)
      (rule sstriple_consequence, auto simp add: aentails_def)
qed

text \<open>This is a useful lemma for transporting Hoare triple facts of straight-line code (guaranteed
not to return) directly into WP facts using a standard pattern.\<close>
lemma sstriple_straightline_to_wp:
  notes asepconj_simp [simp]
  assumes \<open>\<Gamma>; pre \<turnstile> e \<stileturn> post \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
  shows \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn>
                          (\<lambda>v. post v \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))
                       \<bowtie> (\<lambda>_. \<bottom> \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))
                       \<bowtie> (\<lambda>_. \<bottom> \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))\<close>
    by (intro sstriple_frame_rule; clarsimp simp add: bot_fun_def ucincl_intros intro!:ucincl_Int)
  moreover have \<open>\<And>r. post r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<psi> r\<close>
    by (metis (no_types, lifting) aentails_refl aforall_entailsL asepconj_comm awand_adjoint)
  ultimately have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (simp add: aentails_refl local.bot_aentails_all local.sstriple_consequence)
  from this and assms show \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    using wp_sstriple_iff by blast
qed

lemma sstriple_straightline_to_wp_with_abort:
    notes asepconj_simp [simp]
  assumes \<open>\<Gamma>; pre \<turnstile> e \<stileturn> post \<bowtie> \<bottom> \<bowtie> ab\<close>
    shows \<open>pre \<star> ((\<Sqinter>v. post v \<Zsurj> \<psi> v)\<sqinter>(\<Sqinter>v. ab v \<Zsurj> \<theta> v)) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  let ?frame = \<open>((\<Sqinter>v. post v \<Zsurj> \<psi> v)\<sqinter>(\<Sqinter>v. ab v \<Zsurj> \<theta> v))\<close>
  from assms have A: \<open>\<Gamma>; pre \<star> ?frame \<turnstile> e \<stileturn>
                          (\<lambda>v. post v \<star> ?frame)
                       \<bowtie> (\<lambda>_. \<bottom> \<star> ?frame)
                       \<bowtie> (\<lambda>r. ab r \<star> ?frame)\<close>
    by (intro sstriple_frame_rule; clarsimp simp add: bot_fun_def ucincl_intros intro!:ucincl_Int)
  moreover have B: \<open>\<And>r. ab r \<star> ?frame \<longlongrightarrow> \<theta> r\<close>
    by (metis (no_types, lifting) aentails_refl_eq inf_commute aentails_fold_def
      aentails_inter_weaken2 aforall_entailsL asepconj_mono3)
  moreover have C: \<open>\<And>r. post r \<star> ?frame \<longlongrightarrow> \<psi> r\<close>
    by (metis (no_types, lifting) aentails_refl_eq aentails_fold_def
      aentails_inter_weaken2 aforall_entailsL asepconj_mono3)
  have \<open>\<Gamma>; pre \<star> ?frame \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using sstriple_consequence [OF A]
    by (simp add: B C aentails_refl local.bot_aentails_all)
  from this and assms show \<open>pre \<star> ?frame \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    using wp_sstriple_iff by blast
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_to_wp_frame:
  assumes \<open>\<Gamma>; pre \<turnstile> e \<stileturn> post
                        \<bowtie> (\<lambda>r. (\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<rho> r)
                        \<bowtie> (\<lambda>r. (\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<theta> r)\<close>
    shows \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn> (\<lambda>v. post v \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v')) \<bowtie>
                        (\<lambda>r. ((\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<rho> r) \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v')) \<bowtie>
                        (\<lambda>r. ((\<Sqinter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<theta> r) \<star> (\<Sqinter>v'. post v' \<Zsurj> \<psi> v'))\<close>
    by (intro sstriple_frame_rule; clarsimp simp add: ucincl_intros intro!: ucincl_Int)
  moreover have \<open>pre \<star> (\<Inter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> pre \<star> (\<Inter>v. post v \<Zsurj> \<psi> v)\<close>
    by (intro aentails_refl)
  moreover have \<open>\<And>r. post r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<psi> r\<close>
    by (meson aentails_refl local.aentails_forward local.aforall_entailsL local.asepconj_mono)
  moreover have \<open>\<And>r. (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<rho> r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<rho> r\<close>
    by (blast intro: awand_mp)
  moreover have \<open>\<And>r. (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<Zsurj> \<theta> r \<star> (\<Inter>v'. post v' \<Zsurj> \<psi> v') \<longlongrightarrow> \<theta> r\<close>
    by (blast intro: awand_mp)
  ultimately have \<open>\<Gamma>; pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (rule sstriple_consequence)
  then show \<open>pre \<star> (\<Sqinter>v. post v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> e \<psi> \<rho> \<theta>\<close>
    using assms by (auto intro!: wp_is_weakest_precondition ucincl_asepconj ucincl_Int ucincl_awand)
qed

subsection\<open>Local axioms for core expressions\<close>

text\<open>In this section, we reason on a case-by-case basis, computing the Weakest Precondition for the
expressions of the core computation language.  Note that, as many expressions are defined as abbreviations,
written in terms of a small set of core expressions that others elaborate into, we need only
consider this core set here.

First, we introduce some named collections of theorem that will be useful later, when defining
automation tactics.  We have theorem collections relating to simplification and introduction rules
for the Weakest Precondition calculus:\<close>

named_theorems separation_logic_wp_simps
named_theorems separation_logic_wp_elims
named_theorems separation_logic_wp_intros
named_theorems separation_logic_wp_case_splits

text\<open>Introduction rules introducing schematic variables. Those should be attempted after
destructing quantified assumptions, as only then the schematic may depend on the quantifiers
in the assumptions:\<close>
named_theorems separation_logic_wp_ex_intros

text\<open>Structural entailment rules used while decomposing weakest-precondition goals
belong to the generic separation-logic calculus.  Language profiles may add rules for
their own expressions, but must not be required to make these logical forms visible
to automation.\<close>

declare aexists_entailsL aexists_entailsR aforall_entailsL aforall_entailsR
  apure_entails_iff apure_entailsR [separation_logic_wp_intros]

lemma wp_literal [separation_logic_wp_simps]:
    notes asepconj_simp [simp]
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (literal v) \<psi> \<rho>  \<theta> = \<psi> v\<close>
  using assms by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_literal)

lemma wp_literal_coreI:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> v\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (literal v) \<psi> \<rho> \<theta>\<close>
using assms by (subst wp_literal)

lemma wp_literalI[separation_logic_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<psi> v \<star> \<top>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (literal v) \<psi> \<rho> \<theta>\<close>
  by (simp add: assms local.sstriple_literal local.sstriple_wp_iff)

text\<open>As immediate corollaries of the result above we have analogous results for all of our core
literal values:\<close>
lemma wp_abort [separation_logic_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (abort a) \<psi> \<rho> \<theta> = \<theta> a \<star> UNIV\<close>
  by (clarsimp intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_abort)

lemma wp_abortI [separation_logic_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> a \<star> UNIV\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (abort a) \<psi> \<rho> \<theta>\<close>
using assms by (subst wp_abort)

lemma wp_return [separation_logic_wp_simps]:
    shows \<open>\<W>\<P> \<Gamma> (return_func (literal v)) \<psi> \<rho> \<theta> = \<rho> v \<star> \<top>\<close>
by (auto intro!: aentails_yonedaI simp add: sstriple_wp_iff sstriple_return)

lemma wp_returnI [separation_logic_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<rho> v \<star> \<top>\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (return_func (literal v)) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: wp_return)

lemma wp_bind_core:
  shows \<open>\<W>\<P> \<Gamma> e (\<lambda>r. \<W>\<P> \<Gamma> (f r) \<xi> \<rho> \<theta>) \<rho> \<theta> \<longlongrightarrow>
    \<W>\<P> \<Gamma> (do { v \<leftarrow> e; f v }) \<xi> \<rho> \<theta>\<close>
  by (meson sstriple_bindI wp_is_precondition wp_sstriple_iff)

lemma aentails_cong_only_rhs:
  assumes \<open>\<psi> = \<psi>'\<close>
    shows \<open>(\<phi> \<longlongrightarrow> \<psi>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi>')\<close>
using assms by auto

lemma wp_bindI [separation_logic_wp_intros]:
    notes aentails_intro [intro]
    fixes e :: \<open>('a, 'b, 'c, 'abort,
      'i::nondeterministic_prompt, 'o::nondeterministic_response) expression\<close>
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e (\<lambda>r. \<W>\<P> \<Gamma> (f r) \<xi> \<rho> \<theta>) \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (do { v \<leftarrow> e; f v }) \<xi> \<rho> \<theta>\<close>
using assms by (blast intro: wp_bind_core)

corollary wp_sequence_core:
  shows \<open>\<W>\<P> \<Gamma> e (\<lambda>x. \<W>\<P> \<Gamma> f \<xi> \<rho> \<theta>) \<rho> \<theta> \<longlongrightarrow> \<W>\<P> \<Gamma> (sequence e f) \<xi> \<rho> \<theta>\<close>
by (auto simp add: sequence_def intro!: wp_bind_core)

lemma wp_sequenceI [separation_logic_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e (\<lambda>x. \<W>\<P> \<Gamma> f \<xi> \<rho> \<theta>) \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (sequence e f) \<xi> \<rho> \<theta>\<close>
using assms wp_sequence_core by blast

lemma wp_nondet_choiceI [separation_logic_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>is_nondet_order_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> l \<psi> \<rho> \<theta>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> r \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (nondet_choice l r) \<psi> \<rho> \<theta>\<close>
proof (intro wp_is_weakest_precondition)
  from assms(2) have l:
      \<open>\<Gamma> ; \<phi> \<turnstile> l \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (rule wp_to_sstriple)
  from assms(3) have r:
      \<open>\<Gamma> ; \<phi> \<turnstile> r \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (rule wp_to_sstriple)
  have yh_eq: \<open>\<And>\<sigma>. yh \<Gamma> nondeterministic_choice_prompt \<sigma> =
      {YieldContinue (nondeterministic_left_response, \<sigma>),
       YieldContinue (nondeterministic_right_response, \<sigma>)}\<close>
    using assms(1)
    by (simp add: is_nondet_order_yield_handler_def)
  have y:
      \<open>\<Gamma> ; \<phi> \<turnstile> yield nondeterministic_choice_prompt
        \<stileturn> (\<lambda>_. \<phi>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (simp add: sstriple_yield, intro conjI allI impI;
        auto simp add: is_local_def yh_eq
             dest: aentails_top_R'[OF aentails_refl,
                     unfolded aentails_def, rule_format])
  have k: \<open>\<And>resp. \<Gamma> ; (\<lambda>_. \<phi>) resp \<turnstile>
      (if resp = nondeterministic_left_response then l else r)
      \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using l r by (simp split: if_splits)
  from sstriple_bindI[OF y k] show \<open>\<Gamma> ; \<phi> \<turnstile> nondet_choice l r \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (simp add: nondet_choice_def)
qed

lemma wp_bind2_unseqI [separation_logic_wp_intros]:
    notes aentails_intro[intro]
  assumes \<open>is_nondet_order_yield_handler (yh \<Gamma>)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e0 (\<lambda>v0. \<W>\<P> \<Gamma> e1 (\<lambda>v1. \<W>\<P> \<Gamma> (f v0 v1) \<xi> \<rho> \<theta>) \<rho> \<theta>) \<rho> \<theta>\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> e1 (\<lambda>v1. \<W>\<P> \<Gamma> e0 (\<lambda>v0. \<W>\<P> \<Gamma> (f v0 v1) \<xi> \<rho> \<theta>) \<rho> \<theta>) \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (bind2_unseq f e0 e1) \<xi> \<rho> \<theta>\<close>
  apply (simp add: bind2_unseq_def)
  apply (intro wp_nondet_choiceI wp_is_weakest_precondition sstriple_bindI)
  apply (rule assms(1))
  apply (rule wp_to_sstriple[OF assms(2)] wp_to_sstriple[OF assms(3)] wp_is_precondition)+
  done

lemma wp_two_armed_conditional:
  shows \<open>\<W>\<P> \<Gamma> (two_armed_conditional (literal x) t f) \<psi> \<rho> \<theta>
     = (if x then \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta> else \<W>\<P> \<Gamma> f \<psi> \<rho> \<theta>)\<close>
by (cases x) (simp_all add: two_armed_conditional_def bind_literal_unit)

lemma wp_two_armed_conditionalI[separation_logic_wp_case_splits]:
  assumes \<open>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta>\<close>
      and \<open>\<not>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> f \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (two_armed_conditional (literal x) t f) \<psi> \<rho> \<theta>\<close>
by (simp add: assms wp_two_armed_conditional)

corollary wp_one_armed_conditional:
  assumes \<open>\<And>s. ucincl (\<psi> s)\<close>
  shows \<open>\<W>\<P> \<Gamma> (one_armed_conditional (literal x) t) \<psi> \<rho> \<theta> =
    (if x then \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta> else \<psi> ())\<close>
using assms by (simp add: separation_logic_wp_simps wp_two_armed_conditional)

lemma wp_one_armed_conditionalI[separation_logic_wp_case_splits]:
  assumes \<open>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta>\<close>
      and \<open>\<not>x \<Longrightarrow> \<phi> \<longlongrightarrow> \<psi> () \<star> \<top>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (one_armed_conditional (literal x) t) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_literalI wp_two_armed_conditional)

lemma wp_two_armed_conditional_thenI:
  assumes \<open>x\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> t \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (two_armed_conditional (literal x) t f) \<psi> \<rho> \<theta>\<close>
  by (simp add: assms wp_two_armed_conditional)

lemma wp_two_armed_conditional_elseI:
  assumes \<open>\<not>x\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> f \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (two_armed_conditional (literal x) t f) \<psi> \<rho> \<theta>\<close>
  by (simp add: assms wp_two_armed_conditional)

\<comment>\<open>TODO: This is not uniform with the treatment of conditionals
which are discharged using \<^verbatim>\<open>separation_logic_wp_intros\<close> rather than
\<^verbatim>\<open>separation_logic_wp_simps\<close>.\<close>
lemma wp_get:
    notes asat_simp [simp]
  assumes \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
    shows \<open>has f v \<star> (has f v \<Zsurj> \<psi> v) \<longlongrightarrow> \<W>\<P> \<Gamma> (get f) \<psi> \<rho> \<theta>\<close>
proof -
  have \<open>has f v \<star> (\<Sqinter>x. (\<langle>x=v\<rangle> \<star> has f v) \<Zsurj> \<psi> x) \<longlongrightarrow> \<W>\<P> \<Gamma> (get f) \<psi> \<rho> \<theta>\<close>
    using assms by (auto intro!: sstriple_straightline_to_wp sstriple_getI)
  moreover from assms have \<open>has f v \<star> (has f v \<Zsurj> \<psi> v) \<longlongrightarrow> has f v \<star> (\<Sqinter>x. (\<langle>x=v\<rangle> \<star> has f v) \<Zsurj> \<psi> x)\<close>
    by (clarsimp simp add: aentails_def elim!: awandE asepconjE) (force intro: asepconjI awandI)
  ultimately show ?thesis
    using aentails_trans by force
qed

lemma wp_put:
  assumes \<open>\<And>x. x \<Turnstile> has f v \<Longrightarrow> g x \<Turnstile> has f v'\<close>
      and \<open>\<And>x y. x\<sharp>y \<Longrightarrow> x \<Turnstile> has f v \<Longrightarrow> g (x+y) = g x + y \<and> g x \<sharp> y\<close>
      and \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
    shows \<open>has f v \<star> (has f v' \<Zsurj> \<psi> ()) \<longlongrightarrow> \<W>\<P> \<Gamma> (put g) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>has f v \<star> (\<Sqinter>u. has f v' \<Zsurj> \<psi> u) \<longlongrightarrow> \<W>\<P> \<Gamma> (put g) \<psi> \<rho> \<theta>\<close>
    by (auto intro!: sstriple_straightline_to_wp sstriple_putI)
  moreover from assms have \<open>has f v \<star> (has f v' \<Zsurj> \<psi> ()) \<longlongrightarrow> has f v \<star> (\<Sqinter>u. has f v' \<Zsurj> \<psi> u)\<close>
    by (auto simp add: aentails_def elim!: asepconjE awandE intro!: asepconjI awandI)
  ultimately show ?thesis
    using aentails_trans by force
qed

lemma wp_getI [separation_logic_wp_intros]:
  assumes \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
      and  \<open>\<phi> \<longlongrightarrow> has f v \<star> (has f v \<Zsurj> \<psi> v)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (get f) \<psi> \<rho> \<theta>\<close>
using assms by (force intro: aentails_trans' wp_get)

lemma wp_putI:
  assumes \<open>\<And>x. x \<Turnstile> has f v \<Longrightarrow> g x \<Turnstile> has f v'\<close>
      and \<open>\<And>x y. x\<sharp>y \<Longrightarrow> x \<Turnstile> has f v \<Longrightarrow> g (x+y) = g x + y \<and> g x \<sharp> y\<close>
      and \<open>ucincl (has f v)\<close>
      and \<open>\<And>x. ucincl (\<psi> x)\<close>
      and \<open>\<phi> \<longlongrightarrow> has f v \<star> (has f v' \<Zsurj> \<psi> ())\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (put g) \<psi> \<rho> \<theta>\<close>
using assms by - (rule aentails_trans', rule wp_put, auto)

lemma wp_fun [separation_logic_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (funcall0 f) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (call f) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall1 f1 (literal a0)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f1 a0)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall2 f2 (literal a0) (literal a1)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f2 a0 a1)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall3 f3 (literal a0) (literal a1) (literal a2)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f3 a0 a1 a2)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall4 f4 (literal a0) (literal a1) (literal a2) (literal a3)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f4 a0 a1 a2 a3)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall5 f5 (literal a0) (literal a1) (literal a2) (literal a3) (literal a4)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f5 a0 a1 a2 a3 a4)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall6 f6 (literal a0) (literal a1) (literal a2) (literal a3) (literal a4) (literal a5)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f6 a0 a1 a2 a3 a4 a5)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall7 f7 (literal a0) (literal a1) (literal a2) (literal a3) (literal a4) (literal a5) (literal a6)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f7 a0 a1 a2 a3 a4 a5 a6)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall8 f8 (literal a0) (literal a1) (literal a2) (literal a3) (literal a4) (literal a5) (literal a6) (literal a7)) \<phi> \<rho> \<theta> = \<W>\<P> \<Gamma> (funcall0 (f8 a0 a1 a2 a3 a4 a5 a6 a7)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall9 f9 (literal a0) (literal a1) (literal a2) (literal a3) (literal a4) (literal a5) (literal a6) (literal a7) (literal a8)) \<phi> \<rho> \<theta> =
           \<W>\<P> \<Gamma> (funcall0 (f9 a0 a1 a2 a3 a4 a5 a6 a7 a8)) \<phi> \<rho> \<theta>\<close>
    and \<open>\<W>\<P> \<Gamma> (funcall10 f10 (literal a0) (literal a1) (literal a2) (literal a3) (literal a4) (literal a5) (literal a6) (literal a7) (literal a8) (literal a9)) \<phi> \<rho> \<theta> =
           \<W>\<P> \<Gamma> (funcall0 (f10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)) \<phi> \<rho> \<theta>\<close>
by (simp only: shallow_computation_simps)+

text\<open>This rule is useful for unfolding the definition of a called function and reasoning about it
directly.\<close>
lemma wp_call_function_body:
  shows \<open>\<W>\<P> \<Gamma> f \<psi> \<psi> \<theta> \<longlongrightarrow> \<W>\<P> \<Gamma> (call (FunctionBody f)) \<psi> \<rho> \<theta>\<close>
  by (clarsimp intro!: aentails_yonedaI sstriple_callI simp add: sstriple_wp_iff
    wp_is_precondition)

\<comment> \<open>NB We don't mark this as an introduction rule because for some functions
we want to invoke a function contract rather than unfolding their definition.\<close>
corollary wp_call_function_bodyI:
    notes aentails_intro [intro]
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (function_body f) \<psi> \<psi> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms wp_call_function_body by (cases f; clarsimp) blast

\<comment>\<open>The following formulation is useful in the presence of a list of definitions for functions
to be inlined, one of which will discharge the first generated assumption.\<close>
corollary wp_call_inlineI:
  assumes \<open>f \<equiv> FunctionBody b\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> b \<psi> \<psi> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by (clarsimp intro!: wp_call_function_bodyI)

corollary wp_call_inline'I:
  assumes \<open>f \<equiv> g\<close>
      and \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call g) \<psi> \<rho> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by clarsimp

corollary wp_call_function_bodyI2 [separation_logic_wp_intros]:
    notes aentails_intro [intro]
  assumes \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> f \<psi> \<psi> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call (FunctionBody f)) \<psi> \<rho> \<theta>\<close>
using assms wp_call_function_body by (cases f; clarsimp) blast

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma wp_satisfies_function_contract_direct:
    notes asat_simp [simp]
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
      and pre: \<open>\<phi> \<longlongrightarrow> function_contract_pre \<C>\<close>
      and post: \<open>\<And>r. function_contract_post \<C> r \<longlongrightarrow> \<psi> r\<close>
      and abort: \<open>\<And>r. function_contract_abort \<C> r \<longlongrightarrow> \<theta> r\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>\<Gamma>; function_contract_pre \<C> \<turnstile> call f \<stileturn> function_contract_post \<C> \<bowtie> \<rho> \<bowtie> function_contract_abort \<C>\<close>
    by (auto elim!: satisfies_function_contractE)
  note X = this
  have \<open>\<Gamma>; \<phi> \<turnstile> call f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using sstriple_consequence[OF X pre post aentails_refl abort] by simp
  from this show ?thesis
    by (simp add: wp_sstriple_iff)
qed

lemma wp_satisfies_function_contract:
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>function_contract_pre \<C> \<star> ((\<Sqinter>r. function_contract_post \<C> r \<Zsurj> \<psi> r)
                                   \<sqinter>(\<Sqinter>r. function_contract_abort \<C> r \<Zsurj> \<theta> r))
           \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by (elim satisfies_function_contractE,
   intro sstriple_straightline_to_wp_with_abort, auto)

lemma wp_call_with_abortI:
  assumes A: \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
      and B: \<open>\<phi> \<longlongrightarrow> function_contract_pre \<C> \<star>
           ((\<Sqinter>r. function_contract_post \<C> r \<Zsurj> \<psi> r)
           \<sqinter>(\<Sqinter>r. function_contract_abort \<C> r \<Zsurj> \<theta> r))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  by (intro aentails_trans[OF _ wp_satisfies_function_contract[OF A]], simp add: B)

lemma wp_callI:
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
      and \<open>function_contract_abort \<C> = \<bottom>\<close>
      and \<open>\<phi> \<longlongrightarrow> function_contract_pre \<C> \<star> (\<Sqinter>r. function_contract_post \<C> r \<Zsurj> \<psi> r)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (call f) \<psi> \<rho> \<theta>\<close>
  using assms by - (intro wp_call_with_abortI, assumption, simp add: awand_bot)

lemma wp_funliteral:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (funcall1 (lift_fun1 f1) (literal v0)) \<psi> \<rho> \<theta> = \<psi> (f1 v0)\<close>
      and \<open>\<W>\<P> \<Gamma> (funcall2 (lift_fun2 f2) (literal v0) (literal v1)) \<psi> \<rho> \<theta> = \<psi> (f2 v0 v1)\<close>
      and \<open>\<W>\<P> \<Gamma> (funcall3 (lift_fun3 f3) (literal v0) (literal v1) (literal v2)) \<psi> \<rho> \<theta> = \<psi> (f3 v0 v1 v2)\<close>
      and \<open>\<W>\<P> \<Gamma> (funcall4 (lift_fun4 f4) (literal v0) (literal v1) (literal v2) (literal v3)) \<psi> \<rho> \<theta> = \<psi> (f4 v0 v1 v2 v3)\<close>
      and \<open>\<W>\<P> \<Gamma> (funcall5 (lift_fun5 f5) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4)) \<psi> \<rho> \<theta> = \<psi> (f5 v0 v1 v2 v3 v4)\<close>
      and \<open>\<W>\<P> \<Gamma> (funcall6 (lift_fun6 f6) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4) (literal v5)) \<psi> \<rho> \<theta> = \<psi> (f6 v0 v1 v2 v3 v4 v5)\<close>
      and \<open>\<W>\<P> \<Gamma> (funcall7 (lift_fun7 f7) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4) (literal v5) (literal v6)) \<psi> \<rho> \<theta> = \<psi> (f7 v0 v1 v2 v3 v4 v5 v6)\<close>
      and \<open>\<W>\<P> \<Gamma> (funcall8 (lift_fun8 f8) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4) (literal v5) (literal v6) (literal v7)) \<psi> \<rho> \<theta> = \<psi> (f8 v0 v1 v2 v3 v4 v5 v6 v7)\<close>
  using assms by (clarsimp intro!: aentails_yonedaI simp add: sstriple_wp_iff
    sstriple_call_funliteral asepconj_simp)+

lemma wp_op_eq [separation_logic_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (funcall2 (lift_fun2 (\<lambda>a b. a = b)) (literal e) (literal f))
      \<psi> \<rho> \<theta> = \<psi> (e = f)\<close>
using assms by (clarsimp simp add: wp_funliteral)

subsection\<open>Loops\<close>

text\<open>Note that this is not added to \<^verbatim>\<open>separation_logic_wp_intros\<close>. The invariant pretty much always needs
to be provided, so there is not much point.\<close>
lemma wp_raw_for_loopI:
    notes aentails_intro [intro]
      and aentails_simp [simp]
      and asepconj_simp [simp]
  assumes \<open>\<And>past todo. ucincl (INV past todo)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV [] xs\<close>
      and \<open>\<And>past cur todo. xs = past@(cur#todo) \<Longrightarrow> INV past (cur#todo) \<longlongrightarrow> \<W>\<P> \<Gamma> (f cur) (\<lambda>_. INV (past@[cur]) todo) \<rho> \<theta>\<close>
      and \<open>INV xs [] \<longlongrightarrow> \<psi> ()\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have H: \<open>\<Gamma> ; \<langle>xs = []@xs\<rangle> \<star> INV [] xs \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. \<langle>xs = xs@[]\<rangle> \<star> INV xs []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (intro sstriple_raw_for_loop) (force intro: ucincl_intros wp_to_sstriple)
  from assms have \<open>INV [] xs \<longlongrightarrow>  \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<theta>\<close>
    by (intro wp_is_weakest_precondition; clarsimp intro: ucincl_intros)
      (rule sstriple_consequence[OF H]; clarsimp simp add: aentails_refl)
  from this and assms show ?thesis
    by blast
qed

text\<open>The following is a framed version of \<^text>\<open>wp_raw_for_loopI\<close> recovering the latter if
\<^term>\<open>\<xi> = UNIV\<close>.\<close>
lemma wp_raw_for_loop_framedI:
  assumes \<open>\<And>past todo. ucincl (INV past todo)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>ucincl (\<psi> ())\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV [] xs \<star> ((INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>past cur todo. INV past (cur#todo) \<longlongrightarrow> \<W>\<P> \<Gamma> (f cur) (\<lambda>_. INV (past@[cur]) todo) \<tau> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
proof -
  let ?pc = \<open>((INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  from assms have \<open>\<Gamma> ; INV [] xs \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (intro sstriple_raw_for_loop_framed) (auto simp add: local.wp_to_sstriple ucincl_intros)
  from this and assms have \<open>INV [] xs \<star> ?pc \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
    using local.ucincl_asepconj wp_is_weakest_precondition by (metis (mono_tags, lifting)
      ucincl_Int local.ucincl_IntE local.ucincl_awand local.ucincl_inter)
  from this and assms show ?thesis
    by (meson assms ucincl_asepconj ucincl_awand aentails_trans')
qed

text\<open>Alternative loop rule which might be easier to use in some situations. Passing the list to the
invariant may seem redundant because it's part of the context, but we don't always know what the
list will be named in the current proof state.\<close>
lemma wp_raw_for_loop_framedI':
    fixes xs :: \<open>'e list\<close>
      and INV :: \<open>'e list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>ls i. ucincl (INV ls i)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>ucincl (\<psi> ())\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV xs 0 \<star> ((INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>i. i < length xs \<Longrightarrow> INV xs i \<longlongrightarrow> \<W>\<P> \<Gamma> (f (xs ! i)) (\<lambda>_. INV xs (i+1)) \<tau> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
proof -
  let ?pc = \<open>((INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  from assms have \<open>\<Gamma> ; INV xs 0 \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (intro sstriple_raw_for_loop_framed') (auto simp add: local.wp_to_sstriple ucincl_intros)
  from this and assms have \<open>INV xs 0 \<star> ?pc \<longlongrightarrow> \<W>\<P> \<Gamma> (raw_for_loop xs f) \<psi> \<rho> \<chi>\<close>
    by (intro wp_is_weakest_precondition) (auto intro!: ucincl_Int ucincl_awand ucincl_inter
      ucincl_asepconj)
  from this and assms show ?thesis
    by (meson assms ucincl_asepconj ucincl_awand aentails_trans')
qed

subsection\<open>Bounded while loops\<close>

lemma wp_bounded_while_framedI:
    fixes INV :: \<open>nat \<Rightarrow> 'a assert\<close>
      and INV' :: \<open>nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>k. ucincl (INV k)\<close>
      and \<open>\<And>k. ucincl (INV' k)\<close>
      and \<open>\<And>r. ucincl (\<rho> r)\<close>
      and \<open>ucincl (\<psi> ())\<close>
      and \<open>\<And>r. ucincl (\<tau> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> INV n \<star> ((INV 0 \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
      and \<open>\<And>k. k < n \<Longrightarrow>
            INV (Suc k) \<longlongrightarrow> \<W>\<P> \<Gamma> cond (\<lambda>c.
              if c then INV' k else INV 0) \<tau> \<theta>\<close>
      and \<open>\<And>k. k < n \<Longrightarrow>
            INV' k \<longlongrightarrow> \<W>\<P> \<Gamma> body (\<lambda>_. INV k) \<tau> \<theta>\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (bounded_while n cond body) \<psi> \<rho> \<chi>\<close>
proof -
  let ?pc = \<open>((INV 0 \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))\<close>
  from assms have \<open>\<Gamma> ; INV n \<star> ?pc \<turnstile> bounded_while n cond body \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    by (intro sstriple_bounded_while_framed[where INV'=INV'])
       (auto simp add: local.wp_to_sstriple ucincl_intros)
  from this and assms have \<open>INV n \<star> ?pc \<longlongrightarrow> \<W>\<P> \<Gamma> (bounded_while n cond body) \<psi> \<rho> \<chi>\<close>
    by (intro wp_is_weakest_precondition) (auto intro!: ucincl_Int ucincl_awand ucincl_inter
      ucincl_asepconj)
  from this and assms show ?thesis
    by (meson assms ucincl_asepconj ucincl_awand aentails_trans')
qed

(*<*)
end
(*>*)

(*<*)
end
(*>*)
