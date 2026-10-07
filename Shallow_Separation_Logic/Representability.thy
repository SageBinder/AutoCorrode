(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Representability
  imports Shallow_State_Logic.Assertion_Language Triple
begin

subsection\<open>A representability criterion for predicates on assertions\<close>

text\<open>This section, which can be safely skipped, lays out some intuition, rationale, and potential
for generalization behind the definition of the weakest precondition.

The overall goal of the weakest precondition calculus is to reduce questions about triples
\<^term>\<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close> to questions of ordinary entailment \<^term>\<open>(\<longlongrightarrow>)\<close>: For \<^emph>\<open>fixed\<close>
\<^term>\<open>\<Gamma>\<close>, \<^term>\<open>e\<close>, \<^term>\<open>\<psi>\<close> and \<^term>\<open>\<rho>\<close>, we seek to find an assertion \<^verbatim>\<open>\<wp>\<close> so that for any
\<^term>\<open>\<phi>\<close>, \<^term>\<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close> is equivalent to \<^verbatim>\<open>\<phi> \<longlongrightarrow> \<wp>\<close>.

The underlying problem, here, has little to do with the striple itself: Given a
a predicate \<^term>\<open>T\<close> on assertions assigning to each, we ask whether there is an assertion \<^verbatim>\<open>\<wp>\<^sub>T\<close>
so that \<^term>\<open>T \<phi>\<close> is equivalent to \<^verbatim>\<open>\<phi> \<longlongrightarrow> \<wp>\<^sub>T\<close>. In our case, \<^term>\<open>T\<close> is the striple, and
\<^term>\<open>(\<longlongrightarrow>)\<close> is entailment, but other predicates \<^term>\<open>T\<close> or relations \<^term>\<open>(\<longlongrightarrow>)\<close> could be
considered as well: Most generally, we're looking at the question of functor representability.\<close>

type_synonym 't afunctor = \<open>'t assert \<Rightarrow> bool\<close>

definition representable_afunctor :: \<open>'t assert \<Rightarrow> 't afunctor\<close> where
  \<open>representable_afunctor \<phi> \<equiv> \<lambda>\<psi>. \<psi> \<longlongrightarrow> \<phi>\<close>

definition is_representable :: \<open>'t afunctor \<Rightarrow> bool\<close> where
  \<open>is_representable T \<equiv> \<exists>\<phi>. T = representable_afunctor \<phi>\<close>

definition is_contravariant :: \<open>'t afunctor \<Rightarrow> bool\<close> where
  \<open>is_contravariant T \<equiv> \<forall>\<phi> \<psi>. \<phi> \<longlongrightarrow> \<psi> \<longrightarrow> T \<psi> \<longrightarrow> T \<phi>\<close>

lemma representable_afunctor_is_contravariant:
  assumes \<open>is_representable T\<close>
    shows \<open>is_contravariant T\<close>
using assms aentails_trans by (auto simp add: is_representable_def is_contravariant_def
  representable_afunctor_def)

text\<open>If a functor is representable, one can explicitly write down its representing assertion
in terms of the functor itself:\<close>
definition afunctor_sup :: \<open>'t afunctor \<Rightarrow> 't assert\<close> where
  \<open>afunctor_sup T \<equiv> \<Squnion>\<phi>\<in>{\<phi>. T \<phi>}. \<phi>\<close>

lemma afunctor_sup_transformation:
  assumes \<open>T \<phi>\<close>
    shows \<open>\<phi> \<longlongrightarrow> afunctor_sup T\<close>
using assms by (auto simp add: afunctor_sup_def aentails_def asat_def)

lemma afunctor_sup_representable:
  shows \<open>afunctor_sup (representable_afunctor \<phi>) = \<phi>\<close>
by (auto simp add: is_representable_def representable_afunctor_def afunctor_sup_def
  aentails_def asat_def)

text\<open>The following theorem makes precise that \<^term>\<open>afunctor_sup T\<close> is the only candidate
for the representing assertion for a functor:\<close>
lemma afunctor_unique_representability:
  shows \<open>is_representable T \<longleftrightarrow> T = representable_afunctor (afunctor_sup T)\<close>
proof 
  assume \<open>is_representable T\<close>
  then show \<open>T = representable_afunctor (afunctor_sup T)\<close>
    by (auto simp add: is_representable_def representable_afunctor_def afunctor_sup_def
        aentails_def asat_def)
next
  assume \<open>T = representable_afunctor (afunctor_sup T)\<close>
  then show \<open>is_representable T\<close>
    using is_representable_def by auto
qed

text\<open>We end with a representability criterion for functors:\<close>
definition is_sup_stable :: \<open>'t afunctor \<Rightarrow> bool\<close> where
  \<open>is_sup_stable T \<equiv> \<forall>\<Phi>. (\<forall>\<phi>\<in>\<Phi>. T \<phi>) \<longrightarrow> T (\<Union>\<Phi>)\<close>

lemma afunctor_supI:
  assumes \<open>is_sup_stable T\<close>
      and \<open>\<And>\<phi>. \<phi> \<in> \<Phi> \<Longrightarrow> T \<phi>\<close>
    shows \<open>T (\<Union>\<Phi>)\<close>
using assms by (auto simp add: is_sup_stable_def)

lemma is_representable_implies_sup_stable:
  assumes \<open>is_representable T\<close>
    shows \<open>is_sup_stable T\<close>
using assms by (auto simp add: is_representable_def is_sup_stable_def representable_afunctor_def
  aentails_def asat_def)

lemma afunctor_representability_criterion:
  assumes \<open>is_contravariant T\<close>
      and \<open>is_sup_stable T\<close>
    shows \<open>is_representable T\<close>
proof -
  let ?\<tau> = \<open>afunctor_sup T\<close>
  from assms have \<open>T ?\<tau>\<close>
    by (auto intro!: afunctor_supI simp add: afunctor_sup_def)
  moreover from this and assms have \<open>\<And>\<phi>. \<phi> \<longlongrightarrow> ?\<tau> \<Longrightarrow> T \<phi>\<close>
    by (simp add: is_contravariant_def)
  moreover from this and afunctor_sup_transformation have \<open>T = representable_afunctor ?\<tau>\<close>
    by (auto simp add: representable_afunctor_def)
  ultimately show ?thesis
    unfolding is_representable_def by auto
qed

lemma afunctor_representability_iff:
  assumes \<open>is_representable T\<close>
  shows \<open>\<And>\<phi>. (\<phi> \<longlongrightarrow> afunctor_sup T) \<longleftrightarrow> T \<phi>\<close>
  using assms by (clarsimp simp add: fun_eq_iff afunctor_unique_representability
    representable_afunctor_def)

text \<open>Note that the above argument does not use anything about \<^term>\<open>(\<longlongrightarrow>)\<close> other than it defining
a complete lattice, and the 'representability theorem' trivially extends to this setting.\<close>

end
