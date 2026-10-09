(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Triple
  imports Shallow_State_Logic.Assertion_Language Shallow_Computation.Shallow_Computation Precision Weak_Triple
begin
(*>*)

section\<open>Triples\<close>

subsection\<open>Evaluation predicates\<close>

(*<*)
context sepalg begin
(*>*)

abbreviation expression_is_local where
  \<open>expression_is_local \<Gamma> e \<phi> \<equiv>
     is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,e\<rangle> (v,\<sigma>')) \<phi> \<and>
     is_local (\<lambda>\<sigma> (r, \<sigma>'). \<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,e\<rangle> (r,\<sigma>')) \<phi> \<and>
     is_local (\<lambda>\<sigma> (a, \<sigma>'). \<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,e\<rangle> (a,\<sigma>')) \<phi>\<close>

lemma expression_is_local_weaken:
  assumes \<open>\<phi>' \<longlongrightarrow> \<phi>\<close>
      and \<open>expression_is_local \<Gamma> e \<phi>\<close>
    shows \<open>expression_is_local \<Gamma> e \<phi>'\<close>
  using assms by (clarsimp simp add: is_local_weaken)

lemma expression_is_local_Union:
  assumes \<open>\<And>x. expression_is_local \<Gamma> e (\<phi> x)\<close>
    shows \<open>expression_is_local \<Gamma> e (\<Union>x. \<phi> x)\<close>
  using assms by (simp add: is_local_Union)

definition sstriple ::
     \<open>('a, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response)
        striple_context \<Rightarrow> \<comment> \<open>Fixed context for this verification\<close>
      'a assert \<Rightarrow> \<comment> \<open>The property of the pre-state\<close>
      ('a, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>Expanded out our expression type\<close>
      ('v \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The property of the post-state after successful execution\<close>
      ('r \<Rightarrow> 'a assert) \<Rightarrow> \<comment> \<open>The property of the post-state after successful early return\<close>
      ('abort abort \<Rightarrow> 'a assert) \<Rightarrow>
      bool\<close> ("(_) ; (_) /\<turnstile>/ (_) /\<stileturn>/ (_) /\<bowtie>/ (_) /\<bowtie>/ (_)" [50,50,50,50,50,50]50) where
  \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta> \<equiv> (
     \<phi> \<turnstile> eval_value (yh \<Gamma>) e \<stileturn>\<^sub>R \<psi> \<and>
     \<phi> \<turnstile> eval_return (yh \<Gamma>) e \<stileturn>\<^sub>R \<xi> \<and>
     \<phi> \<turnstile> eval_abort (yh \<Gamma>) e \<stileturn>\<^sub>R \<theta>)\<close>

lemma sstripleI:
  assumes \<open>\<phi> \<turnstile> eval_value (yh \<Gamma>) e \<stileturn>\<^sub>R \<psi>\<close>
      and \<open>\<phi> \<turnstile> eval_return (yh \<Gamma>) e \<stileturn>\<^sub>R \<xi>\<close>
      and \<open>\<phi> \<turnstile> eval_abort (yh \<Gamma>) e \<stileturn>\<^sub>R \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
using assms sstriple_def by blast

lemma sstriple_upwards_closure:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<star> \<top> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> (\<lambda>r. \<psi> r \<star> \<top>) \<bowtie> \<xi> \<bowtie> \<theta>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> (\<lambda>r. \<xi> r \<star> \<top>) \<bowtie> \<theta>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> (\<lambda>a. \<theta> a \<star> \<top>))\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>) \<longleftrightarrow> (\<Gamma> ; \<phi> \<turnstile> e \<stileturn> (\<lambda>r. \<psi> r \<star> \<top>) \<bowtie> (\<lambda>r. \<xi> r \<star> \<top>) \<bowtie> (\<lambda>a. \<theta> a \<star> \<top>))\<close>
  by (auto simp add: sstriple_def atriple_rel_upwards_closure' asepconj_simp)

lemma sstriple_striple:
  fixes \<Gamma> :: \<open>('a, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response)
    striple_context\<close>
    and \<phi> :: \<open>'a assert\<close>
    and e :: \<open>('a, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    and \<psi> :: \<open>'v \<Rightarrow> 'a assert\<close>
    and \<xi> :: \<open>'r \<Rightarrow> 'a assert\<close>
    and \<theta> :: \<open>'abort abort \<Rightarrow> 'a assert\<close>
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>) \<longleftrightarrow>
           (\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta> \<and> is_local (eval_value (yh \<Gamma>) e) \<phi>
                                        \<and> is_local (eval_return (yh \<Gamma>) e) \<phi>
                                        \<and> is_local (eval_abort (yh \<Gamma>) e) \<phi>)\<close>
   (is \<open>?a \<longleftrightarrow> ?b\<close>)
proof -
  { assume SS: \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
    then have \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      by (intro striple_localI'; auto simp add: sstriple_def atriple_rel_def
        eval_value_def eval_return_def eval_abort_def asepconj_weakenI)
    moreover from SS have \<open>is_local (eval_value (yh \<Gamma>) e) \<phi>\<close>
                      and \<open>is_local (eval_return (yh \<Gamma>) e) \<phi>\<close>
                      and \<open>is_local (eval_abort (yh \<Gamma>) e) \<phi>\<close>
      by (auto simp add: atriple_rel_def sstriple_def)
    ultimately have \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta> \<and> is_local (eval_value (yh \<Gamma>) e) \<phi>
                                                  \<and> is_local (eval_return (yh \<Gamma>) e) \<phi>
                                                  \<and> is_local (eval_abort (yh \<Gamma>) e) \<phi>)\<close>
      by auto }
  moreover {
    assume S: \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>is_local (eval_value (yh \<Gamma>) e) \<phi>\<close>
      and \<open>is_local (eval_return (yh \<Gamma>) e) \<phi>\<close>
      and \<open>is_local (eval_abort (yh \<Gamma>) e) \<phi>\<close>
    then have \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      by (intro sstripleI; clarsimp simp add: atriple_rel_def eval_value_def eval_return_def
        eval_abort_def striple_def atriple_def shallow_computation_eval_action_via_predicate ucincl_UNIV
        asepconj_weakenI)
  }
  ultimately show ?thesis
    by auto
qed

lemma sstriple_implies_is_local:
  assumes \<open>\<Gamma>; \<phi> \<turnstile> e \<stileturn> \<alpha> \<bowtie> \<beta> \<bowtie> \<gamma>\<close>
  shows \<open>expression_is_local (yh \<Gamma>) e \<phi>\<close>
  using assms by (simp add: sstriple_striple eval_abort_def eval_return_def eval_value_def)

lemma sstriple_striple':
  fixes \<Gamma> :: \<open>('a, 'abort, 'i::nondeterministic_prompt, 'o::nondeterministic_response)
    striple_context\<close>
    and \<phi> :: \<open>'a assert\<close>
    and e :: \<open>('a, 'v, 'r, 'abort, 'i, 'o) expression\<close>
    and \<psi> :: \<open>'v \<Rightarrow> 'a assert\<close>
    and \<xi> :: \<open>'r \<Rightarrow> 'a assert\<close>
    and \<theta> :: \<open>'abort abort \<Rightarrow> 'a assert\<close>
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>) \<longleftrightarrow>
           (\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta> \<and> expression_is_local (yh \<Gamma>) e \<phi>)\<close>
  by (clarsimp simp add: sstriple_striple eval_value_def eval_abort_def eval_return_def)

lemma sstriple_from_stripleI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>is_local (eval_value (yh \<Gamma>) e) \<phi>\<close>
      and \<open>is_local (eval_return (yh \<Gamma>) e) \<phi>\<close>
      and \<open>is_local (eval_abort (yh \<Gamma>) e) \<phi>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
  using assms sstriple_striple by blast

lemma striple_from_sstripleI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
  using assms sstriple_striple by blast

lemma sstriple_satisfiable:
  assumes \<open>striple_context_no_yield ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<theta>\<close>
      and \<open>is_sat \<phi>\<close>
      and \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<And>r. ucincl (\<xi> r)\<close>
      and \<open>\<And>a. ucincl (\<theta> a)\<close>
    shows \<open>(\<exists>v. is_sat (\<psi> v)) \<or> (\<exists>r. is_sat (\<xi> r)) \<or> (\<exists>a. is_sat (\<theta> a))\<close>
  using assms striple_satisfiable striple_from_sstripleI by blast

subsection \<open>Basic properties of \<^term>\<open>sstriple\<close>\<close>

text\<open>When proving a triple, one can without loss of generality assume that the spatial
precondition of the triple is satisfiable.\<close>
lemma sstriple_assume_is_sat:
  assumes \<open>is_sat \<phi> \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (meson aentails_is_sat is_local_empty is_local_weaken striple_assume_is_sat sstriple_striple)

lemma sstriple_existsI:
  assumes \<open>(\<And>x. \<Gamma> ; \<phi> x \<turnstile> e \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; (\<Union>x. \<phi> x) \<turnstile> e \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (simp add: local.is_local_bUnion local.striple_bexistsI sstriple_striple)

lemma sstriple_existsI':
  assumes \<open>(\<And>\<phi>. \<phi> \<in> \<Phi> \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; (\<Union>\<Phi>) \<turnstile> e \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (simp add: local.is_local_Union' local.striple_existsI' sstriple_striple)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_bexistsI:
  assumes \<open>(\<And>x. x\<in>S \<Longrightarrow> \<Gamma> ; \<phi> x \<turnstile> e \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; (\<Union>x\<in>S. \<phi> x) \<turnstile> e \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (metis (mono_tags, lifting) imageE sstriple_existsI')

subsection\<open>Structural rules\<close>

text\<open>This is the rule of consequence, which allows you to strengthen the preconditions of an
expression's execution and strengthen the postcondition:\<close>
lemma sstriple_consequence:
  assumes \<open>\<Gamma> ; \<phi>' \<turnstile> e \<stileturn> \<psi>' \<bowtie> \<rho>' \<bowtie> \<theta>'\<close>
      and \<open>\<phi> \<longlongrightarrow> \<phi>'\<close>
      and \<open>\<And>r. \<psi>' r \<longlongrightarrow> \<psi> r\<close>
      and \<open>\<And>r. \<rho>' r \<longlongrightarrow> \<rho> r\<close>
      and \<open>\<And>a. \<theta>' a \<longlongrightarrow> \<theta> a\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using assms is_local_weaken by (intro sstriple_from_stripleI; clarsimp simp add: sstriple_striple
  striple_consequence)

text\<open>NB: this is expressed in a non-standard form as it's used to derive other results below by
unifying against the premiss of another theorem.\<close>
lemma sstriple_consequence_wrap:
  shows \<open>\<forall>\<phi> \<psi> \<rho> \<theta> \<psi>' \<rho>' \<theta>' \<phi>' e \<Gamma>.
     sstriple \<Gamma> \<phi>' e \<psi>' \<rho>' \<theta>'
      \<longrightarrow> \<phi> \<longlongrightarrow> \<phi>'
      \<longrightarrow> (\<forall>r. \<psi>' r \<longlongrightarrow> \<psi> r)
      \<longrightarrow> (\<forall>r. \<rho>' r \<longlongrightarrow> \<rho> r)
      \<longrightarrow> (\<forall>a. \<theta>' a \<longlongrightarrow> \<theta> a)
      \<longrightarrow> sstriple \<Gamma> \<phi> e \<psi> \<rho> \<theta>\<close>
using sstriple_consequence by blast

theorem sstriple_frame_rule:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<star> \<xi> \<turnstile> e \<stileturn> (\<lambda>r. \<psi> r \<star> \<xi>) \<bowtie> (\<lambda>r. \<rho> r \<star> \<xi>)\<bowtie> (\<lambda>a. \<theta> a \<star> \<xi>)\<close>
  using assms by (intro sstriple_from_stripleI; clarsimp simp add: sstriple_striple
      striple_frame_rule is_local_frame)

text\<open>NB: this is expressed in a non-standard form as it's used to derive other results below by
unifying against the premiss of another theorem.\<close>
theorem sstriple_frame_rule_wrap:
  shows \<open>\<forall>\<phi> \<psi> \<rho> \<theta> \<xi> \<Gamma> e. sstriple \<Gamma> \<phi> e \<psi> \<rho> \<theta>
     \<longrightarrow> sstriple \<Gamma> (\<phi> \<star> \<xi>) e (\<lambda>v. \<psi> v \<star> \<xi>) (\<lambda>r. \<rho> r \<star> \<xi>) (\<lambda>a. \<theta> a \<star> \<xi>)\<close>
  by (simp add: sstriple_frame_rule)

lemmas sstriple_frame_rule' = triple_frame_rule'
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]
lemmas sstriple_frame_ruleI = triple_frame_ruleI
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]
lemmas sstriple_frame_ruleI' = triple_frame_ruleI'
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]
lemmas sstriple_frame_rule_asepconj_multi_singleI' =
  triple_frame_rule_asepconj_multi_singleI'
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]
lemmas sstriple_frame_rule_asepconj_multi =
  triple_frame_rule_asepconj_multi_singleI'
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]
lemmas sstriple_frame_rule_asepconj_multi_single =
  triple_frame_rule_asepconj_multi_single
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]
lemmas sstriple_frame_rule_no_value =
  triple_frame_rule_no_value
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]
lemmas sstriple_frame_rule_no_return =
  triple_frame_rule_no_return
  [OF sstriple_consequence_wrap, OF sstriple_frame_rule_wrap]

subsection\<open>Local axioms for core expressions in SSA form:\<close>

text\<open>This is the ``fundamental result'' here, as most other shallow-language constructs are defined in
terms of the monadic bind.  Note that this is the rule for \<^verbatim>\<open>let\<close> in disguise.\<close>
lemma sstriple_bindI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<And>x. \<Gamma> ; \<psi> x \<turnstile> f x \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>   \<comment> \<open>Case of continuation into \<^term>\<open>f\<close>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> Core_Expression.bind e f \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms by (clarsimp simp add: sstriple_def shallow_computation_eval_predicate_simps
    atriple_rel_bind atriple_rel_disj)

text\<open>This is basically the \<^verbatim>\<open>sstriple_bindI\<close> theorem in a (thin) disguise:\<close>
corollary sstriple_sequenceI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<Gamma> ; \<psi> () \<turnstile> f \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<And>r. \<rho> r = \<xi> r\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> sequence e f \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms unfolding sequence_def by (auto intro: sstriple_bindI)

text\<open>The \<^verbatim>\<open>skip\<close> command does not modify the state in any way, and always succeeds:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_skipI:
  shows \<open>\<Gamma> ; \<psi> \<turnstile> skip \<stileturn> (\<lambda>_. \<psi>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (auto intro!: sstriple_from_stripleI striple_skipI
      simp add: eval_value_def eval_return_def eval_abort_def eval_predicate_skip is_local_def)

text\<open>Executing a literal does not modify the state in anyway way, but does return the literal value.
It also always succeeds:\<close>
lemma sstriple_literalI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> literal v \<stileturn> (\<lambda>rv. \<langle>rv = v\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (auto intro: sstriple_from_stripleI striple_literalI
      simp add: eval_predicate_literal is_local_def eval_value_def eval_return_def eval_abort_def)

lemma sstriple_literal:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> literal v \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> v \<star> \<top>)\<close>
proof (intro iffI)
  show \<open>\<Gamma> ; \<phi> \<turnstile> literal v \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta> \<Longrightarrow> \<phi> \<longlongrightarrow> \<psi> v \<star> UNIV\<close>
    by (simp add: local.striple_literal sstriple_striple')
  show \<open>\<phi> \<longlongrightarrow> \<psi> v \<star> UNIV \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> literal v \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (meson aentails_true is_local_weaken striple_literal sstriple_literalI sstriple_striple)
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_return_valI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> return_val v \<stileturn> \<psi> \<bowtie> (\<lambda>rv. \<langle>rv = v\<rangle>) \<bowtie> \<theta>\<close>
  by (auto intro!: sstriple_from_stripleI striple_return_valI
      simp add: eval_predicate_return is_local_def eval_value_def eval_return_def eval_abort_def)

lemma sstriple_return_val:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> return_val v \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<rho> v \<star> \<top>)\<close>
proof
  show \<open>\<Gamma> ; \<phi> \<turnstile> return_val v \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta> \<Longrightarrow> \<phi> \<longlongrightarrow> \<rho> v \<star> UNIV\<close>
    by (simp add: striple_return_val sstriple_striple)
  show \<open>\<phi> \<longlongrightarrow> \<rho> v \<star> UNIV \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> return_val v \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (meson aentails_true is_local_weaken striple_return_val sstriple_return_valI sstriple_striple)
qed

text\<open>The \<^verbatim>\<open>return_func\<close> command always succeeds and returns the given value:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_returnI:
  shows \<open>\<Gamma> ; \<top> \<turnstile> return_func (literal v) \<stileturn> \<psi> \<bowtie> (\<lambda>rv. \<langle>rv = v\<rangle>) \<bowtie> \<theta>\<close>
  by (simp add: bind_literal_unit return_func_def sstriple_return_valI)

lemma sstriple_return:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> return_func (literal v) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<rho> v \<star> \<top>)\<close>
  by (simp add: bind_literal_unit return_func_def sstriple_return_val)

text\<open>Abort and panic terminate execution of the program:\<close>
lemma sstriple_abort:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> abort m \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<theta> m \<star> \<top>)\<close>
  by (fastforce simp add: sstriple_striple striple_abort is_local_def eval_value_def
    eval_return_def eval_abort_def shallow_computation_eval_predicate_simps)

text\<open>Panic terminates execution of the program:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_yield:
  shows \<open>(\<Gamma>; \<phi> \<turnstile> yield \<omega> \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (
               is_local (\<lambda>\<sigma> (v, \<sigma>'). YieldContinue (v, \<sigma>') \<in> yh \<Gamma> \<omega> \<sigma>) \<phi> \<and>
               is_local (\<lambda>\<sigma> (a, \<sigma>'). YieldAbort a \<sigma>' \<in> yh \<Gamma> \<omega> \<sigma>) \<phi> \<and>
               (\<forall>\<sigma> \<sigma>' v. YieldContinue (v, \<sigma>') \<in> yh \<Gamma> \<omega> \<sigma> \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<longrightarrow> \<sigma>' \<Turnstile> \<psi> v \<star> UNIV) \<and>
               (\<forall>\<sigma> \<sigma>' a. YieldAbort a \<sigma>' \<in> yh \<Gamma> \<omega> \<sigma> \<longrightarrow> \<sigma> \<Turnstile> \<phi> \<longrightarrow> \<sigma>' \<Turnstile> \<theta> a \<star> UNIV))\<close>
  by (auto simp add: sstriple_def eval_abort_def eval_value_def eval_return_def is_local_False
    shallow_computation_eval_predicate_simps shallow_computation_eval_action_via_predicate striple_yield atriple_rel_def)

text\<open>Conditionals\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sstriple_two_armed_conditionalI:
  assumes \<open>x \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and \<open>\<not> x \<Longrightarrow> \<Gamma> ; \<phi> \<turnstile> f \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> two_armed_conditional (literal x) e f \<stileturn> \<xi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (cases x) (simp_all add: two_armed_conditional_def shallow_computation_simps)

text\<open>Note that, in contrast to the weak striple, this lemma cannot be strengthened into
an equivalence, as \<^verbatim>\<open>call f\<close> can be local without \<^verbatim>\<open>f\<close> being local.\<close>
lemma sstriple_callI:
  assumes \<open>\<Gamma> ; \<phi> \<turnstile> f \<stileturn> \<psi> \<bowtie> \<psi> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> call (FunctionBody f) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
using assms by (auto simp: sstriple_def atriple_rel_def eval_predicate_call
  eval_predicate_call_rel is_local_disj) (subst is_local_def; clarsimp)

lemma sstriple_call_funliteral:
  shows \<open>(\<Gamma> ; \<phi> \<turnstile> funcall1 (lift_fun1 f1) (literal v0) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f1 v0) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> funcall2 (lift_fun2 f2) (literal v0) (literal v1) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f2 v0 v1) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> funcall3 (lift_fun3 f3) (literal v0) (literal v1) (literal v2) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f3 v0 v1 v2) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> funcall4 (lift_fun4 f4) (literal v0) (literal v1) (literal v2) (literal v3) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f4 v0 v1 v2 v3) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> funcall5 (lift_fun5 f5) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f5 v0 v1 v2 v3 v4) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> funcall6 (lift_fun6 f6) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4) (literal v5) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f6 v0 v1 v2 v3 v4 v5) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> funcall7 (lift_fun7 f7) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4) (literal v5) (literal v6) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f7 v0 v1 v2 v3 v4 v5 v6) \<star> \<top>)\<close>
    and \<open>(\<Gamma> ; \<phi> \<turnstile> funcall8 (lift_fun8 f8) (literal v0) (literal v1) (literal v2) (literal v3) (literal v4) (literal v5) (literal v6) (literal v7) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>) \<longleftrightarrow> (\<phi> \<longlongrightarrow> \<psi> (f8 v0 v1 v2 v3 v4 v5 v6 v7) \<star> \<top>)\<close>
  by (fastforce simp: sstriple_striple striple_call_funliteral shallow_computation_simps striple_literal
    eval_value_def eval_return_def eval_abort_def is_local_def shallow_computation_eval_predicate_simps)+

lemma sstriple_getI:
  assumes \<open>ucincl (has f v)\<close>
    shows \<open>\<Gamma>; has f v \<turnstile> get f \<stileturn> (\<lambda>x. \<langle>x = v\<rangle> \<star> has f v) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof -
  from \<open>ucincl (has f v)\<close> have \<open>\<And>x y. x \<sharp> y \<Longrightarrow> x \<Turnstile> has f v \<Longrightarrow> (x + y) \<Turnstile> has f v\<close>
    by (simp add: local.asat_weaken)
  with assms show ?thesis
    apply (intro sstriple_from_stripleI striple_getI)
    apply (auto simp: is_local_def shallow_computation_eval_predicate_simps eval_value_def
        eval_return_def eval_abort_def asat_def has_def)
    done
qed

lemma sstriple_putI:
  assumes \<open>\<And>x. x \<Turnstile> has f v \<Longrightarrow> g x \<Turnstile> has f v'\<close>
      and \<open>\<And>x y. x\<sharp>y \<Longrightarrow> x \<Turnstile> has f v \<Longrightarrow> g (x+y) = g x + y \<and> g x \<sharp> y\<close>
    shows \<open>\<Gamma>; has f v \<turnstile> put g \<stileturn> (\<lambda>_. has f v') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
  by (auto intro!: sstriple_from_stripleI striple_putI simp add: is_local_def shallow_computation_eval_predicate_simps eval_value_def
      eval_return_def eval_abort_def)


subsection\<open>Loops\<close>

lemma sstriple_raw_for_loop:
    fixes I :: \<open>'t list \<Rightarrow> 't list \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>past cur todo. \<Gamma> ; I past (cur # todo) \<turnstile> f cur \<stileturn> (\<lambda>_. I (past @ [cur]) todo) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; I [] xs \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. I xs []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
proof (induction xs arbitrary: I)
  case Nil
  then show ?case
    by (simp add: raw_for_loop_def sstriple_skipI)
next
  case (Cons x xs)
  then have \<open>\<Gamma> ; I [] (x # xs) \<turnstile> f x \<stileturn> (\<lambda>_. I [x] xs) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (metis append_Nil)
  moreover have \<open>\<Gamma> ; I [x] xs \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. I (x # xs) []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using Cons.prems Cons.IH[where I=\<open>\<lambda>past todo. I (x # past) todo\<close>] by (metis append_Cons)
  ultimately have \<open>\<Gamma> ; I [] (x # xs) \<turnstile> (bind (f x) (\<lambda>_. raw_for_loop xs f)) \<stileturn> (\<lambda>_. I (x # xs) []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using sstriple_bindI by fastforce
  then show \<open>\<Gamma> ; I [] (x # xs) \<turnstile> raw_for_loop (x # xs) f \<stileturn> (\<lambda>_. I (x # xs) []) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (clarsimp simp add: raw_for_loop_def sequence_def)
qed

lemma sstriple_raw_for_loop_framed:
    notes aentails_intro [intro]
    fixes INV :: \<open>'t list \<Rightarrow> 't list \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>p t. ucincl (INV p t)\<close>
      and \<open>\<And>past cur todo. \<Gamma> ;  INV past (cur # todo) \<turnstile> f cur \<stileturn> (\<lambda>_. INV (past @ [cur]) todo) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; INV [] xs \<star> ((INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r)) \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(INV xs [] \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r)\<close>
  {
    fix past cur todo
    have \<open>\<Gamma> ; INV past (cur # todo) \<turnstile> f cur \<stileturn> (\<lambda>_. INV (past @ [cur]) todo) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms by auto
    moreover have \<open>\<Gamma> ; INV past (cur # todo) \<star> ?pc \<turnstile> f cur \<stileturn>
        (\<lambda>_. INV (past @ [cur]) todo \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using assms by (intro sstriple_frame_rule; clarsimp)
    moreover have \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
    proof -
      have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    moreover have \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
      by (meson aentails_refl aentails_trans' aentails_inter_weaken aforall_entailsL asepconj_mono awand_counit)
    ultimately have \<open>\<Gamma> ; INV past (cur # todo) \<star>?pc \<turnstile> f cur \<stileturn>
          (\<lambda>_. INV (past @ [cur]) todo \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      using assms
      by (meson aentails_refl sstriple_consequence)
  }
  then have \<open>\<Gamma> ; INV [] xs \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. INV xs [] \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using assms sstriple_raw_for_loop[where I=\<open>\<lambda>p t. INV p t \<star> ?pc\<close>]
      by blast
  moreover have \<open>INV xs [] \<star> ?pc \<longlongrightarrow> \<psi> ()\<close>
    by (metis (no_types, lifting) aentails_refl local.asepconj_comm local.aentails_int local.awand_adjoint)
  ultimately have \<open>\<Gamma> ; INV [] xs \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using local.sstriple_consequence by (fastforce simp add: aentails_refl)
  then show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.sstriple_consequence by fastforce
qed

lemma sstriple_raw_for_loop':
    fixes I :: \<open>'t list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>i. i < length xs \<Longrightarrow> (\<Gamma> ; I xs i \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. I xs (i+1)) \<bowtie> \<rho> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; I xs 0 \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. I xs (length xs)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using assms
proof (induction xs arbitrary: I)
  case Nil
  then show ?case
    by (simp add: raw_for_loop_def sstriple_skipI)
next
  case (Cons x xs)
  then have \<open>\<Gamma> ; I (x # xs) 0 \<turnstile> f x \<stileturn> (\<lambda>_. I (x # xs) 1) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by fastforce
  moreover have \<open>\<And>i. i < length xs \<Longrightarrow> \<Gamma> ; I (x # xs) (Suc i) \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. I (x # xs) (Suc (Suc i))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (metis Cons.prems Suc_eq_plus1 Suc_mono length_Cons nth_Cons_Suc)
  then have \<open>\<Gamma> ; I (x # xs) 1 \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. I (x # xs) (Suc (length xs))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using  Cons.IH[where I=\<open>\<lambda>_ i. I (x # xs) (i+1)\<close>] by force
  ultimately have \<open>\<Gamma> ; I (x # xs) 0 \<turnstile> (bind (f x) (\<lambda>_. raw_for_loop xs f)) \<stileturn> (\<lambda>_. I (x # xs) (Suc (length xs))) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (auto intro: sstriple_bindI[where \<psi>=\<open>\<lambda> _. I (x # xs) 1\<close>])
  then show ?case
    by (auto simp add: raw_for_loop_def sequence_def)
qed

lemma sstriple_raw_for_loop_framed':
    notes aentails_intro [intro]
    fixes INV :: \<open>'t list \<Rightarrow> nat \<Rightarrow> 'a assert\<close>
  assumes \<open>\<And>i. (i < length xs) \<Longrightarrow> (\<Gamma> ; INV xs i \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. INV xs (i+1)) \<bowtie> \<tau> \<bowtie> \<theta>)\<close>
    shows \<open>\<Gamma> ; INV xs 0 \<star> (INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r) \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(INV xs (length xs) \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r)\<close>
  {
    fix i
    assume \<open>i < length xs\<close>
    from this have \<open>\<Gamma> ; INV xs i \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. INV xs (i+1)) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      using assms by auto
    moreover have \<open>\<Gamma> ; INV xs i \<star> ?pc \<turnstile> f (xs ! i) \<stileturn>
        (\<lambda>_. INV xs (i+1) \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using calculation assms by (intro sstriple_frame_rule)
        (auto intro!: ucincl_Int ucincl_awand ucincl_inter)
    moreover have \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
    proof -
      have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
      from this show \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
        by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
    qed
    moreover have \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
      by (meson aentails_refl_eq aentails_trans' aentails_inter_weaken aforall_entailsL asepconj_mono3
          awand_counit)
    ultimately have \<open>\<Gamma> ; INV xs i \<star> ?pc \<turnstile> f (xs ! i) \<stileturn> (\<lambda>_. INV xs (i+1) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      by (meson aentails_refl sstriple_consequence)
  }
  from this have \<open>\<Gamma> ; INV xs 0 \<star> ?pc
                            \<turnstile> raw_for_loop xs f \<stileturn> (\<lambda>_. INV xs (length xs) \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using assms sstriple_raw_for_loop'[where I=\<open>\<lambda>xs' i'. INV xs' i' \<star> ?pc\<close>] by blast
  moreover have \<open>INV xs (length xs) \<star> ?pc \<longlongrightarrow> \<psi> ()\<close>
    by (metis (no_types, lifting) aentails_refl local.asepconj_comm local.aentails_int local.awand_adjoint)
  moreover have \<open>\<Gamma> ; INV xs 0 \<star> ?pc \<turnstile> raw_for_loop xs f \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using calculation local.sstriple_consequence by (fastforce simp add: aentails_refl)
  from this show ?thesis
    using aentails_refl local.asepconj_comm local.awand_mp local.sstriple_consequence by fastforce
qed

subsection\<open>Bounded while-loop triples\<close>

text\<open>Basic bounded while-loop triple. The invariant @{term INV} is indexed by remaining fuel.
Each iteration step must establish the invariant for one less fuel via a triple on the
condition followed by the body (when the condition is true).\<close>
lemma sstriple_bounded_while:
    fixes INV :: \<open>nat \<Rightarrow> 'a assert\<close>
      and INV' :: \<open>nat \<Rightarrow> 'a assert\<close>
  assumes step: \<open>\<And>k. k < n \<Longrightarrow>
    \<Gamma> ; INV (Suc k) \<turnstile> cond \<stileturn>
      (\<lambda>c. if c then INV' k else \<psi> ()) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and body_step: \<open>\<And>k. k < n \<Longrightarrow>
    \<Gamma> ; INV' k \<turnstile> body \<stileturn> (\<lambda>_. INV k) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      and base: \<open>INV 0 \<longlongrightarrow> \<psi> ()\<close>
    shows \<open>\<Gamma> ; INV n \<turnstile> bounded_while n cond body \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using step body_step
proof (induction n)
  case 0
  have \<open>\<Gamma> ; INV 0 \<turnstile> skip \<stileturn> (\<lambda>_. INV 0) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    by (rule sstriple_skipI)
  then have \<open>\<Gamma> ; INV 0 \<turnstile> skip \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using base by (auto intro: sstriple_consequence aentails_refl)
  then show ?case by simp
next
  case (Suc n)
  have cond_triple:
    \<open>\<Gamma> ; INV (Suc n) \<turnstile> cond \<stileturn>
      (\<lambda>c. if c then INV' n else \<psi> ()) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using Suc.prems by simp
  have body_triple: \<open>\<Gamma> ; INV' n \<turnstile> body \<stileturn> (\<lambda>_. INV n) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using Suc.prems by simp
  have ih: \<open>\<Gamma> ; INV n \<turnstile> bounded_while n cond body \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    using Suc.IH Suc.prems by simp
  have true_branch: \<open>\<Gamma> ; INV' n \<turnstile> sequence body (bounded_while n cond body) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    unfolding sequence_def using body_triple ih sstriple_bindI by fastforce
  have false_branch: \<open>\<Gamma> ; \<psi> () \<turnstile> skip \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  proof -
    have \<open>\<Gamma> ; \<psi> () \<turnstile> skip \<stileturn> (\<lambda>_. \<psi> ()) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      by (rule sstriple_skipI)
    then show ?thesis
      by (auto intro: sstriple_consequence aentails_refl)
  qed
  have \<open>\<Gamma> ; INV (Suc n) \<turnstile> bind cond (\<lambda>c. if c then sequence body (bounded_while n cond body) else skip) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  proof (rule sstriple_bindI[OF cond_triple])
    fix c :: bool
    show \<open>\<Gamma> ; (if c then INV' n else \<psi> ()) \<turnstile>
              (if c then sequence body (bounded_while n cond body) else skip) \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<theta>\<close>
      using true_branch false_branch by (cases c) simp_all
  qed
  then show ?case by simp
qed

text\<open>Framed version: carries a frame through all iterations.\<close>
lemma sstriple_bounded_while_framed:
    notes aentails_intro [intro]
    fixes INV :: \<open>nat \<Rightarrow> 'a assert\<close>
      and INV' :: \<open>nat \<Rightarrow> 'a assert\<close>
  assumes ucincl_INV: \<open>\<And>k. ucincl (INV k)\<close>
      and ucincl_INV': \<open>\<And>k. ucincl (INV' k)\<close>
      and cond_step: \<open>\<And>k. k < n \<Longrightarrow>
            \<Gamma> ; INV (Suc k) \<turnstile> cond \<stileturn>
              (\<lambda>c. if c then INV' k else INV 0) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
      and body_step: \<open>\<And>k. k < n \<Longrightarrow>
            \<Gamma> ; INV' k \<turnstile> body \<stileturn> (\<lambda>_. INV k) \<bowtie> \<tau> \<bowtie> \<theta>\<close>
    shows \<open>\<Gamma> ; INV n \<star> ((INV 0 \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r))
              \<turnstile> bounded_while n cond body \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
proof -
  let ?pc = \<open>(INV 0 \<Zsurj> \<psi> ()) \<sqinter> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<sqinter> (\<Sqinter>r. \<theta> r \<Zsurj> \<chi> r)\<close>
  have tau_rho: \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
  proof -
    have \<open>\<And>r. \<tau> r \<star> (\<Sqinter>r. \<tau> r \<Zsurj> \<rho> r) \<longlongrightarrow> \<rho> r\<close>
      by (meson aentails_refl aentails_trans aforall_entailsL asepconj_mono3 awand_counit)
    from this show \<open>\<And>r. \<tau> r \<star> ?pc \<longlongrightarrow> \<rho> r\<close>
      by (meson aentails_fold_def aentails_inter_weaken aentails_inter_weaken2 asepconj_mono awand_adjointI)
  qed
  have theta_chi: \<open>\<And>a. \<theta> a \<star> ?pc \<longlongrightarrow> \<chi> a\<close>
    by (meson aentails_refl aentails_trans' aentails_inter_weaken aforall_entailsL asepconj_mono awand_counit)
  have inv0_psi: \<open>INV 0 \<star> ?pc \<longlongrightarrow> \<psi> ()\<close>
    by (metis (no_types, lifting) aentails_refl local.asepconj_comm local.aentails_int local.awand_adjoint)
  \<comment>\<open>Frame each condition step\<close>
  {
    fix k
    assume kn: \<open>k < n\<close>
    have \<open>\<Gamma> ; INV (Suc k) \<star> ?pc \<turnstile> cond \<stileturn>
        (\<lambda>c. (if c then INV' k else INV 0) \<star> ?pc)
          \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using cond_step[OF kn] ucincl_INV by (intro sstriple_frame_rule; clarsimp)
    moreover have \<open>\<And>c. (if c then INV' k else INV 0) \<star> ?pc \<longlongrightarrow>
        (if c then INV' k \<star> ?pc else \<psi> ())\<close>
      using inv0_psi by (auto simp add: aentails_refl)
    ultimately have \<open>\<Gamma> ; INV (Suc k) \<star> ?pc \<turnstile> cond \<stileturn>
        (\<lambda>c. if c then INV' k \<star> ?pc else \<psi> ())
          \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      using tau_rho theta_chi
      by (meson aentails_refl aentails_trans sstriple_consequence)
  }
  moreover {
    fix k
    assume kn: \<open>k < n\<close>
    have \<open>\<Gamma> ; INV' k \<star> ?pc \<turnstile> body \<stileturn>
        (\<lambda>_. INV k \<star> ?pc) \<bowtie> (\<lambda>r. \<tau> r \<star> ?pc) \<bowtie> (\<lambda>a. \<theta> a \<star> ?pc)\<close>
      using body_step[OF kn] ucincl_INV' by (intro sstriple_frame_rule; clarsimp)
    from this have \<open>\<Gamma> ; INV' k \<star> ?pc \<turnstile> body \<stileturn>
        (\<lambda>_. INV k \<star> ?pc) \<bowtie> \<rho> \<bowtie> \<chi>\<close>
      using tau_rho theta_chi
      by (meson aentails_refl sstriple_consequence)
  }
  ultimately have \<open>\<Gamma> ; INV n \<star> ?pc \<turnstile> bounded_while n cond body \<stileturn> \<psi> \<bowtie> \<rho> \<bowtie> \<chi>\<close>
    using sstriple_bounded_while[where INV=\<open>\<lambda>k. INV k \<star> ?pc\<close> and INV'=\<open>\<lambda>k. INV' k \<star> ?pc\<close>]
      inv0_psi by blast
  then show ?thesis by simp
qed

lemma is_local_eqI:
  assumes \<open>\<And>\<sigma> \<sigma>'. \<sigma> \<Turnstile> \<phi> \<star> \<top> \<Longrightarrow> R \<sigma> \<sigma>' = S \<sigma> \<sigma>'\<close>
  shows \<open>is_local R \<phi> = is_local S \<phi>\<close>
proof -
  from assms have \<open>\<And>\<sigma> \<sigma>'. \<sigma> \<Turnstile> \<phi> \<Longrightarrow> R \<sigma> \<sigma>' = S \<sigma> \<sigma>'\<close>
    by (simp add: asepconj_weakenI)
  from this and assms show ?thesis
    by (clarsimp simp add: is_local_def asepconjI)
qed

lemma sstriple_yield_handler_refine:
  assumes \<open>\<Theta> \<lesssim> \<Gamma>\<close>
      and \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    shows \<open>\<Theta> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
proof -
  from assms have ref: \<open>yield_handler_nondet_basic_refines (yh \<Theta>) (yh \<Gamma>)\<close>
    by simp
  { fix \<sigma> assume \<open>\<sigma> \<Turnstile> \<phi> \<star> \<top>\<close>
    from this and assms have \<open>\<And>a \<sigma>'. \<sigma> \<leadsto>\<^sub>a\<langle>yh \<Gamma>, e\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close>
      by (metis asat_connectives_characterisation(2) bot_apply asepconj_ident2
        atripleE stripleE_abort ucincl_UNIV ucincl_empty striple_from_sstripleI)
    from this have no_abort: \<open>(yh \<Gamma>, e) \<diamondop>\<^sub>a \<sigma> = {}\<close>
      by (simp add: abort_evaluations_def)
    from \<open>\<And>a \<sigma>'. \<sigma> \<leadsto>\<^sub>a\<langle>yh \<Gamma>, e\<rangle> (a, \<sigma>') \<longleftrightarrow> False\<close> eval_predicate_refine[OF ref no_abort] have
          eq_abort: \<open>\<And>a \<sigma>'. \<sigma> \<leadsto>\<^sub>a\<langle>yh \<Theta>, e\<rangle> (a, \<sigma>') \<longleftrightarrow> \<sigma> \<leadsto>\<^sub>a\<langle>yh \<Gamma>, e\<rangle> (a, \<sigma>')\<close> and
          eq_val: \<open>\<And>v \<sigma>'. \<sigma> \<leadsto>\<^sub>v\<langle>yh \<Theta>, e\<rangle> (v, \<sigma>') \<longleftrightarrow> \<sigma> \<leadsto>\<^sub>v\<langle>yh \<Gamma>, e\<rangle> (v, \<sigma>')\<close> and
          eq_res: \<open>\<And>r \<sigma>'. \<sigma> \<leadsto>\<^sub>r\<langle>yh \<Theta>, e\<rangle> (r, \<sigma>') \<longleftrightarrow> \<sigma> \<leadsto>\<^sub>r\<langle>yh \<Gamma>, e\<rangle> (r, \<sigma>')\<close> by simp+
  }
  note X = this
  from X have
    \<open>is_local (eval_return (yh \<Theta>) e) \<phi> \<longleftrightarrow> is_local (eval_return (yh \<Gamma>) e) \<phi>\<close> and
    \<open>is_local (eval_value (yh \<Theta>) e) \<phi> \<longleftrightarrow> is_local (eval_value (yh \<Gamma>) e) \<phi>\<close> and
    \<open>is_local (eval_abort (yh \<Theta>) e) \<phi> \<longleftrightarrow> is_local (eval_abort (yh \<Gamma>) e) \<phi>\<close>
    by (intro is_local_eqI; clarsimp simp add: eval_value_def eval_abort_def eval_return_def)+
  moreover from assms have \<open>\<Theta> ; \<phi> \<turnstile> e \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    using assms by (simp add: striple_yield_handler_refine striple_from_sstripleI)
  ultimately show ?thesis
    using assms by (clarsimp simp add: sstriple_striple)
qed

corollary sstriple_yield_handler_no_yield_implies_all:
  assumes \<open>striple_context_no_yield ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
    shows \<open>\<Gamma> ; \<phi> \<turnstile> e \<stileturn> \<psi> \<bowtie> \<xi> \<bowtie> \<bottom>\<close>
  using assms striple_context_refines_top sstriple_yield_handler_refine by blast

(*<*)
end

end
(*>*)
