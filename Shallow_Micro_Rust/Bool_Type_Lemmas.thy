(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Bool_Type_Lemmas
  imports Core_Expression_Lemmas Shallow_Micro_Rust_Base.Bool_Type
begin
declare [[urust_conformance_check = true]]
(*>*)

lemma evaluate_trueE [micro_rust_elims]:
  assumes \<open>evaluate Bool_Type.true \<sigma> = k\<close>
      and \<open>k = Success True \<sigma> \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (unfold true_def; elim evaluate_literalE; force)

lemma evaluate_true [micro_rust_simps]:
  shows \<open>evaluate Bool_Type.true \<sigma> = Success True \<sigma>\<close>
by (auto simp add: true_def micro_rust_simps)

lemma evaluate_false [micro_rust_simps]:
  shows \<open>evaluate Bool_Type.false \<sigma> = Success False \<sigma>\<close>
by (auto simp add: false_def micro_rust_simps)

lemma evaluate_falseE [micro_rust_elims]:
  assumes \<open>evaluate Bool_Type.false \<sigma> = k\<close>
      and \<open>k = Success False \<sigma> \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (unfold false_def; elim evaluate_literalE; force)

lemma evaluate_two_armed_conditionalI [micro_rust_intros]:
    fixes test :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
  assumes \<open>\<And>\<sigma>'. evaluate test \<sigma> = Success True \<sigma>' \<Longrightarrow> k = evaluate t \<sigma>'\<close>
      and \<open>\<And>\<sigma>'. evaluate test \<sigma> = Success False \<sigma>' \<Longrightarrow> k = evaluate f \<sigma>'\<close>
      and \<open>\<And>r \<sigma>'. evaluate test \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>'\<close>
      and \<open>\<And>a \<sigma>'. evaluate test \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>'\<close>
      and \<open>\<And>\<pi> \<sigma>' test'. evaluate test \<sigma> = Yield \<pi> \<sigma>' test' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. if (test' \<omega>) \<lbrace> t \<rbrace> else \<lbrace> f \<rbrace>)\<close>
    shows \<open>evaluate (if test \<lbrace> t \<rbrace> else \<lbrace> f \<rbrace>) \<sigma> = k\<close>
using assms by (simp add: two_armed_conditional_def; cases \<open>evaluate test \<sigma>\<close>; intro evaluate_bindI; auto)

lemma evaluate_two_armed_conditionalE [micro_rust_elims]:
  assumes \<open>evaluate (two_armed_conditional test t f) \<sigma> = k\<close>
    and \<open>\<And>q \<sigma>' \<sigma>''. evaluate test \<sigma> = Success True \<sigma>' \<Longrightarrow> evaluate t \<sigma>' = k \<Longrightarrow> R\<close>
    and \<open>\<And>q \<sigma>' \<sigma>''. evaluate test \<sigma> = Success False \<sigma>' \<Longrightarrow> evaluate f \<sigma>' = k \<Longrightarrow> R\<close>
    and \<open>\<And>r \<sigma>'. evaluate test \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>a \<sigma>'. evaluate test \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>' \<Longrightarrow>  R\<close>
    and \<open>\<And>\<pi> \<sigma>' test'. evaluate test \<sigma> = Yield \<pi> \<sigma>' test' \<Longrightarrow>
      k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. if (test' \<omega>) \<lbrace> t \<rbrace> else \<lbrace> f \<rbrace>) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (unfold two_armed_conditional_def) (elim evaluate_bindE; clarsimp split: if_splits)

text\<open>Note that conditionals satisfy some "obvious" properties.  For example, testing against the
\<^emph>\<open>truth\<close> and \<^emph>\<open>falsity\<close> constants collapses the conditional, as one would expect:\<close>
urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_1
  (e, f)
  \<open> if True { \<epsilon>\<open>e\<close> } else { \<epsilon>\<open>f\<close> } \<close>

urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_2
  (e, f)
  \<open> if False { \<epsilon>\<open>e\<close> } else { \<epsilon>\<open>f\<close> } \<close>

lemma two_armed_conditional_true_false_collapse [micro_rust_simps]:
  shows \<open>Bool_Type_Lemmas_urust_site_1 e f = e\<close>
    and \<open>Bool_Type_Lemmas_urust_site_2 e f = f\<close>
  by (auto simp add: two_armed_conditional_def true_def false_def micro_rust_simps)

text\<open>Moreover, we can also perform some common-subexpression elimination, by "hoisting" common
expressions that appear in both branches of the conditional out, as follows:\<close>
urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_3
  (c, e, g, f)
  \<open>
    if \<epsilon>\<open>c\<close> {
      \<epsilon>\<open>e\<close>;
      \<epsilon>\<open>g\<close>
    } else {
      \<epsilon>\<open>f\<close>;
      \<epsilon>\<open>g\<close>
    }
  \<close>

urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_4
  (c, e, f, g)
  \<open>
    if \<epsilon>\<open>c\<close> {
      \<epsilon>\<open>e\<close>
    } else {
      \<epsilon>\<open>f\<close>
    };
    \<epsilon>\<open>g\<close>
  \<close>

lemma two_armed_conditional_sequence_hoist [micro_rust_simps]:
  shows \<open>Bool_Type_Lemmas_urust_site_3 c e g f =
    Bool_Type_Lemmas_urust_site_4 c e f g\<close> (is \<open>?LHS = ?RHS\<close>)
proof -
  have X: \<open>\<And>v e f g. (if v then (e; g) else (f; g)) = (if v then (e; g) else (f; g))\<close>
    by (case_tac v; auto)
  have \<open>?RHS = (let v = c; ((if v then e else f); g))\<close>
    by (simp add: two_armed_conditional_def Core_Expression_Lemmas.bind_assoc sequence_def)
  also have \<open>... = (let v = c; (if v then (e; g) else (f; g)))\<close>
    by (metis (mono_tags, lifting))
  also have \<open>... = ?LHS\<close>
    by (simp add: two_armed_conditional_def)
  finally show ?thesis by auto
qed

text\<open>Interestingly, this floating out of common subexpressions does not work in the other direction,
nor is it true that we can collapse a conditional where both branches contain the same expression,
\<^term>\<open>e\<close>, to that expression.  This is because the test expression of a conditional may panic, or
return early from a function!\<close>

lemma evaluate_assert_valE [micro_rust_elims]:
  assumes \<open>evaluate (assert_val v) \<sigma> = k\<close>
    and \<open>v = True \<Longrightarrow> k = Success () \<sigma> \<Longrightarrow> R\<close>
    and \<open>v = False \<Longrightarrow> k = Abort AssertionFailed \<sigma> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (cases v; simp add: assert_val_def micro_rust_simps)

lemma evaluate_assertE [micro_rust_elims]:
  assumes \<open>evaluate (assert e) \<sigma> = k\<close>
    and \<open>\<And>\<sigma>'. evaluate e \<sigma> = Success True \<sigma>' \<Longrightarrow> k = Success () \<sigma>' \<Longrightarrow>  R\<close>
    and \<open>\<And>\<sigma>'. evaluate e \<sigma> = Success False \<sigma>' \<Longrightarrow> k = Abort AssertionFailed \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>' \<Longrightarrow> R\<close>
    and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. assert (e' \<omega>)) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (simp only: assert_def; elim evaluate_bindE evaluate_assert_valE; auto)

lemma evaluate_assertI [micro_rust_intros]:
  assumes \<open>\<And>\<sigma>'. evaluate e \<sigma> = Success True \<sigma>' \<Longrightarrow> k = Success () \<sigma>'\<close>
      and \<open>\<And>\<sigma>'. evaluate e \<sigma> = Success False \<sigma>' \<Longrightarrow> k = Abort AssertionFailed \<sigma>'\<close>
      and \<open>\<And>a \<sigma>'. evaluate e \<sigma> = Abort a \<sigma>' \<Longrightarrow> k = Abort a \<sigma>'\<close>
      and \<open>\<And>\<pi> \<sigma>' e'. evaluate e \<sigma> = Yield \<pi> \<sigma>' e' \<Longrightarrow> k = Yield \<pi> \<sigma>' (\<lambda>\<omega>. assert (e' \<omega>))\<close>
      and \<open>\<And>r \<sigma>'. evaluate e \<sigma> = Return r \<sigma>' \<Longrightarrow> k = Return r \<sigma>'\<close>
  shows \<open>evaluate (assert e) \<sigma> = k\<close>
  using assms
  by (auto intro: evaluate_bindI simp add: assert_def assert_val_def micro_rust_simps)

text\<open>In degenerate cases, this assertion expression behaves like a form of \<^term>\<open>panic\<close>:\<close>
lemma assert_false_sequence [micro_rust_simps]:
  shows \<open>(assert (\<up>False); e) = assert (\<up>False)\<close>
  by (simp add: micro_rust_simps assert_def assert_val_def)

text\<open>...and \<^term>\<open>skip\<close>:\<close>
urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_5
  (e)
  \<open> assert!(True); \<epsilon>\<open>e\<close> \<close>

lemma assert_true_sequence [micro_rust_simps]:
  shows \<open>Bool_Type_Lemmas_urust_site_5 e = e\<close>
  by (simp add: micro_rust_simps assert_def assert_val_def)

urust_expr [abbrev = true] evaluate_negation_literal_1 ::
  \<open>bool \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
  (c)
  \<open> !c \<close>

urust_expr [abbrev = true] evaluate_negation_literal_2
  (c)
  \<open> \<llangle>\<not>c\<rrangle> \<close>

lemma evaluate_negation_literal [micro_rust_simps]:
  shows \<open>evaluate_negation_literal_1 c = evaluate_negation_literal_2 c\<close>
  by (clarsimp simp add: micro_rust_simps negation_def)

urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_8
  (c, d)
  \<open> c && \<epsilon>\<open>d\<close> \<close>

urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_9
  (c, d)
  \<open> if c { \<epsilon>\<open>d\<close> } else { False } \<close>

lemma evaluate_conjunction_literal [micro_rust_simps]:
  shows \<open>Bool_Type_Lemmas_urust_site_8 c d = Bool_Type_Lemmas_urust_site_9 c d\<close>
  by (clarsimp simp add: micro_rust_simps urust_conj_def two_armed_conditional_def false_def)

urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_10
  (c, e)
  \<open> c || \<epsilon>\<open>e\<close> \<close>

urust_expr [abbrev = true] Bool_Type_Lemmas_urust_site_11
  (c, e)
  \<open> if c { True } else { \<epsilon>\<open>e\<close> } \<close>

lemma evaluate_disjunction_literal [micro_rust_simps]:
  shows \<open>Bool_Type_Lemmas_urust_site_10 c e = Bool_Type_Lemmas_urust_site_11 c e\<close>
  by (clarsimp simp add: micro_rust_simps urust_disj_def two_armed_conditional_def true_def)

urust_expr [abbrev = true] evaluate_eq_literal_1
  (c, d)
  \<open> c == d \<close>

urust_expr [abbrev = true] evaluate_eq_literal_2
  (c, d)
  \<open> \<llangle>c = d\<rrangle> \<close>

lemma evaluate_eq_literal [micro_rust_simps]:
  shows \<open>evaluate_eq_literal_1 c d = evaluate_eq_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps urust_eq_def)

urust_expr [abbrev = true] evaluate_neq_literal_1
  (c, d)
  \<open> c != d \<close>

urust_expr [abbrev = true] evaluate_neq_literal_2
  (c, d)
  \<open> \<llangle>c \<noteq> d\<rrangle> \<close>

lemma evaluate_neq_literal [micro_rust_simps]:
  shows \<open>evaluate_neq_literal_1 c d = evaluate_neq_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps urust_neq_def)

(* We don't add these to micro_rust_simps as it can leads to overly aggressive case-splitting
   by HOL's if_split rule. Still, it can be useful in specific proofs. *)

urust_expr [abbrev = true] evaluate_pure_if_1
  (x, y, z)
  \<open> if x { y } else { z } \<close>

urust_expr [abbrev = true] evaluate_pure_if_2
  (x, y, z)
  \<open> \<llangle>if x then y else z\<rrangle> \<close>

lemma evaluate_pure_if:
  shows \<open>evaluate_pure_if_1 x y z = evaluate_pure_if_2 x y z\<close>
  by (clarsimp simp add: micro_rust_simps)

urust_expr [abbrev = true] evaluate_pure_if_then_True_1
  (x, z)
  \<open> \<llangle>if x then True else z\<rrangle> \<close>

urust_expr [abbrev = true] evaluate_pure_if_then_True_2
  (x, z)
  \<open> \<llangle>x \<or> z\<rrangle> \<close>

lemma evaluate_pure_if_then_True:
  shows \<open>evaluate_pure_if_then_True_1 x z = evaluate_pure_if_then_True_2 x z\<close>
  by simp

urust_expr [abbrev = true] evaluate_pure_if_else_True_1
  (x, y)
  \<open> \<llangle>if x then y else True\<rrangle> \<close>

urust_expr [abbrev = true] evaluate_pure_if_else_True_2
  (x, y)
  \<open> \<llangle>\<not>x \<or> y\<rrangle> \<close>

lemma evaluate_pure_if_else_True:
  shows \<open>evaluate_pure_if_else_True_1 x y = evaluate_pure_if_else_True_2 x y\<close>
  by simp


(*<*)
end
(*>*)
