(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Generic state-logic foundation. *)
(*<*)
theory Separation_Algebra
  imports Apartness
begin
(*>*)

named_theorems ucincl_intros
named_theorems ucincl_elims

named_theorems sepalg_simps

section\<open>Separation algebras\<close>

text\<open>To avoid talking about our underlying machine state for as long as possible, when defining
assertions, we will phrase them in terms of an algebra that is known to be sufficiently expressive
to develop the connectives of Separation Logic.  As a result, these definitions will work for \<^emph>\<open>any\<close>
machine state, or similarly any other structure, that can be shown to satisfy the properties of this
algebra, and are therefore "maximally reusable".  We want to maintain this reusability when
we move away from pure logic and into separation logic.  To do this, we will use a \<^emph>\<open>typeclass\<close>,
which fixes three abstract operations:
\begin{enumerate*}
\item
The \<^emph>\<open>empty machine\<close>, written using \<^verbatim>\<open>0\<close>,
\item
The ability to \<^emph>\<open>join together\<close> two \<^emph>\<open>disjoint\<close> pieces of a machine, written using \<^verbatim>\<open>+\<close>,
\item
The ability to tell when two subpieces of a machine are in fact \<^emph>\<open>disjoint\<close>.
\end{enumerate*}
This is captured below:\<close>
class sepalg = plus + zero + apart +
  assumes sepalg_ident2 [simp, sepalg_simps]: \<open>x + 0 = x\<close>
      and sepalg_comm [simp, sepalg_simps]: \<open>x \<sharp> y \<Longrightarrow> x + y = y + x\<close>
      and sepalg_assoc [simp, sepalg_simps]: \<open>\<lbrakk> x \<sharp> y; y \<sharp> z; x \<sharp> z \<rbrakk> \<Longrightarrow> x + (y + z) = (x + y) + z\<close>
      and sepalg_apart_plus2 [intro]: \<open>\<lbrakk> x \<sharp> (y + z); y \<sharp> z\<rbrakk> \<Longrightarrow> x \<sharp> y\<close>
      and sepalg_apart_assoc2 [intro]: \<open>\<lbrakk> x \<sharp> (y + z); y \<sharp> z\<rbrakk> \<Longrightarrow> (x + y) \<sharp> z\<close>
begin

lemma sepalg_ident [simp, sepalg_simps]:
  shows \<open>0 + x = x\<close>
using sepalg_comm sepalg_ident2 by auto

lemma sepalg_apart_plus [intro]:
  assumes \<open>(x + y) \<sharp> z\<close>
      and \<open>x \<sharp> y\<close>
    shows \<open>y \<sharp> z\<close>
proof -
  from \<open>x \<sharp> y\<close> have \<open>x + y = y + x\<close> and \<open>y \<sharp> x\<close>
    by auto
  from \<open>x + y = y + x\<close> and \<open>(x + y) \<sharp> z\<close> have \<open>z \<sharp> (y + x)\<close>
    by auto
  from \<open>z \<sharp> (y + x)\<close> and \<open>y \<sharp> x\<close> have \<open>z \<sharp> y\<close>
    by fast
  from this show ?thesis
    by auto
qed

lemma sepalg_apart_assoc [intro]:
  assumes \<open>(x + y) \<sharp> z\<close>
      and \<open>x \<sharp> y\<close>
    shows \<open>x \<sharp> (y + z)\<close>
proof -
  from assms have \<open>y \<sharp> z\<close>
    using sepalg_apart_plus by fast
  moreover from assms have \<open>x + y = y + x\<close> and \<open>y \<sharp> x\<close>
    by auto
  moreover from assms have \<open>z \<sharp> (y + x)\<close>
    by auto
  moreover from calculation have \<open>(z + y) \<sharp> x\<close>
    by blast
  ultimately show ?thesis
    using assms by auto
qed

lemma sepalg_apart_plus_distrib[simp, sepalg_simps]:
  assumes \<open>x \<sharp> y\<close>
      and \<open>x \<sharp> z\<close>
      and \<open>y \<sharp> z\<close>
    shows \<open>x \<sharp> (y + z) = (x + y) \<sharp> z\<close>
using assms by blast

end

subsection\<open>A strong separation algebra\<close>

text\<open>We further restrict our class of separation algebras by considering those with the following
additional property:\<close>

class strong_sepalg = sepalg +
  assumes sepalg_pairwise: \<open>x \<sharp> y \<Longrightarrow> x + y \<sharp> z \<longleftrightarrow> y \<sharp> z \<and> x \<sharp> z\<close>
begin

text\<open>Note that this immediately implies that pairwise disjoint elements remain disjoint under
combination with the separation algebra's addition operator:\<close>

lemma sepalg_pairwise_apart [intro]:
  assumes \<open>x \<sharp> y\<close>
      and \<open>y \<sharp> z\<close>
      and \<open>x \<sharp> z\<close>
    shows \<open>x + y \<sharp> z\<close>
using assms by (metis local.sepalg_pairwise)

text\<open>The following corollary of \<^verbatim>\<open>sepalg_pairwise\<close> also holds:\<close>

lemma sepalg_pairwise2[simp, sepalg_simps]:
  assumes \<open>y \<sharp> z\<close>
    shows \<open>x \<sharp> y + z \<longleftrightarrow> x \<sharp> y \<and> x \<sharp> z\<close>
using assms local.sepalg_pairwise by auto

end

subsection\<open>Cancellative separation algebras\<close>

class cancellative_sepalg = strong_sepalg +
  assumes sepalg_cancel: \<open>\<And>x y z. x + z = y + z \<Longrightarrow> x \<sharp> z \<Longrightarrow> y \<sharp> z \<Longrightarrow> x = y\<close>
begin

lemma sepalg_cancel_iff:
  assumes \<open>x \<sharp> z\<close>
      and \<open>y \<sharp> z\<close>
    shows \<open>(x + z = y + z) \<longleftrightarrow> (x = y)\<close>
using assms sepalg_cancel by blast

end

subsection\<open>The derived partial order\<close>

context sepalg begin

text \<open>For a separation algebra, passing to constituents of disjoint/apart decompositions of an
element defines a derived partial order on the separation algebra.\<close>
definition derived_order :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<close> 50) where
  \<open>derived_order x y \<longleftrightarrow> (\<exists>z. x \<sharp> z \<and> x + z = y)\<close>

lemma derived_orderI [intro]:
  assumes \<open>x \<sharp> z \<and> x + z = y\<close>
    shows \<open>x \<preceq> y\<close>
using assms by (auto simp add: derived_order_def)

lemma derived_orderE [elim]:
  assumes \<open>x \<preceq> y\<close>
      and \<open>\<And>z. x \<sharp> z \<Longrightarrow> x + z = y \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms derived_order_def by blast

lemma derived_order_refl [simp]:
  shows \<open>x \<preceq> x\<close>
using zero_disjoint sepalg_ident2 by blast

lemma derived_order_zero [simp]:
  shows \<open>0 \<preceq> x\<close>
by (simp add:derived_order_def)

lemma derived_order_trans [trans]:
  assumes \<open>x \<preceq> y\<close>
      and \<open>y \<preceq> z\<close>
    shows \<open>x \<preceq> z\<close>
proof -
  from assms obtain z\<^sub>1 and z\<^sub>2 where \<open>x + z\<^sub>1 = y\<close> and \<open>y + z\<^sub>2 = z\<close> and \<open>x \<sharp> z\<^sub>1\<close> and \<open>y \<sharp> z\<^sub>2\<close>
    by blast
  from this show \<open>x \<preceq> z\<close>
    by (metis derived_order_def local.disjoint_sym local.sepalg_apart_assoc local.sepalg_apart_plus
      local.sepalg_assoc)
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma derived_order_antisym:
  assumes \<open>x \<preceq> y\<close>
      and \<open>y \<preceq> x\<close>
    shows \<open>x = y\<close>
proof -
  from assms obtain z\<^sub>1 where \<open>x + z\<^sub>1 = y\<close> and \<open>z\<^sub>1 \<sharp> x\<close>
    by (auto elim!: derived_orderE)
  moreover from assms obtain z\<^sub>2 where \<open>y + z\<^sub>2 = x\<close> and \<open>z\<^sub>2 \<sharp> y\<close>
    by (auto elim!: derived_orderE)
  moreover from calculation have \<open>(y + z\<^sub>2 + z\<^sub>1) = y\<close>
    by auto
  ultimately show \<open>x = y\<close>
    by (metis local.disjoint_sym local.reflE local.sepalg_apart_plus local.sepalg_comm
      local.sepalg_ident2)
qed

lemma derived_order_distinct_downward_closed:
  assumes \<open>x \<sharp> z\<close>
      and \<open>y \<preceq> z\<close>
    shows \<open>x \<sharp> y\<close>
proof -
  from \<open>y \<preceq> z\<close> obtain w where \<open>y \<sharp> w\<close> and \<open>y + w = z\<close>
    by blast
  from this and \<open>x \<sharp> z\<close> have \<open>x \<sharp> y + w\<close>
    by simp
  from this and \<open>y + w = z\<close> and \<open>y \<sharp> w\<close> show ?thesis
    by blast
qed

lemma derived_order_plus_monotone:
  assumes \<open>a \<preceq> b\<close>
      and \<open>b \<sharp> y\<close>
    shows \<open>a + y \<preceq> b + y\<close>
proof -
  from assms obtain c where \<open>a \<sharp> c\<close> and \<open>a + c = b\<close>
    by blast
  moreover from assms calculation have \<open>a \<sharp> y\<close> and \<open>c \<sharp> y\<close>
    by (metis derived_order_distinct_downward_closed local.disjoint_sym local.sepalg_apart_plus)+
  moreover from assms calculation have \<open>(a + y) + c = b + y\<close>
    by auto
  moreover from assms calculation have \<open>(a + y) \<sharp> c\<close>
    by auto
  ultimately show ?thesis using derived_orderI
    by blast
qed

lemma derived_order_plus_monotone2:
  assumes \<open>a \<preceq> b\<close>
      and \<open>b \<sharp> y\<close>
    shows \<open>y + a \<preceq> y + b\<close>
proof -
  from assms have \<open>a \<sharp> y\<close>
    by fastforce
  from this and assms have \<open>a + y \<preceq> b + y\<close>
    using derived_order_plus_monotone by blast
  from \<open>a + y \<preceq> b + y\<close> and \<open>a \<sharp> y\<close> and \<open>b \<sharp> y\<close> show ?thesis
    by auto
qed

(*<*)
end
(*>*)

subsection\<open>Separation algebras satisfying the cross-split axiom\<close>

class cross_split_sepalg = cancellative_sepalg +
  assumes sepalg_crosssplit: \<open>\<And>a b c d. a \<sharp> b \<Longrightarrow> c \<sharp> d \<Longrightarrow> a + b = c + d \<Longrightarrow>
    (\<exists>t00 t01 t10 t11. t00 \<sharp> t01 \<and> t00 \<sharp> t10 \<and> t00 \<sharp> t11 \<and> t01 \<sharp> t10 \<and> t01 \<sharp> t11 \<and> t10 \<sharp> t11 \<and>
        a = t00 + t01 \<and> b = t10 + t11 \<and> c = t00 + t10 \<and> d = t01 + t11)\<close>
begin

lemma sepalg_derived_order_plus:
    notes sepalg_simps[simp del]
  assumes \<open>\<sigma>0 \<preceq> \<sigma>\<close>
      and \<open>\<sigma>1 \<preceq> \<sigma>\<close>
      and \<open>\<sigma>0 \<sharp> \<sigma>1\<close>
    shows \<open>\<sigma>0 + \<sigma>1 \<preceq> \<sigma>\<close>
proof -
  from assms obtain \<sigma>0' and \<sigma>1' where \<open>\<sigma>0 \<sharp> \<sigma>0'\<close> and \<open>\<sigma>1 \<sharp> \<sigma>1'\<close> and \<open>\<sigma> = \<sigma>0 + \<sigma>0'\<close> and \<open>\<sigma> = \<sigma>1 + \<sigma>1'\<close>
    using local.derived_order_def by auto
  moreover from this assms and sepalg_crosssplit[where a=\<sigma>0 and b=\<sigma>0' and c=\<sigma>1 and d=\<sigma>1'] obtain t00 t01 t10 t11 where
    \<open>t00 \<sharp> t01 \<and> t00 \<sharp> t10 \<and> t00 \<sharp> t11 \<and> t01 \<sharp> t10 \<and> t01 \<sharp> t11 \<and> t10 \<sharp> t11 \<and>
        \<sigma>0 = t00 + t01 \<and> \<sigma>0' = t10 + t11 \<and> \<sigma>1 = t00 + t10 \<and> \<sigma>1' = t01 + t11\<close>
    by presburger
  moreover from this have \<open>t00 \<sharp> t00\<close>
    using assms(3) local.disjoint_sym by blast
  moreover from this have \<open>t00 = 0\<close>
    by blast
  moreover from calculation have \<open>\<sigma>0 = t01\<close> and \<open>\<sigma>1 = t10\<close>
    by (auto simp add: sepalg_ident)
  moreover from calculation have \<open>\<sigma> = t10 + t01 + t11\<close>
    by (simp add: local.sepalg_assoc local.sepalg_ident)
  ultimately show ?thesis
    using local.sepalg_comm by auto
qed

end

(*<*)
context sepalg
begin
(*>*)

subsection\<open>Upwards-closure\<close>

text\<open>A predicate is \<^emph>\<open>upwards-closed\<close> if its truth at a point $x$ implies truth at every other point
above $x$:\<close>
definition ucpred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>ucpred P \<equiv> \<forall>x y. P x \<longrightarrow> x \<preceq> y \<longrightarrow> P y\<close>

text\<open>We have introduction and elimination rules for this concept:\<close>
lemma ucpredI:
  assumes \<open>\<And>x y. P x \<Longrightarrow> x \<preceq> y \<Longrightarrow> P y\<close>
    shows \<open>ucpred P\<close>
using assms by (auto simp add: ucpred_def)

lemma ucpredE:
  assumes \<open>ucpred P\<close>
      and \<open>(\<And>x y. P x \<Longrightarrow> x \<preceq> y \<Longrightarrow> P y) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (clarsimp simp add: ucpred_def)

text\<open>Similarly, a partial function is upwards closed if it being defined at a point $x$ implies that
it is also defined at every other point above $x$:\<close>
definition ucpfunc :: \<open>('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> where
  \<open>ucpfunc f \<equiv> \<forall>v. ucpred (\<lambda>s. f s = Some v)\<close>

text\<open>We also derive introduction and elimination rules for this concept, too:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma ucpfuncI:
  assumes \<open>\<And>v. ucpred (\<lambda>x. f x = Some v)\<close>
    shows \<open>ucpfunc f\<close>
using assms by(auto simp add: ucpfunc_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma ucpfuncE:
  assumes \<open>ucpfunc f\<close>
      and \<open>(\<And>v. ucpred (\<lambda>x. f x = Some v)) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by(auto simp add: ucpfunc_def)

text\<open>A set is also upwards closed if the set membership predicate on that set is upwards closed:\<close>
definition ucincl :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>ucincl S \<equiv> ucpred (\<lambda>x. x \<in> S)\<close>

lemma ucinclI:
  assumes \<open>ucpred (\<lambda>x. x \<in> S)\<close>
    shows \<open>ucincl S\<close>
using assms by (auto simp add: ucincl_def)

lemma ucinclE:
  assumes \<open>ucincl S\<close>
      and \<open>ucpred (\<lambda>x. x \<in> S) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: ucincl_def)

lemma ucpred_upward_closure:
  assumes \<open>ucpred P\<close>
    shows \<open>ucincl (Collect P)\<close>
using assms by (clarsimp elim: ucpredE intro!: ucinclI)

end

subsection\<open>Some concrete separation algebras\<close>

instantiation unit :: cancellative_sepalg
begin

definition zero_unit :: unit where
  \<open>zero_unit \<equiv> ()\<close>

definition disjoint_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> bool\<close> where
  \<open>disjoint_unit _ _ \<equiv> True\<close>

definition plus_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> unit\<close> where
  \<open>plus_unit _ _ \<equiv> ()\<close>

instance
  by (standard; unfold disjoint_unit_def plus_unit_def zero_unit_def; simp)

end

instantiation option :: (type)strong_sepalg
begin

definition plus_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> 'a option\<close> where
  \<open>plus_option x y \<equiv>
    case x of
      None \<Rightarrow> y
    | Some _ \<Rightarrow> x\<close>

instance
  by (standard; unfold disjoint_option_def plus_option_def zero_option_def; clarsimp split: option.splits)

end

instantiation option :: (type)cancellative_sepalg
begin

instance
proof
     fix x y z :: \<open>'a option\<close>
  assume \<open>x + z = y + z\<close>
     and \<open>x \<sharp> z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x = y\<close>
    by (cases x; cases y; cases z) (auto simp add: disjoint_option_def plus_option_def)
qed

end

instantiation set :: (type)strong_sepalg
begin

definition plus_set :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>plus_set x y \<equiv> x \<union> y\<close>

instance
  by (standard; unfold zero_set_def plus_set_def disjoint_set_def; auto)

end

instantiation set :: (type)cancellative_sepalg
begin

instance
proof
     fix x y z :: \<open>'a set\<close>
  assume \<open>x + z = y + z\<close>
     and \<open>x \<sharp> z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x = y\<close>
    by (clarsimp simp add: disjoint_set_def plus_set_def) blast
qed

end

instantiation "prod" :: (sepalg, sepalg) sepalg
begin

definition plus_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>plus_prod x y \<equiv> (fst x + fst y, snd x + snd y)\<close>

instance
proof
   fix x :: \<open>'a \<times> 'b\<close>
  show \<open>x + 0 = x\<close>
    by (cases x) (auto simp add: plus_prod_def zero_prod_def)
next
     fix x y :: \<open>'a \<times> 'b\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>x + y = y + x\<close>
    by (auto simp add: plus_prod_def disjoint_prod_def)
next
     fix x y z :: \<open>'a \<times> 'b\<close>
  assume \<open>x \<sharp> y\<close>
     and \<open>y \<sharp> z\<close>
     and \<open>x \<sharp> z\<close>
  from this show \<open>x + (y + z) = x + y + z\<close>
    by (cases x; cases y; cases z, unfold disjoint_prod_def plus_prod_def)
      (metis sepalg_assoc split_pairs)
next
    fix x y z :: \<open>'a \<times> 'b\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x \<sharp> y\<close>
    by (auto simp add: disjoint_prod_def plus_prod_def)
next
    fix x y z :: \<open>'a \<times> 'b\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x + y \<sharp> z\<close>
    by (clarsimp simp add: disjoint_prod_def plus_prod_def) (metis disjoint_sym sepalg_apart_assoc2)
qed

end

instantiation "prod" :: (strong_sepalg, strong_sepalg) strong_sepalg
begin

instance
  by standard (auto simp add: plus_prod_def disjoint_prod_def)

end

instantiation "prod" :: (cancellative_sepalg, cancellative_sepalg) cancellative_sepalg
begin

instance
  by standard (auto simp add: plus_prod_def disjoint_prod_def sepalg_cancel_iff)

end

instantiation "fun" :: (type, sepalg)sepalg
begin

definition plus_fun :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where
  \<open>plus_fun f g \<equiv> \<lambda>x. f x + g x\<close>

instance
proof
   fix x :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>x + 0 = x\<close>
    by (clarsimp simp add: zero_fun_def plus_fun_def)
next
     fix x y :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>x + y = y + x\<close>
    by (clarsimp simp add: zero_fun_def plus_fun_def disjoint_fun_def)
next
     fix x y z :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>x \<sharp> y\<close>
     and \<open>y \<sharp> z\<close>
     and \<open>x \<sharp> z\<close>
  from this show \<open>x + (y + z) = x + y + z\<close>
    by (unfold plus_fun_def disjoint_fun_def) (metis sepalg_assoc)
next
     fix x y z :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x \<sharp> y\<close>
    by (unfold plus_fun_def disjoint_fun_def) blast
next
     fix x y z :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x + y \<sharp> z\<close>
    by (unfold plus_fun_def disjoint_fun_def) blast
qed

end

instantiation "fun" :: (type, strong_sepalg)strong_sepalg
begin

instance
  by standard (auto simp add: plus_fun_def disjoint_fun_def sepalg_pairwise2)

end

instantiation "fun" :: (type,cancellative_sepalg)cancellative_sepalg
begin

instance
proof
     fix x y z :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>x + z = y + z\<close>
     and \<open>x \<sharp> z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x = y\<close>
    by (clarsimp simp add: plus_fun_def disjoint_fun_def) (meson ext sepalg_cancel_iff)
qed

end

lemma partial_map_plus:
    fixes f g :: \<open>'a \<rightharpoonup> 'b\<close>
  assumes \<open>f \<sharp> g\<close>
    shows \<open>f + g = f ++ g\<close>
using assms by (clarsimp simp add: disjoint_fun_def disjoint_option_def plus_fun_def plus_option_def
  map_add_def intro!: ext split: option.splits) (metis option.discI)

lemma partial_map_plus_update_right [simp]:
    fixes f g :: \<open>'a \<rightharpoonup> 'b\<close>
  assumes \<open>f \<sharp> g\<close>
      and \<open>a \<in> dom g\<close>
    shows \<open>f + g(a \<mapsto> v) = (f + g)(a \<mapsto> v)\<close>
using assms by (clarsimp simp add: disjoint_fun_def disjoint_option_def plus_fun_def plus_option_def
  map_add_def intro!: ext split: option.splits) (metis option.discI)

lemma partial_map_plus_update_left [simp]:
    fixes f g :: \<open>'a \<rightharpoonup> 'b\<close>
  assumes \<open>f \<sharp> g\<close>
      and \<open>a \<in> dom f\<close>
    shows \<open>f(a \<mapsto> v) + g = (f + g)(a \<mapsto> v)\<close>
using assms by (clarsimp simp add: disjoint_fun_def disjoint_option_def plus_fun_def plus_option_def
  map_add_def intro!: ext split: option.splits)

(*<*)
end
(*>*)
