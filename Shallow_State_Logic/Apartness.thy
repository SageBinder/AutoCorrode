(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Generic state-logic foundation. *)
(*<*)
theory Apartness
  imports Main
begin
(*>*)

section\<open>Apartness\<close>

text\<open>Separation logic rests on a notion of apartness/disjointness for parts of the state. In this
section, we define a type class and notation for types with an apartness relation, and instantiate
it with a few basic types and type constructors.

We always require a designated element which is apart from every other element, and use the
\<^class>\<open>zero\<close> typeclass for that:\<close>

class apart_pre = zero +
    fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix "\<sharp>" 60)
    assumes zero_disjoint [simp, intro]: \<open>x \<sharp> 0\<close>
        and disjoint_sym [simp]: \<open>x \<sharp> y \<longleftrightarrow> y \<sharp> x\<close>

lemma (in apart_pre) zero_disjoint2 [simp, intro]:
  shows \<open>0 \<sharp> x\<close>
  by auto

text\<open>Note that \<^emph>\<open>every\<close> type trivially implements \<^class>\<open>apart_pre\<close> via \<^term>\<open>\<forall>x. x \<sharp> x\<close>, but this
disregards the intuition that elements apart from themselves should be trivial in some sense.  The
strongest formalization of this is to require uniqueness for self-apart elements, as captured in the
following specialization of \<^class>\<open>apart_pre\<close>:\<close>
                 
class apart = apart_pre +
  assumes unique [intro]: \<open>x \<sharp> x \<Longrightarrow> x = 0\<close>

lemma (in apart) reflE [elim]:
  assumes \<open>x \<sharp> x\<close>
      and \<open>x = 0 \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by(auto dest: local.unique)

subsection\<open>Instantiations\<close>

text\<open>In this section we develop some basic examples of types with a natural apartness relation:
optional values \<^typ>\<open>'a option\<close>, sets \<^typ>\<open>'a set\<close>, and --- in case \<^typ>\<open>'b\<close> has an apartness
relation---maps \<^typ>\<open>'a \<Rightarrow> 'b\<close>. As a special case, we recover the canonical apartness relation for
\<^emph>\<open>partial\<close> maps \<^typ>\<open>'a \<rightharpoonup> 'b\<close> which are equivalent to \<^typ>\<open>'a \<Rightarrow> 'b option\<close>.\<close>

subsubsection\<open>Apartness for optional values\<close>

text\<open>Optional values are apart if at least one of them is \<^term>\<open>None\<close>.\<close>

instantiation option :: (type)apart
begin

definition zero_option :: \<open>'a option\<close> where
  \<open>zero_option \<equiv> None\<close>

definition disjoint_option :: \<open>'a option \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>disjoint_option x y \<equiv> case (x, y) of
    (Some _, Some _) \<Rightarrow> False
    | otherwise      \<Rightarrow> True\<close>

instance
proof
   fix x :: \<open>'a option\<close>
  show \<open>x \<sharp> 0\<close>
    by (cases x; auto simp add: zero_option_def disjoint_option_def)
next
   fix x y :: \<open>'a option\<close>
  show \<open>x \<sharp> y \<longleftrightarrow> y\<sharp>x\<close>
    by (cases x; cases y; simp add: disjoint_option_def)
next
     fix x :: \<open>'a option\<close>
  assume \<open>x \<sharp> x\<close>
  from this show \<open>x = 0\<close>
    by (cases x; simp add: disjoint_option_def zero_option_def)
qed

end

subsubsection\<open>Apartness for products\<close>

instantiation "prod" :: (apart, apart)apart
begin

definition disjoint_prod :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod x y \<equiv> (fst x) \<sharp> (fst y) \<and> (snd x) \<sharp> (snd y)\<close>

definition zero_prod :: \<open>'a \<times> 'b\<close> where
  \<open>zero_prod \<equiv> (0, 0)\<close>

instance  
  by (standard, auto simp add: disjoint_prod_def zero_prod_def)

end

subsubsection\<open>Apartness for sets\<close>

text\<open>Sets are ``apart'' if they are disjoint in the usual set-theoretic sense.\<close>

instantiation set :: (type)apart
begin

definition zero_set :: \<open>'a set\<close> where
  \<open>zero_set \<equiv> Set.empty\<close>

definition disjoint_set :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>x \<sharp> y \<longleftrightarrow> (x \<inter> y = {})\<close>

instance
proof
   fix x :: \<open>'a set\<close>
  show \<open>x \<sharp> 0\<close>
    by (auto simp add: disjoint_set_def zero_set_def)
next
   fix x y :: \<open>'a set\<close>
  show \<open>x \<sharp> y \<longleftrightarrow> y \<sharp> x\<close>
    by (auto simp add: disjoint_set_def)
next
     fix x :: \<open>'a set\<close>
  assume \<open>x \<sharp> x\<close>
  from this show \<open>x = 0\<close>
    by (simp add: disjoint_set_def zero_set_def)
qed

end

subsubsection\<open>Apartness for total maps\<close>

text\<open>Next, we define an apartness relation for (total) functions \<^typ>\<open>'a \<Rightarrow> 'b\<close> whose codomain
\<^typ>\<open>'b\<close> has an apartness relation. In this case, apartness is defined pointwise in the codomain,
while the domain can be of \<^emph>\<open>any\<close> type.\<close>

instantiation "fun" :: (type, apart_pre)apart_pre
begin

definition zero_fun :: \<open>'a \<Rightarrow> 'b\<close> where
  \<open>zero_fun \<equiv> \<lambda> _. 0\<close>

definition disjoint_fun:: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> where
   \<open>f \<sharp> g \<equiv> \<forall>x. f x \<sharp> g x\<close>

instance
proof
   fix f :: \<open>'a \<Rightarrow> 'b\<close> 
  show \<open>f \<sharp> 0\<close>
    by (simp add: Apartness.zero_fun_def disjoint_fun_def)
next
   fix x y :: \<open>'a \<Rightarrow> 'b\<close>
  show \<open>x \<sharp> y \<longleftrightarrow> y \<sharp> x\<close>
    by (auto simp add: disjoint_fun_def)
qed

end

instantiation "fun" :: (type, apart)apart
begin

instance
proof
     fix f :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>f \<sharp> f\<close>
  from this show \<open>f = 0\<close>
    using unique by (auto simp add: disjoint_fun_def zero_fun_def)
qed

end

subsubsection\<open>Apartness for partial maps\<close>

text\<open>A notable special case of the previous instantiations are \<^emph>\<open>partial maps\<close> \<^typ>\<open>'a \<rightharpoonup> 'b\<close>: those
are modelled as total functions \<^typ>\<open>'a \<Rightarrow> 'b option\<close> (with unmapped elements corresponding to
elements mapped to \<^term>\<open>None\<close>) and hence inherit implementations \<^class>\<open>apart_pre\<close> and \<^class>\<open>apart\<close>.

Concretely, two partial maps are apart if and only if their domains are apart as sets:\<close>

lemma disjoint_mapI:
    fixes f g :: \<open>'a \<rightharpoonup> 'b\<close>
  assumes \<open>Map.dom f \<inter> Map.dom g = {}\<close>
    shows \<open>f \<sharp> g\<close>
  by (metis assms disjoint_fun_def disjoint_iff disjoint_sym domIff zero_disjoint zero_option_def)

lemma disjoint_mapE:
    fixes f g :: \<open>'a \<rightharpoonup> 'b\<close>
  assumes \<open>f \<sharp> g\<close>
  shows \<open>Map.dom f \<inter> Map.dom g = {}\<close>
proof -
  {
       fix x :: 'a
    assume \<open>x \<in> dom f\<close>
       and \<open>x \<in> dom g\<close>
    then have False
      using assms unfolding disjoint_option_def disjoint_fun_def
      by (metis domD prod.case option.case(2))
  }
  from this show ?thesis
    by auto
qed

lemma disjoint_map_iff:
    fixes f g :: \<open>'a \<rightharpoonup> 'b\<close>
    shows \<open>f \<sharp> g \<longleftrightarrow> Map.dom f \<inter> Map.dom g = {}\<close>
  using disjoint_mapE disjoint_mapI by auto

(*<*)
end
(*>*)
