(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Shareable_Value
  imports
    "HOL-Library.Datatype_Records"
    Shallow_State_Logic.Apartness
    Shallow_State_Logic.Assertion_Language
    Shallow_State_Logic.Separation_Algebra
    Shallow_State_Logic.Tree_Shares
    Data_Structures.RedBlackTree_Extensional
begin
(*>*)

subsection\<open>Shareable values\<close>

text\<open>A \<^verbatim>\<open>shareable_value\<close> is a concrete implementation for a spatial resource that is
\begin{enumerate}
\item
readable,
\item
writable,
\item
arbitrarily shareable.
\end{enumerate}

We define the underlying separation algebra and prove that it is well-behaved
(i.e. it's a strong, cancellative separation algebra).\<close>

datatype 'v shareable_value
  = Shared_Value \<open>nonempty_share\<close> \<open>'v\<close>
  | No_Value

definition map_shareable_value :: \<open>('v \<Rightarrow> 'w) \<Rightarrow> ('v shareable_value \<Rightarrow> 'w shareable_value)\<close> where
  \<open>map_shareable_value f val \<equiv>
     case val of
       No_Value          \<Rightarrow> No_Value
     | Shared_Value sh v \<Rightarrow> Shared_Value sh (f v)\<close>

instantiation shareable_value :: (type)apart
begin

definition zero_shareable_value :: \<open>'v shareable_value\<close> where
  \<open>zero_shareable_value \<equiv> No_Value\<close>

fun disjoint_shareable_value :: \<open>'v shareable_value \<Rightarrow> 'v shareable_value \<Rightarrow> bool\<close> where
  \<open>disjoint_shareable_value No_Value _        = True\<close> |
  \<open>disjoint_shareable_value _        No_Value = True\<close> |
  \<open>disjoint_shareable_value (Shared_Value sh\<^sub>1 v\<^sub>1) (Shared_Value sh\<^sub>2 v\<^sub>2) =
    (Rep_nonempty_share sh\<^sub>1 \<sharp> Rep_nonempty_share sh\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2)\<close>

instance
proof
   fix x :: \<open>'a shareable_value\<close>
  show \<open>x \<sharp> 0\<close>
    by (cases x) (auto simp add: zero_shareable_value_def)
next
   fix x y :: \<open>'a shareable_value\<close>
  show \<open>x \<sharp> y \<longleftrightarrow> y \<sharp> x\<close>
    by (cases x; cases y) auto
next
     fix x :: \<open>'a shareable_value\<close>
  assume \<open>x \<sharp> x\<close>
  from this and bot.not_eq_extremum Rep_nonempty_share show \<open>x = 0\<close>
    by (cases x) (auto simp add: zero_shareable_value_def disjoint_share_def)
qed

end

instantiation shareable_value :: (type)sepalg
begin

fun plus_shareable_value :: \<open>'v shareable_value \<Rightarrow> 'v shareable_value \<Rightarrow> 'v shareable_value\<close> where
  \<open>plus_shareable_value No_Value              y                    = y\<close> |
  \<open>plus_shareable_value x                     No_Value             = x\<close> |
  \<open>plus_shareable_value (Shared_Value sh\<^sub>1 v\<^sub>1) (Shared_Value sh\<^sub>2 v\<^sub>2) =
    Shared_Value (sh\<^sub>1 + sh\<^sub>2) v\<^sub>1\<close>

instance
proof
   fix x :: \<open>'a shareable_value\<close>
  show \<open>x + 0 = x\<close>
    by (cases x) (auto simp add: zero_shareable_value_def)
next
     fix x y :: \<open>'a shareable_value\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>x + y = y + x\<close>
    by (cases x; cases y; clarsimp simp add: plus_nonempty_share_def) (metis
      plus_nonempty_share.rep_eq sup.commute)
next
     fix x y z :: \<open>'a shareable_value\<close>
  assume \<open>x \<sharp> y\<close>
     and \<open>y \<sharp> z\<close>
     and \<open>x \<sharp> z\<close>
  from this show \<open>x + (y + z) = x + y + z\<close>
    by (cases x; cases y; cases z; clarsimp) (metis Rep_nonempty_share_inject inf_sup_aci(6)
      plus_nonempty_share.rep_eq)
next
     fix x y z :: \<open>'a shareable_value\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this and plus_nonempty_share.rep_eq show \<open>x \<sharp> y\<close>
    by (cases x; cases y; cases z) (auto simp add: plus_share_def)
next
     fix x y z :: \<open>'a shareable_value\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x + y \<sharp> z\<close>
    by (cases x; cases y; cases z; clarsimp) (metis disjoint_sym plus_nonempty_share.rep_eq
      plus_share_def sepalg_apart_assoc2)
qed

end

instantiation shareable_value :: (type)strong_sepalg
begin

instance
proof
  fix x y z :: \<open>'a shareable_value\<close>
  assume \<open>x \<sharp> y\<close>
  {
    fix nx ny nz vx vy vz
    assume \<open>x = Shared_Value nx vx\<close>
       and \<open>y = Shared_Value ny vy\<close>
       and \<open>z = Shared_Value nz vz\<close>
    moreover from this \<open>x \<sharp> y\<close> have \<open>vx = vy\<close> and \<open>Rep_nonempty_share nx \<sharp> Rep_nonempty_share ny\<close>
      by auto
    moreover {
      assume \<open>Rep_nonempty_share nz \<sharp> Rep_nonempty_share (nx + ny)\<close>
        and \<open>vz = vy\<close>
      from this calculation \<open>x \<sharp> y\<close> have \<open>Rep_nonempty_share ny \<sharp> Rep_nonempty_share nz\<close>
        using plus_nonempty_share.rep_eq plus_share_def by auto
    } moreover {
      assume \<open>Rep_nonempty_share nz \<sharp> Rep_nonempty_share (nx + ny)\<close>
        and \<open>vz = vy\<close>
      from this calculation \<open>x \<sharp> y\<close> have \<open>Rep_nonempty_share nx \<sharp> Rep_nonempty_share nz\<close>
        by (metis disjoint_sym plus_nonempty_share.rep_eq plus_share_def sepalg_apart_plus sepalg_comm)
    } moreover {
      assume \<open>vy = vz\<close>
        and \<open>Rep_nonempty_share nx \<sharp> Rep_nonempty_share nz\<close>
        and \<open>Rep_nonempty_share nx \<sharp> Rep_nonempty_share ny\<close>
        and \<open>Rep_nonempty_share ny \<sharp> Rep_nonempty_share nz\<close>
      from this calculation \<open>x \<sharp> y\<close> have \<open>Rep_nonempty_share nz \<sharp> Rep_nonempty_share (nx + ny)\<close>
        by (metis disjoint_sym plus_nonempty_share.rep_eq plus_share_def sepalg_pairwise2)
    }
    ultimately have \<open>(x + y) \<sharp> z \<longleftrightarrow> (y \<sharp> z \<and> x \<sharp> z)\<close>
      by auto
  }
  from this show \<open>(x + y) \<sharp> z = (y \<sharp> z \<and> x \<sharp> z)\<close>
    by (cases x; cases y; cases z) auto
qed

end

instantiation shareable_value :: (type)cancellative_sepalg
begin

instance
proof
     fix x y z :: \<open>'a shareable_value\<close>
  assume 1: \<open>x + z = y + z\<close>
     and 2: \<open>x \<sharp> z\<close>
     and 3: \<open>y \<sharp> z\<close>
  moreover {
       fix share\<^sub>x e\<^sub>x share\<^sub>y e\<^sub>y share\<^sub>z e\<^sub>z
    assume \<open>x = Shared_Value share\<^sub>x e\<^sub>x\<close>
       and \<open>y = Shared_Value share\<^sub>y e\<^sub>y\<close>
       and \<open>z = Shared_Value share\<^sub>z e\<^sub>z\<close>
    moreover from this have \<open>Shared_Value (share\<^sub>x + share\<^sub>z) e\<^sub>x = Shared_Value (share\<^sub>y + share\<^sub>z) e\<^sub>y\<close>
      using 1 by auto
    moreover from this have \<open>share\<^sub>x + share\<^sub>z = share\<^sub>y + share\<^sub>z\<close> and \<open>e\<^sub>x = e\<^sub>y\<close>
      by auto
    ultimately have \<open>x = y\<close>
      by (metis 2 3 Rep_nonempty_share_inject disjoint_shareable_value.simps(3) plus_nonempty_share.rep_eq plus_share_def
          sepalg_cancel_iff)
  }
  moreover {
       fix share\<^sub>x e\<^sub>x share\<^sub>z e\<^sub>z
    assume \<open>x = Shared_Value share\<^sub>x e\<^sub>x\<close>
       and \<open>y = No_Value\<close>
       and \<open>z = Shared_Value share\<^sub>z e\<^sub>z\<close>
    from this and 1 and 2 and 3 have \<open>x = y\<close>
      by (metis plus_shareable_value.simps(1) reflE sepalg_apart_plus2)
  }
  moreover {
       fix share\<^sub>y e\<^sub>y share\<^sub>z e\<^sub>z
    assume \<open>x = No_Value\<close>
       and \<open>y = Shared_Value share\<^sub>y e\<^sub>y\<close>
       and \<open>z = Shared_Value share\<^sub>z e\<^sub>z\<close>
    from this and 1 and 2 and 3 have \<open>x = y\<close>
      by (metis plus_shareable_value.simps(1) reflE sepalg_apart_plus2)
  }
  ultimately show \<open>x = y\<close>
    by (metis plus_shareable_value.simps(1) sepalg_comm shareable_value.exhaust)
qed

end

declare zero_shareable_value_def [simp]

lemma no_value_unit [simp]:
  shows \<open>x + No_Value = x\<close>
by (cases x) auto

lemma no_value_unit2 [simp]:
  shows \<open>No_Value + x = x\<close>
by (cases x) auto

lemma disjoint_sharable_valueI [intro]:
  assumes \<open>x = No_Value \<or> y = No_Value \<or>
           (\<exists>sx sy vx vy.
                 Rep_nonempty_share sx \<sharp> Rep_nonempty_share sy \<and> vx = vy \<and>
                 x = Shared_Value sx vx \<and> y = Shared_Value sy vy)\<close>
  shows \<open>x \<sharp> y\<close>
using assms by (cases x; cases y) auto

lemma disjoint_shareable_valueE [elim]:
    fixes x y :: \<open>'v shareable_value\<close>
  assumes \<open>x\<sharp>y\<close>
      and \<open>x = No_Value \<Longrightarrow> R\<close>
      and \<open>y = No_Value \<Longrightarrow> R\<close>
      and \<open>\<And>shx shy v. Rep_nonempty_share shx \<sharp> Rep_nonempty_share shy \<Longrightarrow> x = Shared_Value shx v \<Longrightarrow>
              y = Shared_Value shy v \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (cases x; cases y) auto

(*<*)
context
  includes lattice_syntax
begin
(*>*)

lemma shareable_value_disjoint_top:
  shows \<open>Shared_Value \<top> v \<sharp> \<sigma> \<longleftrightarrow> \<sigma> = No_Value\<close>
    and \<open>\<sigma> \<sharp> Shared_Value \<top> v \<longleftrightarrow> \<sigma> = No_Value\<close>
proof -
  show \<open>Shared_Value \<top> v \<sharp> \<sigma> \<longleftrightarrow> \<sigma> = No_Value\<close>
    using Rep_nonempty_share bot.not_eq_extremum disjoint_share_def top_nonempty_share.rep_eq
      by (cases \<sigma>) (auto simp add: disjoint_share_def)
  from this show \<open>\<sigma> \<sharp> Shared_Value \<top> v \<longleftrightarrow> \<sigma> = No_Value\<close>
    by auto
qed

lemma shareable_value_disjoint_from_value:
  shows \<open>\<sigma> \<sharp> (Shared_Value sh v) \<longleftrightarrow> (\<sigma> = No_Value \<or> (\<exists>sh'. (Rep_nonempty_share sh \<sharp> Rep_nonempty_share sh') \<and> \<sigma> = Shared_Value sh' v))\<close>
by (cases \<sigma>) (auto simp add: derived_orderE intro!: derived_orderI)

lemma shareable_value_upwards_aux:
  assumes \<open>Rep_nonempty_share sh0 \<preceq> Rep_nonempty_share sh1\<close>
  shows \<open>Shared_Value sh0 v1 \<preceq> Shared_Value sh1 v1\<close>
proof -
  obtain z where z: \<open>Rep_nonempty_share sh0 \<sharp> z\<close> \<open>Rep_nonempty_share sh0 + z = Rep_nonempty_share sh1\<close>
    using assms by blast
  then show ?thesis 
  unfolding derived_order_def  
  by (metis Abs_nonempty_share_inverse Rep_nonempty_share_inverse bot.not_eq_extremum disjoint_shareable_value.simps(3) mem_Collect_eq
      plus_shareable_value.simps(3) sepalg_ident2 zero_disjoint plus_nonempty_share.rep_eq plus_share_def zero_share_def)
qed

corollary shareable_value_upwards_closure_core:
  shows \<open>(Shared_Value sh0 v0 \<preceq> Shared_Value sh1 v1) \<longleftrightarrow> (v0 = v1 \<and> Rep_nonempty_share sh0 \<preceq> Rep_nonempty_share sh1)\<close>
    and \<open>No_Value \<preceq> Shared_Value sh v \<longleftrightarrow> True\<close>
    and \<open>Shared_Value sh v \<preceq> No_Value \<longleftrightarrow> False\<close>
proof -
  have \<open>\<And>sh'. \<lbrakk>Rep_nonempty_share sh' \<sharp> Rep_nonempty_share sh0\<rbrakk>
           \<Longrightarrow> \<exists>z. z \<sharp> Rep_nonempty_share sh0 \<and> Rep_nonempty_share sh0 + z = Rep_nonempty_share (sh0 + sh')\<close>
    using plus_nonempty_share.rep_eq plus_share_def by auto
  then have \<open>Shared_Value sh0 v0 \<preceq> Shared_Value sh1 v1 \<Longrightarrow> Rep_nonempty_share sh0 \<preceq> Rep_nonempty_share sh1\<close>
    by (auto simp: derived_order_def shareable_value_disjoint_from_value)
  then show \<open>(Shared_Value sh0 v0 \<preceq> Shared_Value sh1 v1) \<longleftrightarrow> (v0 = v1 \<and> Rep_nonempty_share sh0 \<preceq> Rep_nonempty_share sh1)\<close>
    by (fastforce intro: shareable_value_upwards_aux)
next
  show \<open>No_Value \<preceq> Shared_Value sh v \<longleftrightarrow> True\<close>
    by fastforce
next
  show \<open>Shared_Value sh v \<preceq> No_Value \<longleftrightarrow> False\<close>
    by fastforce
qed

corollary shareable_value_upwards_closure:
  assumes \<open>Shared_Value sh v \<preceq> \<sigma>\<close>
    shows \<open>\<exists>sh'. \<sigma> = Shared_Value sh' v \<and> Rep_nonempty_share sh \<preceq> Rep_nonempty_share sh'\<close>
using assms by (cases \<sigma>) (auto simp add: shareable_value_upwards_closure_core)

corollary shareable_value_upwards_closureE:
  assumes \<open>Shared_Value sh v \<preceq> \<sigma>\<close>
      and \<open>\<And>sh'. \<sigma> = Shared_Value sh' v \<Longrightarrow> Rep_nonempty_share sh \<preceq> Rep_nonempty_share sh' \<Longrightarrow> R\<close>
    shows R
using assms by (meson shareable_value_upwards_closure)

corollary shareable_value_upwards_closureI:
  assumes \<open>\<sigma> = Shared_Value sh' v\<close>
      and \<open>Rep_nonempty_share sh \<preceq> Rep_nonempty_share sh'\<close>
    shows \<open>Shared_Value sh v \<preceq> \<sigma>\<close>
by (simp add: assms shareable_value_upwards_closure_core)

corollary shareable_value_uc_state:
  shows \<open>\<up>\<^sub>s (Shared_Value sh v) = {\<sigma>. \<exists>sh'. \<sigma> = Shared_Value sh' v \<and> Rep_nonempty_share sh' \<in> \<up>\<^sub>s (Rep_nonempty_share sh)}\<close>
by (clarsimp simp add: uc_state_def shareable_value_upwards_closure_core)
  (metis (no_types, opaque_lifting) shareable_value_upwards_closure shareable_value_upwards_closureI)

lemma shareable_value_uc_state_asepconj:
  assumes \<open>Rep_nonempty_share sh0 \<sharp> Rep_nonempty_share sh1\<close>
      and \<open>v0 = v1\<close>
    shows \<open>\<up>\<^sub>s (Shared_Value sh0 v0) \<star> \<up>\<^sub>s (Shared_Value sh1 v1) = \<up>\<^sub>s (Shared_Value (sh0 + sh1) v0)\<close>
using assms by (simp add: asepconj_uc_state)

lemma shareable_value_uc_state_asepconj_general:
  shows \<open>\<up>\<^sub>s (Shared_Value sh0 v0) \<star> \<up>\<^sub>s (Shared_Value sh1 v1) =
     (if Rep_nonempty_share sh0 \<sharp> Rep_nonempty_share sh1 \<and> v0 = v1 then
        \<up>\<^sub>s (Shared_Value (sh0 + sh1) v0)
      else
        {})\<close>
by (cases \<open>Rep_nonempty_share sh0 \<sharp> Rep_nonempty_share sh1\<close>; cases \<open>v0 = v1\<close>) (auto simp add:
  shareable_value_uc_state_asepconj asepconj_uc_state_general)

lemma nonempty_share_top_eq:
  shows \<open>(Rep_nonempty_share sh = \<top>) \<longleftrightarrow> (sh = \<top>)\<close>
by (metis Rep_nonempty_share_inverse top_nonempty_share.rep_eq)

lemma share_uc_state_top:
  shows \<open>\<up>\<^sub>s (\<top>::share) = {\<top>}\<close>
by (auto simp add: uc_state_def derived_order_def plus_share_def)

corollary shareable_value_uc_state_top:
  shows \<open>\<up>\<^sub>s (Shared_Value \<top> v) = { Shared_Value \<top> v}\<close>
by (clarsimp simp add: nonempty_share_top_eq share_uc_state_top shareable_value_uc_state
  top_nonempty_share.rep_eq)

definition shareable_value_to_share :: \<open>'v shareable_value \<Rightarrow> share\<close> where
  \<open>shareable_value_to_share v \<equiv>
     case v of
       No_Value          \<Rightarrow> bot
     | Shared_Value sh _ \<Rightarrow> Rep_nonempty_share sh\<close>

lemma shareable_value_to_share_plus:
  assumes \<open>a \<sharp> b\<close>
    shows \<open>shareable_value_to_share (a + b) = shareable_value_to_share a + shareable_value_to_share b\<close>
using assms by (auto simp add: plus_nonempty_share.rep_eq plus_share_def sup_commute
  shareable_value_to_share_def split!: shareable_value.splits)

definition sh_dom :: \<open>('a \<Rightarrow> 'v shareable_value) \<Rightarrow> 'a set\<close> where
  \<open>sh_dom f \<equiv> { a. \<exists>sh v. f a = Shared_Value sh v }\<close>

lemma sh_dom_empty [simp]:
  shows \<open>sh_dom (\<lambda>_. No_Value) = {}\<close>
by (auto simp add: sh_dom_def)

lemma sh_dom_is_empty [intro]:
  assumes \<open>sh_dom f = {}\<close>
    shows \<open>f = (\<lambda>x. No_Value)\<close>
using assms by (clarsimp simp add: sh_dom_def) (metis (mono_tags, lifting) emptyE mem_Collect_eq
  shareable_value.exhaust)

lemma sh_domI [intro]:
  assumes \<open>f a = Shared_Value sh v\<close>
    shows \<open>a \<in> sh_dom f\<close>
using assms by (auto simp add: sh_dom_def)

lemma sh_domE [elim]:
  assumes \<open>a \<in> sh_dom f\<close>
      and \<open>\<And>sh v. f a = Shared_Value sh v \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: sh_dom_def)

lemma shareable_map_plus_dom [simp]:
  fixes f g :: \<open>'a \<Rightarrow> 'v shareable_value\<close>
  shows \<open>sh_dom (f + g) = sh_dom f \<union> sh_dom g\<close>
proof (intro equalityI subsetI)
     fix x
  assume \<open>x \<in> sh_dom (f + g)\<close>
  from this obtain sh\<^sub>1 v\<^sub>1 where \<open>Shared_Value sh\<^sub>1 v\<^sub>1 = (f + g) x\<close>
    by auto
  moreover from this have \<open>x \<in> sh_dom f \<or> x \<in> sh_dom g\<close>
    by (metis plus_fun_def plus_shareable_value.elims sh_domI)
  ultimately show \<open>x \<in> sh_dom f \<union> sh_dom g\<close>
    by auto
next
     fix x
  assume \<open>x \<in> sh_dom f \<union> sh_dom g\<close>
  then show \<open>x \<in> sh_dom (f + g)\<close>
    by (simp add: plus_fun_def sh_dom_def) (metis plus_shareable_value.elims)
qed

lemma partial_map_plus_dom [simp]:
  fixes f g :: \<open>'a \<rightharpoonup> 'b\<close>
  shows \<open>dom (f + g) = dom f \<union> dom g\<close>
by (auto simp add: plus_fun_def plus_option_def split: option.splits)

definition nonempty_share_combine :: \<open>nonempty_share \<Rightarrow> nonempty_share \<Rightarrow> nonempty_share\<close> where
  \<open>nonempty_share_combine sh0 sh1 \<equiv> sh0 + sh1\<close>

end

(*<*)
end
(*>*)
