(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Generic state-logic foundation. *)
(*<*)
theory Tree_Shares
  imports Main Apartness Separation_Algebra
begin
(*>*)

section \<open>Share accounting\<close>

text
\<open>To reason about shared ownership and concurrent access to resources,
is is useful to have a system that allows precise accounting for permissions
to resources (memory regions, primarily, but also more abstract resources).
The share accounting system developed here is one way to do this, and is
closely based on the paper "A Fresh Look at Separation Algebras and
Share Accounting" by Dockins, Hobor and Appel.

Algebraically, this share model is a Boolean algebra endowed with an
extra multiplication-like structure called share "relativization".

In addition, it supports two key share accounting use cases: splitting
and token counting. In the splitting use case, any given nonempty share
can be split into two disjoint subshares (each also nonempty) which
combine to give the original share. Splitting is useful for reasoning
about "borrowing" use cases in both sequential and concurrent settings
where some resource owner (or borrower) wishes to allow another
context (e.g., a function to be called, or a separate thread) shared access
to a resource. This use case makes sense primarily when the two contexts
involved are peers, in some sense.

The token counting mode is useful when a central authority is used to
keep track of a shared resource, such as a reader/writer lock.
The central authority retains "most" of the permission, but can
pass out portions of the resource to others, collecting them together
later. In this setting, the token authority need only count how many
tokens it has passed out.

Using share relativization, these two modes can be combined together
in interesting ways, providing flexibility in the styles of share
accounting that can be expressed.\<close>

subsection \<open>Binary Boolean trees\<close>

text
\<open>Shares are built out of binary trees with Boolean values
at the leaves. We impose a preorder on these trees and select
out a subset of trees that are "canonical". On canonical trees,
the preorder is actually a partial order, and the operations we
define on trees preserve the property of being canonical.\<close>

datatype tree
  = Leaf \<open>bool\<close>
  | Node \<open>tree\<close> \<open>tree\<close>

abbreviation (input) Top where
  \<open>Top \<equiv> Leaf True\<close>

abbreviation (input) Bot where
  \<open>Bot \<equiv> Leaf False\<close>

text
\<open>It is convenient to define induction and case analysis
principles that automatically split into sub-cases based
on the value of Boolean leaves, so we do that here.\<close>

lemma tree_deep_induct [case_names Bot Top Node]:
  assumes \<open>P Bot\<close>
      and \<open>P Top\<close>
      and \<open>\<And> a b. P a \<Longrightarrow> P b \<Longrightarrow> P (Node a b)\<close>
    shows \<open>P t\<close>
using assms by (induction t; metis)

lemma tree_deep_exhaust [case_names Bot Top Node]:
  assumes \<open>t = Bot \<Longrightarrow> P\<close>
      and \<open>t = Top \<Longrightarrow> P\<close>
      and \<open>\<And>a b. t = Node a b \<Longrightarrow> P\<close>
    shows \<open>P\<close>
using assms by (cases t; force)

text
\<open>Trees are canonical just when they do not contain any
instances of the pattern \<^verbatim>\<open>Node (Leaf b) (Leaf b)\<close>. Such
trees are canonically represented instead by the term
\<^verbatim>\<open>Leaf b\<close>.\<close>

inductive canonical :: \<open>tree \<Rightarrow> bool\<close> where
  canonical_Leaf: \<open>canonical (Leaf b)\<close> |
  canonical_Node:
    \<open>canonical x \<Longrightarrow>
     canonical y \<Longrightarrow>
     (case (x, y) of (Leaf b1, Leaf b2) \<Rightarrow> b1 \<noteq> b2 | _ \<Rightarrow> True) \<Longrightarrow>
     canonical (Node x y)\<close>

inductive_cases canonical_NodeE: \<open>canonical (Node a b)\<close>
inductive_cases canonical_Node_LeafE: \<open>canonical (Node (Leaf b1) (Leaf b2))\<close>

declare canonical.intros [simp]

text
\<open>\<^verbatim>\<open>node\<close> is a "smart constructor" that builds an actual \<^verbatim>\<open>Node\<close>,
out of the two given sub-trees, except when both sub-trees are
equal \<^verbatim>\<open>Leaf\<close> values, in which case the leaves are folded up
into a top-level \<^verbatim>\<open>Leaf\<close> value. This operation is guaranteed
to build a canonical tree out of canonical sub-trees.\<close>

fun node :: \<open>tree \<Rightarrow> tree \<Rightarrow> tree\<close>  where
  \<open>node Bot Bot = Bot\<close> |
  \<open>node Top Top = Top\<close> |
  \<open>node x y = Node x y\<close>

fun_cases node_LeafE: \<open>node x y = Leaf b\<close>
fun_cases node_NodeE: \<open>node x y = Node x y\<close>

lemma node_canonical [simp]:
  assumes \<open>canonical x\<close>
      and \<open>canonical y\<close>
    shows \<open>canonical (node x y)\<close>
using assms by (auto intro: node.cases[where x=\<open>(x, y)\<close>] split: tree.splits)

fun canon :: \<open>tree \<Rightarrow> tree\<close> where
  \<open>canon (Leaf b) = Leaf b\<close> |
  \<open>canon (Node a b) = node (canon a) (canon b)\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma canon_canonical:
  shows \<open>canonical (canon x)\<close>
by (induction x) auto

text
\<open>For code extraction purposes, here we define an explicit equality
test algorithm for share trees.\<close>

fun tree_eq_test :: \<open>tree \<Rightarrow> tree \<Rightarrow> bool\<close> where
  \<open>tree_eq_test (Leaf x) (Leaf y) = (x = y)\<close> |
  \<open>tree_eq_test (Leaf x) (Node l r) = False\<close> |
  \<open>tree_eq_test (Node l r) (Leaf y) = False\<close> |
  \<open>tree_eq_test (Node lx rx) (Node ly ry) = (tree_eq_test lx ly \<and> tree_eq_test rx ry)\<close>

lemma tree_eq_test_correct:
  shows \<open>tree_eq_test x y \<longleftrightarrow> x = y\<close>
by (induction x y rule: tree_eq_test.induct; clarsimp)

text
\<open>Here, we define the ordering relation on trees and its induced
equivalence. It is reflexive and transitive, which makes it a preorder.
Later, we will show that it is antisymmetric on canonical trees.\<close>

instantiation tree :: preorder
begin

fun less_eq_tree :: \<open>tree \<Rightarrow> tree \<Rightarrow> bool\<close> where
  \<open>less_eq_tree (Leaf b1)  (Leaf b2)  = (b1 \<le> b2)\<close> |
  \<open>less_eq_tree (Leaf b)   (Node l r) = (less_eq_tree (Leaf b) l \<and> less_eq_tree (Leaf b) r)\<close> |
  \<open>less_eq_tree (Node l r) (Leaf b)   = (less_eq_tree l (Leaf b) \<and> less_eq_tree r (Leaf b))\<close> |
  \<open>less_eq_tree (Node a b) (Node x y) = (less_eq_tree a x \<and> less_eq_tree b y)\<close>

definition less_tree :: \<open>tree \<Rightarrow> tree \<Rightarrow> bool\<close> where
  \<open>less_tree t u \<longleftrightarrow> t \<le> u \<and> \<not>u \<le> t\<close>

lemma less_eq_tree_trans1:
  assumes \<open>b1 \<le> b2\<close>
      and \<open>(Leaf b2) \<le> z\<close>
    shows \<open>(Leaf b1) \<le> z\<close>
using assms by (induction z; simp)

instance
proof
  fix t u :: \<open>tree\<close>
  show \<open>(t < u) = (t \<le> u \<and> \<not> u \<le> t)\<close>
    by (auto simp add: less_tree_def)
next
  fix t :: \<open>tree\<close>
  show \<open>t \<le> t\<close>
    by (induction t, auto)
next
     fix t u v :: \<open>tree\<close>
  assume \<open>t \<le> u\<close>
     and \<open>u \<le> v\<close>
  from this show \<open>t \<le> v\<close>
    by (induction t u arbitrary: v rule: less_eq_tree.induct) (metis less_eq_tree_trans1
          tree.exhaust less_eq_tree.simps)+
qed

end

fun_cases tree_le_BotE: \<open>x \<le> Bot\<close>

definition tree_eq :: \<open>tree \<Rightarrow> tree \<Rightarrow> bool\<close> (infix \<open>\<simeq>\<close> 50) where
  \<open>x \<simeq> y \<longleftrightarrow> x \<le> y \<and> y \<le> x\<close>

lemma tree_eq_refl [intro]:
  shows \<open>reflp (\<simeq>)\<close>
by (auto simp add: tree_eq_def intro: reflpI)

lemma tree_eq_sym [intro]:
  shows \<open>symp (\<simeq>)\<close>
by (auto simp add: tree_eq_def intro: sympI)

lemma tree_eq_trans [intro]:
  shows \<open>transp (\<simeq>)\<close>
by (auto simp add: tree_eq_def intro: order.trans intro!: transpI)

declare sympE[OF tree_eq_sym, sym]
    and transpE[OF tree_eq_trans, trans]

lemma tree_bot_least [simp]:
  shows \<open>Bot \<le> x\<close>
by (induction x) auto

lemma tree_top_greatest [simp]:
  shows \<open>x \<le> Top\<close>
  by (induction x) auto

text
\<open>The complement operation on trees just complements all the leaves.\<close>

fun tree_comp :: \<open>tree \<Rightarrow> tree\<close> where
  \<open>tree_comp (Leaf b) = Leaf (\<not>b)\<close> |
  \<open>tree_comp (Node a b) = Node (tree_comp a) (tree_comp b)\<close>

lemma tree_comp_canonical [simp]:
  assumes \<open>canonical x\<close>
    shows \<open>canonical (tree_comp x)\<close>
  using assms by (induction x rule: tree_comp.induct) (auto elim: canonical_NodeE intro!:
    canonical.intros split: tree.splits)

text \<open>The least upper bound (LUB) operation on trees.\<close>

fun tree_lub :: \<open>tree \<Rightarrow> tree \<Rightarrow> tree\<close> where
  \<open>tree_lub Top x = Top\<close> |
  \<open>tree_lub Bot x = x\<close> |
  \<open>tree_lub x Top = Top\<close> |
  \<open>tree_lub x Bot = x\<close> |
  \<open>tree_lub (Node a b) (Node c d) = node (tree_lub a c) (tree_lub b d)\<close>

lemma tree_lub_canonical [simp]:
  assumes \<open>canonical x\<close>
      and \<open>canonical y\<close>
    shows \<open>canonical (tree_lub x y)\<close>
using assms by (induction x y rule: tree_lub.induct) (auto elim: canonical_NodeE intro!: node_canonical)

text \<open>The greatest lower bound (GLB) operation on trees.\<close>

fun tree_glb :: \<open>tree \<Rightarrow> tree \<Rightarrow> tree\<close> where
  \<open>tree_glb Top  x = x\<close> |
  \<open>tree_glb Bot x  = Bot\<close> |
  \<open>tree_glb x Top  = x\<close> |
  \<open>tree_glb x Bot  = Bot\<close> |
  \<open>tree_glb (Node a b) (Node c d) = node (tree_glb a c) (tree_glb b d)\<close>

lemma tree_glb_canonical [simp]:
  assumes \<open>canonical x\<close>
      and \<open>canonical y\<close>
    shows \<open>canonical (tree_glb x y)\<close>
using assms by (induction x y rule: tree_glb.induct) (auto elim: canonical_NodeE intro!: node_canonical)

lemma tree_equiv_canonical_equal:
  assumes \<open>tree_eq x y\<close>
      and \<open>canonical x\<close>
      and \<open>canonical y\<close>
    shows \<open>x = y\<close>
using assms unfolding tree_eq_def by (induction x y rule: less_eq_tree.induct) (auto elim: canonical_NodeE)

lemma tree_le_node_leaf:
  shows \<open>Node (Leaf x) (Leaf y) \<le> node (Leaf x) (Leaf y)\<close>
    and \<open>node (Leaf x) (Leaf y) \<le> Node (Leaf x) (Leaf y)\<close>
by (cases x; cases y; fastforce)+

lemma tree_le_node1:
  shows \<open>Node x y \<le> node x y\<close>
  by (cases x; cases y) (auto simp add: tree_le_node_leaf)

lemma tree_le_node2:
  shows \<open>node x y \<le> Node x y\<close>
by (cases x; cases y) (auto simp add: tree_le_node_leaf)

lemma tree_eq_node:
  shows \<open>Node x y \<simeq> node x y\<close>
unfolding tree_eq_def by (simp add: tree_le_node1 tree_le_node2)

lemma tree_eq_Node_node:
  assumes \<open>a \<simeq> x\<close>
      and \<open>b \<simeq> y\<close>
    shows \<open>Node a b \<simeq> node x y\<close>
proof -
  from assms have \<open>Node a b \<simeq> Node x y\<close>
    unfolding tree_eq_def by auto
  also have \<open>Node x y \<simeq> node x y\<close>
    unfolding tree_eq_def by (auto simp add: tree_le_node1 tree_le_node2)
  finally show ?thesis .
qed

lemma tree_le_node_r [simp]:
  assumes \<open>z \<le> Node x y\<close>
    shows \<open>z \<le> node x y\<close>
proof -
  have \<open>Node x y \<le> node x y\<close>
    using assms tree_le_node1 order.trans by blast
  from this and assms show ?thesis
    using order.trans by blast
qed

lemma tree_le_node_l [simp]:
  assumes \<open>Node x y \<le> z\<close>
    shows \<open>node x y \<le> z\<close>
proof -
  have \<open>node x y \<le> Node x y\<close>
    by (rule tree_le_node2)
  from this and assms show ?thesis
    using order.trans by blast
qed

lemma tree_eq_node_r [simp]:
  assumes \<open>z \<simeq> Node x y\<close>
    shows \<open>z \<simeq> node x y\<close>
using assms unfolding tree_eq_def by auto

lemma tree_eq_node_l [simp]:
  assumes \<open>Node x y \<simeq> z\<close>
    shows \<open>node x y \<simeq> z\<close>
using assms unfolding tree_eq_def by auto

lemma tree_lub_above1:
  shows \<open>x \<le> tree_lub x y\<close>
by (induction x y rule: tree_lub.induct) auto

lemma tree_lub_above2:
  shows \<open>y \<le> tree_lub x y\<close>
by (induction x y rule: tree_lub.induct) auto

lemma tree_lub_least:
  assumes \<open>x \<le> z\<close>
      and \<open>y \<le> z\<close>
    shows \<open>tree_lub x y \<le> z\<close>
using assms by (induction x y arbitrary: z rule: tree_lub.induct; clarsimp)
  (metis less_eq_tree.simps tree_deep_exhaust tree_le_node_l)

lemma tree_glb_below1:
  shows \<open>tree_glb x y \<le> x\<close>
by (induction x y rule: tree_lub.induct) auto

lemma tree_glb_below2:
  shows \<open>tree_glb x y \<le> y\<close>
  by (induction x y rule: tree_lub.induct) auto

lemma tree_glb_greatest:
  assumes \<open>z \<le> x\<close>
      and \<open>z \<le> y\<close>
    shows \<open>z \<le> tree_glb x y\<close>
using assms by (induction x y arbitrary: z rule: tree_glb.induct; clarsimp)
  (metis less_eq_tree.simps tree_deep_exhaust tree_le_node_r)

subsection \<open>Shares\<close>

text
\<open>Here we define the type \<^verbatim>\<open>share\<close> as the set of canonical trees,
and instantiate the bounded lattice structure for them.\<close>

typedef share = \<open>{t::tree. canonical t}\<close>
  by (rule_tac x=\<open>Top\<close> in exI, auto)

setup_lifting type_definition_share

text\<open>For code generation purposes:\<close>
instantiation share :: equal
begin

lift_definition equal_share :: \<open>share \<Rightarrow> share \<Rightarrow> bool\<close> is \<open>tree_eq_test\<close> .

instance
  by standard (clarsimp simp add: Rep_share_inject equal_share_def map_fun_def tree_eq_test_correct)

end

instantiation share :: bounded_lattice begin

lift_definition bot_share :: \<open>share\<close> is \<open>Bot\<close> by auto
lift_definition top_share :: \<open>share\<close> is \<open>Top\<close> by auto
lift_definition sup_share :: "share \<Rightarrow> share \<Rightarrow> share" is \<open>tree_lub\<close> by auto
lift_definition inf_share :: "share \<Rightarrow> share \<Rightarrow> share" is \<open>tree_glb\<close> by auto
lift_definition less_eq_share :: "share \<Rightarrow> share \<Rightarrow> bool" is \<open>(\<le>)\<close> .
lift_definition less_share :: "share \<Rightarrow> share \<Rightarrow> bool" is \<open>(<)\<close> .

instance
proof
   fix x y :: \<open>share\<close>
  show \<open>x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x\<close>
    by transfer (simp add: less_tree_def)
next
   fix x :: \<open>share\<close>
  show \<open>x \<le> x\<close>
    by transfer simp
next
     fix x y z :: \<open>share\<close>
  assume \<open>x \<le> y\<close>
     and \<open>y \<le> z\<close>
  from this show \<open>x \<le> z\<close>
    by transfer (blast intro: order.trans)
next
     fix x y :: \<open>share\<close>
  assume \<open>x \<le> y\<close>
     and \<open>y \<le> x\<close>
  from this show \<open>x = y\<close>
    by transfer (simp add: tree_eq_def tree_equiv_canonical_equal)
next
   fix x y :: \<open>share\<close>
  show \<open>inf x y \<le> x\<close>
    by transfer (simp add: tree_glb_below1)
next
   fix x y :: \<open>share\<close>
  show \<open>inf x y \<le> y\<close>
    by transfer (simp add: tree_glb_below2)
next
     fix x y z :: \<open>share\<close>
  assume \<open>x \<le> y\<close>
     and \<open>x \<le> z\<close>
  from this show \<open>x \<le> inf y z\<close>
    by transfer (simp add: tree_glb_greatest)
next
   fix x y :: \<open>share\<close>
  show \<open>x \<le> sup x y\<close>
    by transfer (blast intro: tree_lub_above1)
next
   fix x y :: \<open>share\<close>
  show \<open>y \<le> sup x y\<close>
    by transfer (blast intro: tree_lub_above2)
next
     fix x y z :: \<open>share\<close>
  assume \<open>y \<le> x\<close>
     and \<open>z \<le> x\<close>
  from this show \<open>sup y z \<le> x\<close>
    by transfer (simp add: tree_lub_least)
next
   fix x :: \<open>share\<close>
  show \<open>bot \<le> x\<close>
    by transfer simp
next
   fix x :: \<open>share\<close>
  show \<open>x \<le> top\<close>
    by transfer simp
qed

end

text \<open>Now, we move on to showing that shares form a distributive lattice.\<close>

lemma tree_glb_l1:
    fixes x z :: \<open>tree\<close>
  assumes \<open>x \<le> z\<close>
    shows \<open>tree_glb x y \<le> z\<close>
using assms by (meson order.trans tree_glb_below1)

lemma tree_glb_l2:
  assumes \<open>y \<le> z\<close>
    shows \<open>tree_glb x y \<le> z\<close>
using assms by (meson order.trans tree_glb_below2)

lemma tree_distrib1:
  fixes x y z :: \<open>tree\<close>
  shows \<open>tree_lub x (tree_glb y z) \<le> tree_glb (tree_lub x y) (tree_lub x z)\<close>
by (metis order.trans tree_glb_below1 tree_glb_below2 tree_glb_greatest tree_lub_above1
  tree_lub_above2 tree_lub_least)

lemma tree_glb_node_node_l:
  assumes \<open>tree_glb (Node a b) (Node x y) \<le> q\<close>
    shows \<open>tree_glb (node a b) (node x y) \<le> q\<close>
using assms by (meson dual_order.trans tree_glb_below1 tree_glb_below2 tree_glb_greatest
  tree_le_node2)

lemma tree_lub_Node_node_r:
  assumes \<open>q \<le> tree_lub (Node a b) (Node x y)\<close>
    shows \<open>q \<le> tree_lub (Node a b) (node x y)\<close>
using assms by (meson order.trans tree_le_node1 tree_lub_above1 tree_lub_above2 tree_lub_least)

lemma tree_lub_congr:
  assumes \<open>a \<le> x\<close>
      and \<open>b \<le> y\<close>
    shows \<open>tree_lub a b \<le> tree_lub x y\<close>
using assms by (meson order.trans tree_lub_above1 tree_lub_above2 tree_lub_least)

lemma tree_distrib2:
  shows \<open>tree_glb (tree_lub x y) (tree_lub x z) \<le> tree_lub x (tree_glb y z)\<close> (is \<open>?goal x y z\<close>)
proof (induction x arbitrary: y z rule: tree_deep_induct)
  case (Node a b)
  { \<comment> \<open>Focus exclusively on the Node-Node-Node case\<close>
    fix c d e f
    assume \<open>y = Node c d\<close> and \<open>z = Node e f\<close>
    with Node.IH have \<open>?goal (Node a b) y z\<close>
      by (auto simp add: tree_glb_node_node_l tree_lub_Node_node_r)
  }
  then show \<open>?goal (Node a b) y z\<close>
    \<comment> \<open>Now automation can figure out the other Leaf cases\<close>
    by (metis tree_bot_least tree_deep_exhaust tree_glb_greatest tree_glb_l1 tree_glb_l2
              order.refl tree_lub_congr tree_top_greatest)
qed auto

lemma tree_distrib:
  shows \<open>tree_glb (tree_lub x y) (tree_lub x z) \<simeq> tree_lub x (tree_glb y z)\<close>
by (simp add: tree_eq_def tree_distrib1 tree_distrib2)

instantiation share :: distrib_lattice
begin

instance
proof
   fix x y z :: \<open>share\<close>
  show \<open>sup x (inf y z) = inf (sup x y) (sup x z)\<close>
    by transfer (metis tree_distrib tree_equiv_canonical_equal tree_glb_canonical
      tree_lub_canonical)
qed

end

text \<open>Now, we show the properties necessary of the Boolean complement to be able to demonstrat that
shares form a Boolean algebra.\<close>

instantiation share :: \<open>boolean_algebra\<close>
begin

lift_definition uminus_share :: \<open>share \<Rightarrow> share\<close> is
  \<open>tree_comp\<close>
by auto

lift_definition minus_share :: \<open>share \<Rightarrow> share \<Rightarrow> share\<close> is
  \<open>\<lambda>x y. tree_glb x (tree_comp y)\<close>
by auto

lemma tree_glb_comp:
  shows \<open>tree_glb x (tree_comp x) = Leaf False\<close>
by (induction x rule: tree_deep_induct) auto

lemma tree_lub_comp:
  shows \<open>tree_lub x (tree_comp x) = Leaf True\<close>
by (induction x rule: tree_deep_induct) auto

instance
proof
  fix x :: \<open>share\<close>
  show \<open>inf x (- x) = bot\<close>
    by transfer (simp add: tree_glb_comp)
next
  fix x :: \<open>share\<close>
  show \<open>sup x (- x) = top\<close>
    by transfer (simp add: tree_lub_comp)
next
  fix x y :: \<open>share\<close>
  show \<open>x - y = inf x (- y)\<close>
    by transfer force
qed

end

subsection \<open>Share relativization\<close>

fun tree_relativ :: \<open>tree \<Rightarrow> tree \<Rightarrow> tree\<close> where
  \<open>tree_relativ Top x = x\<close> |
  \<open>tree_relativ Bot x = Bot\<close> |
  \<open>tree_relativ (Node l r) x = node (tree_relativ l x) (tree_relativ r x)\<close>

fun_cases tree_relativ_LeafE: \<open>tree_relativ a x = Leaf b\<close>
fun_cases tree_relativ_NodeNodeE: \<open>tree_relativ x (Node a b) = Node c d\<close>

lemma tree_relativ_NodeLeafE':
  assumes \<open>tree_relativ a (Node x y) = Leaf b\<close>
      and \<open>a \<le> Bot \<Longrightarrow> b = False \<Longrightarrow> P\<close>
    shows \<open>P\<close>
using assms by (induction a arbitrary: x y rule: tree_deep_induct; simp) (metis (full_types)
  node_LeafE)

lemma tree_relativ_NodeLeafE:
  assumes \<open>tree_relativ a (Node x y) = Leaf b\<close>
      and \<open>canonical a\<close>
      and \<open>a = Leaf False \<Longrightarrow> b = False \<Longrightarrow> P\<close>
    shows \<open>P\<close>
using assms by (auto elim: tree_relativ_NodeLeafE' simp add: tree_equiv_canonical_equal tree_eq_def)

lemma tree_relativ_canonical [simp]:
  assumes \<open>canonical x\<close>
      and \<open>canonical y\<close>
    shows \<open>canonical (tree_relativ x y)\<close>
using assms by (induction x y rule: tree_relativ.induct; simp) (auto elim!: canonical_NodeE)

lemma tree_eq_lub_node_l:
  assumes \<open>tree_lub (Node a b) (Node x y) \<simeq> q\<close>
    shows \<open>tree_lub (node a b) (node x y) \<simeq> q\<close>
using assms by (meson order.trans tree_eq_def tree_le_node1 tree_le_node2 tree_lub_above1
  tree_lub_above2 tree_lub_least)

lemma tree_eq_glb_node_l:
  assumes \<open>tree_glb (Node a b) (Node x y) \<simeq> q\<close>
    shows \<open>tree_glb (node a b) (node x y) \<simeq> q\<close>
using assms by (meson order.trans tree_eq_def tree_glb_below1 tree_glb_below2 tree_glb_greatest
  tree_glb_node_node_l tree_le_node_r)

lemma tree_relativ_top:
  shows \<open>tree_relativ x Top \<simeq> x\<close>
by (induction x rule: tree_deep_induct) (auto simp add: tree_eq_def)

corollary tree_relativ_top':
  assumes \<open>canonical x\<close>
    shows \<open>tree_relativ x Top = x\<close>
using assms by (auto intro: tree_equiv_canonical_equal simp add: tree_relativ_top)

lemma tree_relativ_bot:
  shows \<open>tree_relativ x Bot = Bot\<close>
by (induction x rule: tree_deep_induct, auto)

corollary tree_relativ_bot':
  shows \<open>tree_relativ x Bot \<le> Bot\<close>
by (clarsimp simp add: tree_relativ_bot)

lemma tree_relativ_lub:
  shows \<open>tree_lub (tree_relativ x y) (tree_relativ x z) \<simeq> tree_relativ x (tree_lub y z)\<close>
by (induction x rule: tree_deep_induct) (auto simp add: tree_eq_Node_node tree_eq_lub_node_l
    tree_eq_node_l intro: reflpD [OF tree_eq_refl])

lemma tree_relativ_glb:
  shows \<open>tree_glb (tree_relativ x y) (tree_relativ x z) \<simeq> tree_relativ x (tree_glb y z)\<close>
by (induction x rule: tree_deep_induct) (auto simp add: tree_eq_Node_node tree_eq_glb_node_l
    tree_eq_node_l intro: reflpD [OF tree_eq_refl])

lemma tree_le_Node_l:
  assumes \<open>a \<le> x\<close>
      and \<open>b \<le> y\<close>
      and \<open>Node x y \<le> z\<close>
    shows \<open>Node a b \<le> z\<close>
using assms by (meson less_eq_tree.simps(4) order.trans)

lemma tree_eq_Node_l:
  assumes \<open>a \<simeq> x\<close>
      and \<open>b \<simeq> y\<close>
      and \<open>Node x y \<simeq> z\<close>
    shows \<open>Node a b \<simeq> z\<close>
using assms by (meson order.trans tree_eq_def tree_le_Node_l tree_le_node1 tree_le_node2)

lemma tree_eq_collapse:
  shows \<open>Node (Leaf b) (Leaf b) \<simeq> Leaf b\<close>
unfolding tree_eq_def by simp

lemma tree_relativ_assoc_aux1:
  assumes \<open>canonical (Node a b)\<close>
    shows \<open>Node (tree_relativ a y) (tree_relativ b y) \<simeq> tree_relativ (node a b) y\<close>
using assms by (auto simp add: tree_eq_def elim!: canonical_NodeE intro: node.cases[of \<open>(a,b)\<close>]
  split: tree.splits)

lemma tree_relativ_assoc:
  assumes \<open>canonical x\<close>
      and \<open>canonical y\<close>
    shows \<open>tree_relativ x (tree_relativ y z) \<simeq> tree_relativ (tree_relativ x y) z\<close>
using assms proof(induction x arbitrary: y z rule: tree_deep_induct)
  case (Node a b y z)
  then have canon: \<open>canonical a\<close> \<open>canonical b\<close>
    by (auto elim: canonical_NodeE)
  moreover 
  obtain a: \<open>tree_relativ a (tree_relativ y z) \<simeq> tree_relativ (tree_relativ a y) z\<close>
     and b: \<open>tree_relativ b (tree_relativ y z) \<simeq> tree_relativ (tree_relativ b y) z\<close>
    using canon Node by blast
  have \<open>\<not> (a = Leaf False \<and> b = Leaf False)\<close>
    using Node.prems canonical_Node_LeafE by blast
  then have *: \<open>canonical (Node (tree_relativ a (Node c d)) (tree_relativ b (Node c d)))\<close>
    if \<open>canonical (Node c d)\<close>
    for c d
    using that by (intro canonical_Node) (auto simp: canon split: tree.splits elim!: tree_relativ_NodeLeafE)
  have \<open>Node (tree_relativ (tree_relativ a y) z) (tree_relativ (tree_relativ b y) z) \<simeq>
       tree_relativ (node (tree_relativ a y) (tree_relativ b y)) z\<close>
  proof (cases y rule: tree_deep_exhaust)
    case Bot
    then show ?thesis
      using tree_eq_collapse tree_relativ_bot by auto
  next
    case Top
     then show ?thesis
       by (simp add: Node.prems(1) canon tree_relativ_assoc_aux1 tree_relativ_top')
   next
     case Node
     then show ?thesis
       using * Node.prems(2) tree_relativ_assoc_aux1 by blast 
   qed
  ultimately show ?case
    using a b tree_eq_Node_l by force
qed (auto simp add: tree_eq_def)

lemma tree_le_node_nodeE:
  assumes \<open>node a b \<le> node x y\<close>
      and \<open>a \<le> x \<Longrightarrow> b \<le> y \<Longrightarrow> P\<close>
    shows \<open>P\<close>
  by (metis assms less_eq_tree.simps(4) order.trans tree_le_node1 tree_le_node2)

lemma tree_relativ_inj1_le:
  assumes \<open>canonical x\<close>
      and \<open>x \<noteq> Bot\<close>
      and \<open>tree_relativ x y \<le> tree_relativ x z\<close>
    shows \<open>y \<le> z\<close>
using assms by (induction x arbitrary: y z; simp) (force elim!: canonical_NodeE tree_le_node_nodeE)

lemma tree_relativ_inj1:
  assumes \<open>canonical x\<close>
      and \<open>x \<noteq> Bot\<close>
      and \<open>tree_relativ x y \<simeq> tree_relativ x z\<close>
    shows \<open>y \<simeq> z\<close>
using assms by (simp add: tree_eq_def tree_relativ_inj1_le)

lemma tree_eq_node_rE:
  assumes \<open>x \<simeq> node a b\<close>
      and \<open>x \<simeq> Node a b \<Longrightarrow> P\<close>
    shows \<open>P\<close>
using assms by (meson order.trans tree_eq_def tree_le_node1 tree_le_node2)

corollary tree_eq_node_lE:
  assumes \<open>node a b \<simeq> x\<close>
      and \<open>Node a b \<simeq> x \<Longrightarrow> P\<close>
    shows \<open>P\<close>
using assms by (meson tree_eq_def tree_eq_node_rE)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma node_leaf_Node:
  assumes \<open>x \<noteq> Leaf b\<close>
    shows \<open>node (Leaf b) x = Node (Leaf b) x\<close>
using assms by (cases x rule: tree_deep_exhaust) auto

lemma tree_relativ_size:
  assumes \<open>canonical a\<close>
      and \<open>size a > 0\<close>
      and \<open>x \<noteq> Bot\<close>
    shows \<open>size (tree_relativ a x) \<ge> size a + size x\<close>
using assms proof (induct a rule: tree_deep_induct)
  case (Node a b)
  {
       fix l1 l2
    assume \<open>tree_relativ a x = Leaf l1\<close>
    with Node have ?case
      by (cases \<open>tree_relativ b x\<close>; auto elim!: canonical_NodeE tree_relativ_LeafE split: tree.splits)
  } moreover {
       fix n1 n2 n3 n4
    assume \<open>tree_relativ a x = Node n1 n2\<close>
    with Node have ?case
      by (cases a rule: tree_deep_exhaust; cases b)
         (auto split: tree.splits bool.split elim: canonical_NodeE)
  }
  ultimately show ?case
    by (cases \<open>tree_relativ a x\<close>) blast
qed auto

lemma tree_relativ_cancel_l:
  assumes \<open>canonical a\<close>
      and \<open>x \<noteq> Bot\<close>
      and \<open>x = tree_relativ a x\<close>
    shows \<open>Top \<le> a\<close>
using assms proof (cases a rule: tree_deep_exhaust)
  case Bot
  with assms show ?thesis by auto
next
  case Top
  then show ?thesis
    by simp
next
  case (Node a b)
  with assms show ?thesis
    by (clarsimp, metis tree_relativ_size add_gr_0 add_le_same_cancel2 leD lessI tree.size(4))
qed

lemma tree_relativ_inj2_le:
  assumes \<open>canonical x\<close>
      and \<open>canonical y\<close>
      and \<open>canonical z\<close>
      and \<open>x \<noteq> Bot\<close>
      and \<open>tree_relativ y x \<simeq> tree_relativ z x\<close>
    shows \<open>y \<le> z\<close>
using assms proof (induction y arbitrary: z rule: tree_deep_induct)
  case Bot
  then show ?case
    using tree_bot_least by blast
next
  case Top
  then show ?case
    by (simp add: tree_equiv_canonical_equal tree_relativ_cancel_l)
next
  case N: (Node a b z)
  then obtain a: \<open>canonical a\<close> and b: \<open>canonical b\<close>
    by (meson canonical_NodeE)
  have [simp]: \<open>z \<noteq> Bot\<close>
    using N.prems assms
    by (metis tree.distinct(1) tree_equiv_canonical_equal tree_relativ.simps(2) tree_relativ_bot tree_relativ_inj1)
  show ?case
  proof (cases z rule: tree_deep_exhaust)
    case (Node c d)
    then obtain  \<open>canonical c\<close> and \<open>canonical d\<close>
      using \<open>canonical z\<close> canonical_NodeE by blast
    then obtain \<open>tree_relativ a x \<simeq> tree_relativ c x\<close> \<open>tree_relativ b x \<simeq> tree_relativ d x\<close>
      by (metis N.prems(5) Node tree_eq_def tree_le_node_nodeE tree_relativ.simps(3))
    then show ?thesis
      by (simp add: a b N.IH Node \<open>canonical c\<close> \<open>canonical d\<close> assms(1,4))
  qed auto
qed 

lemma tree_relativ_inj2:
  assumes \<open>canonical x\<close>
      and \<open>canonical y\<close>
      and \<open>canonical z\<close>
      and \<open>x \<noteq> Bot\<close>
      and \<open>tree_relativ y x \<simeq> tree_relativ z x\<close>
    shows \<open>y \<simeq> z\<close>
using assms tree_relativ_inj2_le unfolding tree_eq_def by blast

lift_definition share_relativ :: \<open>share \<Rightarrow> share \<Rightarrow> share\<close> (infixr \<open>\<bowtie>\<close> 80) is \<open>tree_relativ\<close>
  by simp

text \<open>Shares form a separation algebra:\<close>

instantiation share :: sepalg
begin

(*<*)
context
  includes lattice_syntax
begin
(*>*)

definition disjoint_share :: \<open>share \<Rightarrow> share \<Rightarrow> bool\<close> where
  \<open>disjoint_share x y \<equiv> x \<sqinter> y = \<bottom>\<close>

definition plus_share :: \<open>share \<Rightarrow> share \<Rightarrow> share\<close> where
  \<open>plus_share x y \<equiv> x \<squnion> y\<close>

definition zero_share :: \<open>share\<close> where
  \<open>zero_share = \<bottom>\<close>

(*<*)
end
(*>*)

instance
proof
   fix x :: \<open>share\<close>
  show \<open>x \<sharp> 0\<close>
    by (simp add: disjoint_share_def zero_share_def)
next
   fix x y :: \<open>share\<close>
  show \<open>x \<sharp> y \<longleftrightarrow> y \<sharp> x\<close>
    by (simp add: disjoint_share_def inf_commute)
next
     fix x :: \<open>share\<close>
  assume \<open>x \<sharp> x\<close>
  from this show \<open>x = 0\<close>
    by (simp add: disjoint_share_def zero_share_def)
next
   fix x :: \<open>share\<close>
  show \<open>x + 0 = x\<close>
    by (simp add: plus_share_def zero_share_def)
next
     fix x y :: \<open>share\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>x + y = y + x\<close>
    by (simp add: plus_share_def sup_commute)
next
     fix x y z :: \<open>share\<close>
  assume \<open>x \<sharp> y\<close>
     and \<open>y \<sharp> z\<close>
     and \<open>x \<sharp> z\<close>
  from this show \<open>x + (y + z) = x + y + z\<close>
    by (simp add: inf_sup_aci plus_share_def sup_commute)
next
     fix x y z :: \<open>share\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x \<sharp> y\<close>
    by (simp add: disjoint_share_def inf_shunt plus_share_def)
next
     fix x y z :: \<open>share\<close>
  assume \<open>x \<sharp> y + z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x + y \<sharp> z\<close>
    by (simp add: disjoint_share_def inf_shunt plus_share_def)
qed

end

instantiation share :: strong_sepalg
begin

instance
proof
     fix x y z :: \<open>share\<close>
  assume \<open>x \<sharp> y\<close>
  from this show \<open>(x + y) \<sharp> z \<longleftrightarrow> y \<sharp> z \<and> x \<sharp> z\<close>
    by (clarsimp simp add: disjoint_share_def plus_share_def) (metis bot_eq_sup_iff inf_commute
      inf_sup_distrib1)
qed

end

instantiation share :: cancellative_sepalg
begin

instance
proof
     fix x y z :: \<open>share\<close>
  assume \<open>x + z = y + z\<close>
     and \<open>x \<sharp> z\<close>
     and \<open>y \<sharp> z\<close>
  from this show \<open>x = y\<close>
    by (clarsimp simp add: disjoint_share_def plus_share_def) (metis inf_commute inf_sup_absorb
      inf_sup_distrib2)
qed

end

(*<*)
context
  includes lattice_syntax
begin
(*>*)

lemma shares_nontrivial [simp]:
  shows \<open>\<bottom> < (\<top>::share)\<close>
using bot.not_eq_extremum bot_share.rep_eq top_share.rep_eq by fastforce

lemma share_relativ_top:
  shows \<open>x \<bowtie> \<top> = x\<close>
    and \<open>\<top> \<bowtie> x = x\<close>
using tree_relativ_top tree_equiv_canonical_equal unfolding tree_eq_def by (transfer; simp)+

lemma share_relativ_bot:
  shows \<open>x \<bowtie> \<bottom> = \<bottom>\<close>
    and \<open>\<bottom> \<bowtie> x = \<bottom>\<close>
using tree_relativ_bot tree_equiv_canonical_equal unfolding tree_eq_def by (transfer, simp)+

lemma share_relativ_lub:
  shows \<open>x \<bowtie> (y \<squnion> z) = x \<bowtie> y \<squnion> x \<bowtie> z\<close>
using tree_relativ_lub tree_equiv_canonical_equal unfolding tree_eq_def by transfer auto

lemma share_relativ_glb:
  shows \<open>x \<bowtie> (y \<sqinter> z) = x \<bowtie> y \<sqinter> x \<bowtie> z\<close>
using tree_relativ_glb tree_equiv_canonical_equal unfolding tree_eq_def by transfer auto

lemma share_relativ_assoc:
  shows \<open>(x \<bowtie> y) \<bowtie> z = x \<bowtie> (y \<bowtie> z)\<close>
by transfer (metis tree_equiv_canonical_equal tree_relativ_assoc tree_relativ_canonical)

lemma share_relativ_inj1:
  assumes \<open>x \<noteq> \<bottom>\<close>
      and \<open>x \<bowtie> y = x \<bowtie> z\<close>
    shows \<open>y = z\<close>
using assms by transfer (metis canonical_Leaf tree_equiv_canonical_equal tree_relativ.simps
  tree_relativ_assoc tree_relativ_inj1)

lemma share_relativ_inj2:
  assumes \<open>x \<noteq> \<bottom>\<close>
      and \<open>y \<bowtie> x = z \<bowtie> x\<close>
    shows \<open>y = z\<close>
using assms by transfer (metis canonical_Leaf tree_equiv_canonical_equal tree_relativ.simps
  tree_relativ_assoc tree_relativ_inj2)

lemma share_relativ_disjoint1:
  assumes \<open>x \<sharp> y\<close>
    shows \<open>a \<bowtie> x \<sharp> a \<bowtie> y\<close>
using assms by (auto simp add: disjoint_share_def share_relativ_bot share_relativ_glb[symmetric])

lemma share_relativ_disjoint2:
  assumes \<open>a \<sharp> b\<close>
    shows \<open>a \<bowtie> x \<sharp> b \<bowtie> y\<close>
using assms by (clarsimp simp add: disjoint_share_def) (metis inf_assoc inf_bot_left inf_commute
  inf_top.right_neutral share_relativ_glb share_relativ_top(1))

(*<*)
end
(*>*)

subsection \<open>Nonempty shares\<close>

text\<open>Usually, we prefer to work with the set of all shares, which has nice algebraic structure.
However, it is sometimes useful to work with the subset "nonempty" shares, which excludes
the least element.\<close>

typedef nonempty_share = \<open>{ sh::share. bot < sh }\<close>
  using shares_nontrivial by blast

declare Rep_nonempty_share_inverse [simp]

(*<*)
setup_lifting type_definition_nonempty_share
(*>*)

instantiation nonempty_share :: equal
begin

lift_definition equal_nonempty_share :: \<open>nonempty_share \<Rightarrow> nonempty_share \<Rightarrow> bool\<close>
  is \<open>\<lambda>(s::share) t. s = t\<close> .

instance
proof
   fix x y :: \<open>nonempty_share\<close>
  show \<open>equal_class.equal x y \<longleftrightarrow> (x = y)\<close>
    by transfer force
qed

end

instantiation nonempty_share :: order_top
begin

lift_definition top_nonempty_share :: \<open>nonempty_share\<close> is \<open>top\<close>
  by simp

lift_definition less_nonempty_share :: \<open>nonempty_share \<Rightarrow> nonempty_share \<Rightarrow> bool\<close> is
  \<open>\<lambda>x y. x < y\<close> .

lift_definition less_eq_nonempty_share :: \<open>nonempty_share \<Rightarrow> nonempty_share \<Rightarrow> bool\<close> is
  \<open>\<lambda>x y. x \<le> y\<close> .

instance
proof
   fix x y :: \<open>nonempty_share\<close>
  show \<open>(x < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
    by transfer force
next
   fix x :: \<open>nonempty_share\<close>
  show \<open>x \<le> x\<close>
    by transfer force
next
     fix x y z :: \<open>nonempty_share\<close>
  assume \<open>x \<le> y\<close>
     and \<open>y \<le> z\<close>
  from this show \<open>x \<le> z\<close>
    by transfer force
next
     fix x y :: \<open>nonempty_share\<close>
  assume \<open>x \<le> y\<close>
     and \<open>y \<le> x\<close>
  from this show \<open>x = y\<close>
    by transfer force
next
   fix x :: \<open>nonempty_share\<close>
  show \<open>x \<le> top\<close>
    by transfer force
qed

end

instantiation nonempty_share :: semigroup_add
begin

(*<*)
context
  includes lattice_syntax
begin
(*>*)

lift_definition plus_nonempty_share :: \<open>nonempty_share \<Rightarrow> nonempty_share \<Rightarrow> nonempty_share\<close> is
   \<open>\<lambda>x y. x \<squnion> y\<close>
using less_supI1 by blast

instance
  by standard (transfer, simp add: sup_assoc)

(*<*)
end
(*>*)

end

subsection \<open>Share splitting\<close>

(*<*)
context
includes lattice_syntax
begin
(*>*)

lift_definition Left :: \<open>share\<close> is \<open>Node Top Bot\<close>
  by simp

lift_definition Right :: \<open>share\<close> is \<open>Node Bot Top\<close>
  by simp

lemma Left_Right_disjoint:
  shows \<open>Left \<sharp> Right\<close>
unfolding disjoint_share_def by (transfer; simp)

lemma Left_Right_partition:
  shows \<open>Left \<squnion> Right = \<top>\<close>
by transfer auto

definition split_left :: \<open>share \<Rightarrow> share\<close> where
  \<open>split_left x \<equiv> x \<bowtie> Left\<close>

definition split_right :: \<open>share \<Rightarrow> share\<close> where
  \<open>split_right x \<equiv> x \<bowtie> Right\<close>

lemma split_share_disjoint:
  shows \<open>split_left x \<sharp> split_right x\<close>
  by (simp add: Left_Right_disjoint share_relativ_disjoint1 split_left_def split_right_def)

lemma plus_Left_Right [simp]:
  shows \<open>Left + Right = \<top>\<close>
by (simp add: Left_Right_partition plus_share_def)

lemma Left_nonempty [simp]:
  shows \<open>0 < Left\<close>
by (clarsimp simp add: zero_share_def) (transfer, clarsimp simp add: less_le_not_le)

lemma Right_nonempty [simp]:
  shows \<open>0 < Right\<close>
by (clarsimp simp add: zero_share_def) (transfer, clarsimp simp add: less_le_not_le)

lemma split_share_partition:
  shows \<open>split_left x \<squnion> split_right x = x\<close>
  by (metis Left_Right_partition share_relativ_lub share_relativ_top(1) split_left_def split_right_def)

lemma split_left_nonempty:
  assumes \<open>x \<noteq> \<bottom>\<close>
    shows \<open>split_left x \<noteq> \<bottom>\<close>
using assms by (clarsimp simp add: split_left_def) (transfer, blast elim: tree_relativ_NodeLeafE)

lemma split_right_nonempty:
  assumes \<open>x \<noteq> \<bottom>\<close>
    shows \<open>split_right x \<noteq> \<bottom>\<close>
using assms by (clarsimp simp add: split_right_def) (transfer, blast elim: tree_relativ_NodeLeafE)

subsection \<open>Finite set shares\<close>

text
\<open>For each natural number, we can associate a particular share,
and we can extend this association to finite sets of natural numbers.

The shares for distinct numbers are disjoint, and the lattice structure
on finite sets extends directly to the lattice structure on shares.\<close>

fun tree_of_nat :: \<open>nat \<Rightarrow> tree\<close> where
  \<open>tree_of_nat 0 = Node Top Bot\<close> |
  \<open>tree_of_nat (Suc n) = Node Bot (tree_of_nat n)\<close>

fun_cases tree_of_nat_LeafE: \<open>tree_of_nat n = Leaf b\<close>

lemma tree_of_nat_canonical:
  shows \<open>canonical (tree_of_nat n)\<close>
by (induction n) (auto split: tree.splits intro!: canonical_Node canonical_Leaf elim:
    tree_of_nat_LeafE)

lemma tree_of_nat_disjoint:
  assumes \<open>n \<noteq> m\<close>
    shows \<open>tree_glb (tree_of_nat n) (tree_of_nat m) \<le> Bot\<close>
using assms by (induction n arbitrary: m) (case_tac m; clarsimp simp add: tree_glb_below2 split!:
  nat.splits)+

lemma tree_of_nat_nonempty:
  shows \<open>tree_of_nat n \<noteq> Bot\<close>
by (induction n) auto

lift_definition share_of_nat :: \<open>nat \<Rightarrow> share\<close> is
  \<open>tree_of_nat\<close>
by (rule tree_of_nat_canonical)

lemma share_of_nat_disjoint:
  assumes \<open>n \<noteq> m\<close>
    shows \<open>share_of_nat n \<sqinter> share_of_nat m = \<bottom>\<close>
using assms by (intro antisym) (transfer, auto simp add: tree_bot_least tree_of_nat_disjoint)

definition share_of_natset :: \<open>nat set \<Rightarrow> share\<close> where
  \<open>share_of_natset X \<equiv> Finite_Set.fold (\<lambda>n s. share_of_nat n \<squnion> s) \<bottom> X\<close>

interpretation nat_shares: comp_fun_idem_on \<open>UNIV :: nat set\<close> \<open>\<lambda> n s. share_of_nat n \<squnion> s\<close>
proof
   fix x y
  show \<open>(\<squnion>) (share_of_nat y) \<circ> (\<squnion>) (share_of_nat x) = (\<squnion>) (share_of_nat x) \<circ> (\<squnion>) (share_of_nat y)\<close>
    by (auto simp add: sup_left_commute)
next
   fix x
  show \<open>(\<squnion>) (share_of_nat x) \<circ> (\<squnion>) (share_of_nat x) = (\<squnion>) (share_of_nat x)\<close>
    by (auto simp add: sup_left_commute)
qed

lemma share_of_nat_nonempty:
  shows \<open>share_of_nat n \<noteq> \<bottom>\<close>
by transfer (simp add: tree_of_nat_nonempty)

lemma share_of_natset_empty:
  shows \<open>share_of_natset {} = \<bottom>\<close>
by (simp add: share_of_natset_def)

lemma share_of_natset_insert:
  assumes \<open>finite X\<close>
    shows \<open>share_of_natset (insert n X) = share_of_nat n \<squnion> share_of_natset X\<close>
using assms by (simp add: share_of_natset_def)

lemma share_of_natset_single:
  shows \<open>share_of_natset {x} = share_of_nat x\<close>
by (simp add: share_of_natset_empty share_of_natset_insert)

lemma share_of_nat_member:
  assumes \<open>finite Y\<close>
      and \<open>a \<in> Y\<close>
    shows \<open>share_of_nat a \<le> share_of_natset Y\<close>
using assms by (simp add: share_of_natset_def nat_shares.fold_rec[of Y a])

lemma share_of_nat_nonmember:
  assumes \<open>finite Y\<close>
      and \<open>a \<notin> Y\<close>
    shows \<open>share_of_nat a \<sqinter> share_of_natset Y = \<bottom>\<close>
using assms by (induction Y rule: finite.induct) (auto simp add: share_of_natset_empty
  share_of_natset_insert inf_sup_distrib1 share_of_nat_disjoint)

lemma share_of_natset_subset:
  assumes \<open>finite Y\<close>
      and \<open>X \<subseteq> Y\<close>
    shows \<open>share_of_natset X \<le> share_of_natset Y\<close>
proof -
  from assms have \<open>finite X\<close>
    by (simp add: finite_subset)
  from this and assms show ?thesis
    by (induction X rule: finite.induct) (auto simp add: share_of_natset_empty
      share_of_natset_insert share_of_nat_member)
qed

lemma share_of_natset_union:
  assumes \<open>finite X\<close>
      and \<open>finite Y\<close>
    shows \<open>share_of_natset (X \<union> Y) = share_of_natset X \<squnion> share_of_natset Y\<close>
using assms by (induction X rule: finite.induct) (auto simp add: share_of_natset_empty
  share_of_natset_insert sup_assoc)

lemma share_of_natset_intersection:
  assumes \<open>finite X\<close>
      and \<open>finite Y\<close>
    shows \<open>share_of_natset (X \<inter> Y) = share_of_natset X \<sqinter> share_of_natset Y\<close>
using assms proof (induction X rule: finite.induct)
  case emptyI
  then show ?case  by (simp add: share_of_natset_empty)
next
  case (insertI A a)
  show ?case
  proof (cases \<open>a \<in> Y\<close>)
    case True
    with insertI share_of_nat_member 
    have \<open>share_of_nat a \<le> share_of_natset Y\<close>
      by blast
    then show ?thesis
      by (simp add: True insertI le_iff_sup share_of_natset_insert sup_inf_distrib1)
  next
    case False
    with insertI show ?thesis
      by (simp add: inf_commute inf_sup_distrib1 share_of_nat_nonmember share_of_natset_insert)
  qed
qed

lemma share_of_natset_subtract:
  assumes \<open>finite X\<close>
      and \<open>finite Y\<close>
    shows \<open>share_of_natset (X - Y) = share_of_natset X - share_of_natset Y\<close>
using assms proof (induction X rule: finite.induct)
  case emptyI
  then show ?case
    using share_of_natset_empty by auto
next
  case (insertI A a)
  show ?case
  proof (cases \<open>a \<in> Y\<close>)
    case True
    then have \<dagger>: \<open>share_of_nat a \<le> share_of_natset Y\<close>
      by (simp add: insertI.prems share_of_nat_member)
    have \<open>share_of_natset (insert a A - Y) = share_of_natset A - share_of_natset Y\<close>
      using True by (simp add: insertI)
    also have \<open>\<dots> = (share_of_nat a \<squnion> share_of_natset A) - (share_of_nat a \<squnion> share_of_natset Y)\<close>
     by (metis (no_types) diff_eq diff_shunt \<dagger> inf_sup_distrib2 sup_absorb2 sup_bot_left)
    also have \<open>\<dots> = share_of_natset (insert a A) - share_of_natset (insert a Y)\<close>
      using insertI share_of_natset_insert by fastforce
    also have \<open>... = share_of_natset (insert a A) - share_of_natset Y\<close>
      by (simp add: True insert_absorb)
    finally show ?thesis .
  next
    case False
    then have \<open>share_of_natset (insert a A - Y) = share_of_nat a \<squnion> (share_of_natset A - share_of_natset Y)\<close>
      using insertI share_of_natset_def by (fastforce simp: insert_Diff_if)
    also have \<open>\<dots> = share_of_natset (insert a A) - share_of_natset Y\<close>
      using insertI False False diff_eq inf_shunt  le_iff_sup share_of_nat_nonmember share_of_natset_insert sup_inf_distrib1
    proof -
      have \<open>share_of_nat a \<le> - share_of_natset Y\<close>
        using False inf_shunt insertI.prems share_of_nat_nonmember by auto
      then show ?thesis
        by (simp add: diff_eq insertI.hyps le_iff_sup share_of_natset_insert sup_inf_distrib1)
    qed
    finally show ?thesis .
  qed
qed

lemma share_of_natset_incomplete:
  assumes \<open>finite X\<close>
    shows \<open>share_of_natset X \<noteq> \<top>\<close>
using assms by (metis ex_new_if_finite inf_top.right_neutral infinite_UNIV_char_0
  share_of_nat_nonempty share_of_nat_nonmember)

subsection \<open>Token factories\<close>

text
\<open>In a token counting scheme, we can model individual tokens as the shares
associated with some particular natural number, and the token counter they
come from are modeled using the complement of a share derived from a finite set.
The cardinality of that set indicates how many tokens are outstanding.

Given a token factory, we can always mint a fresh token, leaving us with a
token factory with one additional token outstanding.\<close>

definition is_token :: \<open>share \<Rightarrow> bool\<close> where
  \<open>is_token s \<equiv> \<exists>n. s = share_of_nat n\<close>

definition is_token_factory :: \<open>nat \<Rightarrow> share \<Rightarrow> bool\<close> where
  \<open>is_token_factory sz s \<equiv> \<exists>X. finite X \<and> s = -share_of_natset X \<and> sz = card X\<close>

lemma token_nonempty:
  assumes \<open>is_token t\<close>
    shows \<open>t \<noteq> \<bottom>\<close>
using assms share_of_nat_nonempty by (auto simp add: is_token_def)

lemma token_factory_nonempty:
  assumes \<open>is_token_factory sz f\<close>
    shows \<open>f \<noteq> \<bottom>\<close>
using assms by (clarsimp simp add: is_token_factory_def) (metis share_of_natset_incomplete
  boolean_algebra.compl_zero boolean_algebra_class.boolean_algebra.double_compl)

lemma token_factory_full:
  assumes \<open>is_token_factory 0 f\<close>
    shows \<open>f = \<top>\<close>
using assms share_of_natset_empty by (auto simp add: is_token_factory_def)

lemma factory_disjoint_nonzero:
  assumes \<open>is_token_factory sz f\<close>
      and \<open>x \<sharp> f\<close>
      and \<open>x \<noteq> \<bottom>\<close>
    shows \<open>sz > 0\<close>
  using assms card_gt_0_iff share_of_natset_empty 
  by (force simp add: is_token_factory_def disjoint_share_def)

lemma token_combine:
  assumes \<open>is_token t\<close>
      and \<open>is_token_factory sz f\<close>
      and \<open>t \<sharp> f\<close>
    shows \<open>is_token_factory (sz-1) (t \<squnion> f)\<close>
proof -
  obtain n X where n: \<open>t = share_of_nat n\<close> 
    and X: \<open>f = -share_of_natset X\<close> \<open>finite X\<close> \<open>sz = card X\<close>
    using assms is_token_def is_token_factory_def by blast
  then have \<open>t\<squnion>f = -share_of_natset (X-{n})\<close>
    by (metis boolean_algebra.de_Morgan_disj boolean_algebra_class.boolean_algebra.double_compl diff_eq finite.simps n share_of_natset_single
        share_of_natset_subtract sup.commute)
  moreover from assms n X have \<open>card (X-{n}) = card X-1\<close>
    by (metis disjoint_share_def One_nat_def card_Diff_singleton inf_absorb1 inf_shunt
      share_of_nat_nonempty share_of_nat_nonmember)
  ultimately show \<open>is_token_factory (sz-1) (t\<squnion>f)\<close>
    using X by (metis is_token_factory_def finite_Diff)
qed

lemma token_subtract:
  assumes \<open>is_token t\<close>
      and \<open>is_token_factory sz f\<close>
      and \<open>t \<le> f\<close>
    shows \<open>is_token_factory (sz+1) (f - t)\<close>
proof -
  obtain n X where n: \<open>t = share_of_nat n\<close> 
    and X: \<open>f = -share_of_natset X\<close> \<open>finite X\<close> \<open>sz = card X\<close>
    using assms is_token_def is_token_factory_def by blast
  have \<open>f-t = -share_of_natset (insert n X)\<close>
    using n X by (auto simp add: diff_eq inf_commute share_of_natset_insert)
  moreover from assms n X have \<open>card (insert n X) = card X+1\<close>
    by (metis Suc_eq_plus1 card_insert_if inf_shunt le_iff_inf share_of_nat_member share_of_nat_nonempty)
  ultimately show \<open>is_token_factory (sz+1) (f-t)\<close>
    using n X by (metis is_token_factory_def finite_insert)
qed

definition mint_token :: "share \<Rightarrow> share" where
  \<open>mint_token f \<equiv> share_of_nat (LEAST n. share_of_nat n \<le> f)\<close>

lemma token_factory_mintable:
  assumes \<open>is_token_factory sz f\<close>
    shows \<open>\<exists>n. share_of_nat n \<le> f\<close>
  by (metis assms ex_new_if_finite inf_shunt infinite_UNIV_nat is_token_factory_def share_of_nat_nonmember)

lemma mint_token_is_token:
  shows \<open>is_token (mint_token f)\<close>
  unfolding is_token_def mint_token_def by auto

lemma mint_token_subshare:
  assumes \<open>is_token_factory sz f\<close>
    shows \<open>mint_token f \<le> f\<close>
  by (metis LeastI_ex assms mint_token_def token_factory_mintable)

lemma mint_token_disjoint:
  shows \<open>(f - mint_token f) \<sharp> (mint_token f)\<close>
  by (simp add: disjoint_share_def diff_eq)

lemma mint_token_partitions:
  assumes \<open>is_token_factory sz f\<close>
  shows \<open>(f - mint_token f) \<squnion> mint_token f = f\<close>
  by (metis (no_types) assms diff_eq sup.commute sup_assoc inf_le1 le_iff_sup mint_token_subshare shunt2)

lemma mint_token_is_factory:
  assumes \<open>is_token_factory sz f\<close>
    shows \<open>is_token_factory (Suc sz) (f - mint_token f)\<close>
using assms mint_token_is_token mint_token_subshare token_subtract by auto

(*<*)
end

end
(*>*)
