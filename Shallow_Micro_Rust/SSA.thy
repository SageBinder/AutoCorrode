(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory SSA
  imports Core_Expression_Lemmas Bool_Type_Lemmas Rust_Iterator_Lemmas
          "HOL-Library.Rewrite"
begin
declare [[urust_conformance_check = true]]
(*>*)

subsection\<open>Converting expressions to SSA form\<close>

text\<open>This section shows that each expression of Core Micro Rust can be transformed into a form of
\<^emph>\<open>single static assignment\<close> (or SSA, henceforth) wherein every effectful computation (i.e., an
expression which may return early, for example) is localized within the binding of a \<^verbatim>\<open>let\<close>
expression.  As a result of this, when defining Hoare-style triples later, and when also defining
rules for the Weakest Precondition calculus, we only need to consider terms in this SSA form.  This
massively simplifies some of the rules as we need not consider an early return from the discriminant
expression in a conditional, for example.

Note below that we use a ``trick'' to ensure that simplification using these rules remains tightly
controlled.  Namely, we use the \<^verbatim>\<open>MICRO_RUST_SSA_CONTROL\<close> function, which is merely the identity
function, to ``mark'' exactly where we want SSAification to apply.\<close>

definition MICRO_RUST_SSA_CONTROL :: \<open>('a, 'b, 'c, 'd, 'e, 'f) expression \<Rightarrow> _\<close> where
  \<open>MICRO_RUST_SSA_CONTROL x \<equiv> x\<close>

text\<open>We want the SSA transformations to operate as closely to the syntactic level as possible.
In fact, we could express them entirely at the syntax level, but they would not be provably correct
this way, but rather part of the definition of the denotational semantics.

One possible way around this could be to define SSA at the level of the abstract syntax, and apply
it automatically while elaborating each parser command, proving in the background that the
resulting shallowly embedded expressions are indeed semantically equivalent. Since the correctness
proofs for the SSA transformations should be trivial, that should not require user intervention. In
other words, the SSA transformations would be proven to be correct on a case-by-case basis.

To not stray afar, though, we use a middle ground below: We refer to the abstract Micro Rust syntax
for the constructions to be simplified, but use HOL antiquotations for the arguments.\<close>

text\<open>At present, SSA rewrites happen bottom-up. In this case, the SSA control is strictly speaking
not needed on the RHS of an SSA rewrite rule. We keep it to allow falling back to the original top-down
application of SSA rules if necessary.\<close>

urust_expr [urust_abbrev = true] SSA_urust_site_1
  \<open> \<epsilon>\<open>f\<close>(\<epsilon>\<open>e\<close>) \<close>
  with_args f e

urust_expr [urust_abbrev = true] SSA_urust_site_2
  \<open> let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>; \<epsilon>\<open>f\<close>(x0) \<close>
  with_args e f

lemma ssa_transform_funcall1 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_1 f e) = SSA_urust_site_2 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_3
  \<open> \<epsilon>\<open>fn\<close>(\<epsilon>\<open>e\<close>,\<epsilon>\<open>f\<close>) \<close>
  with_args fn e f

urust_expr [urust_abbrev = true] SSA_urust_site_4
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    \<epsilon>\<open>fn\<close> (x0, x1)
  \<close>
  with_args e f fn

lemma ssa_transform_funcall2 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_3 fn e f) = SSA_urust_site_4 e f fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_5
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>) \<close>
  with_args fn e0 e1 e2

urust_expr [urust_abbrev = true] SSA_urust_site_6
  \<open>
    let v0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let v1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let v2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    \<epsilon>\<open>fn\<close>(v0,v1,v2)
  \<close>
  with_args e0 e1 e2 fn

lemma ssa_transform_funcall3 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_5 fn e0 e1 e2) =
    SSA_urust_site_6 e0 e1 e2 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_7
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>) \<close>
  with_args fn e0 e1 e2 e3

urust_expr [urust_abbrev = true] SSA_urust_site_8
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
    \<epsilon>\<open>fn\<close>(x0,x1,x2,x3)
  \<close>
  with_args e0 e1 e2 e3 fn

lemma ssa_transform_funcall4 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_7 fn e0 e1 e2 e3) =
    SSA_urust_site_8 e0 e1 e2 e3 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_9
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>) \<close>
  with_args fn e0 e1 e2 e3 e4

urust_expr [urust_abbrev = true] SSA_urust_site_10
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
    let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
    \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4)
  \<close>
  with_args e0 e1 e2 e3 e4 fn

lemma ssa_transform_funcall5 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_9 fn e0 e1 e2 e3 e4) =
    SSA_urust_site_10 e0 e1 e2 e3 e4 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_11
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>) \<close>
  with_args fn e0 e1 e2 e3 e4 e5

urust_expr [urust_abbrev = true] SSA_urust_site_12
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
    let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
    let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
    \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5)
  \<close>
  with_args e0 e1 e2 e3 e4 e5 fn

lemma ssa_transform_funcall6 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_11 fn e0 e1 e2 e3 e4 e5) =
    SSA_urust_site_12 e0 e1 e2 e3 e4 e5 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_13
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>) \<close>
  with_args fn e0 e1 e2 e3 e4 e5 e6

urust_expr [urust_abbrev = true] SSA_urust_site_14
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
    let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
    let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
    let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
    \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6)
  \<close>
  with_args e0 e1 e2 e3 e4 e5 e6 fn

lemma ssa_transform_funcall7 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_13 fn e0 e1 e2 e3 e4 e5 e6) =
    SSA_urust_site_14 e0 e1 e2 e3 e4 e5 e6 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_15
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>,\<epsilon>\<open>e7\<close>) \<close>
  with_args fn e0 e1 e2 e3 e4 e5 e6 e7

urust_expr [urust_abbrev = true] SSA_urust_site_16
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
    let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
    let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
    let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
    let x7 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e7\<close>;
    \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6,x7)
  \<close>
  with_args e0 e1 e2 e3 e4 e5 e6 e7 fn

lemma ssa_transform_funcall8 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_15 fn e0 e1 e2 e3 e4 e5 e6 e7) =
    SSA_urust_site_16 e0 e1 e2 e3 e4 e5 e6 e7 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_17
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>,\<epsilon>\<open>e7\<close>,\<epsilon>\<open>e8\<close>) \<close>
  with_args fn e0 e1 e2 e3 e4 e5 e6 e7 e8

urust_expr [urust_abbrev = true] SSA_urust_site_18
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
    let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
    let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
    let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
    let x7 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e7\<close>;
    let x8 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e8\<close>;
    \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6,x7,x8)
  \<close>
  with_args e0 e1 e2 e3 e4 e5 e6 e7 e8 fn

lemma ssa_transform_funcall9 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_17 fn e0 e1 e2 e3 e4 e5 e6 e7 e8) =
    SSA_urust_site_18 e0 e1 e2 e3 e4 e5 e6 e7 e8 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_19
  \<open> \<epsilon>\<open>fn\<close> (\<epsilon>\<open>e0\<close>,\<epsilon>\<open>e1\<close>,\<epsilon>\<open>e2\<close>,\<epsilon>\<open>e3\<close>,\<epsilon>\<open>e4\<close>,\<epsilon>\<open>e5\<close>,\<epsilon>\<open>e6\<close>,\<epsilon>\<open>e7\<close>,\<epsilon>\<open>e8\<close>,\<epsilon>\<open>e9\<close>) \<close>
  with_args fn e0 e1 e2 e3 e4 e5 e6 e7 e8 e9

urust_expr [urust_abbrev = true] SSA_urust_site_20
  \<open>
    let x0 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e0\<close>;
    let x1 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e1\<close>;
    let x2 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e2\<close>;
    let x3 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e3\<close>;
    let x4 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e4\<close>;
    let x5 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e5\<close>;
    let x6 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e6\<close>;
    let x7 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e7\<close>;
    let x8 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e8\<close>;
    let x9 = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e9\<close>;
    \<epsilon>\<open>fn\<close>(x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
  \<close>
  with_args e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 fn

lemma ssa_transform_funcall10 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_19 fn e0 e1 e2 e3 e4 e5 e6 e7 e8 e9) =
    SSA_urust_site_20 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 fn\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

text\<open>We hoist the expression to be returned out of the \<^verbatim>\<open>return\<close> expression, simplify it recursively
and bind it to a variable.  We then return that variable:\<close>
urust_expr [urust_abbrev = true] SSA_urust_site_21
  \<open> return \<epsilon>\<open>r\<close>; \<close>
  with_args r

urust_expr [urust_abbrev = true] SSA_urust_site_22
  \<open> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL r\<close>; return x; \<close>
  with_args r

lemma ssa_transform_return [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_21 r) = SSA_urust_site_22 r\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def return_func_def micro_rust_simps)

lemma ssa_transform_bind2 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind2 exp e f) =
            (let x0 = MICRO_RUST_SSA_CONTROL e;
             let x1 = MICRO_RUST_SSA_CONTROL f;
               (bind2 exp (\<up>x0) (\<up>x1)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind3 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind3 exp x0 x1 x2) =
            (let v0 = MICRO_RUST_SSA_CONTROL x0;
             let v1 = MICRO_RUST_SSA_CONTROL x1;
             let v2 = MICRO_RUST_SSA_CONTROL x2;
                (bind3 exp (\<up>v0) (\<up>v1) (\<up>v2)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind4 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind4 exp x0 x1 x2 x3) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
               (bind4 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind5 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind5 exp x0 x1 x2 x3 x4) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
               (bind5 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind6 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind6 exp x0 x1 x2 x3 x4 x5) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
             let x5 = MICRO_RUST_SSA_CONTROL x5;
               (bind6 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4) (\<up>x5)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind7 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind7 exp x0 x1 x2 x3 x4 x5 x6) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
             let x5 = MICRO_RUST_SSA_CONTROL x5;
             let x6 = MICRO_RUST_SSA_CONTROL x6;
                (bind7 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4) (\<up>x5) (\<up>x6)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind8 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind8 exp x0 x1 x2 x3 x4 x5 x6 x7) =
            (let x0 = MICRO_RUST_SSA_CONTROL x0;
             let x1 = MICRO_RUST_SSA_CONTROL x1;
             let x2 = MICRO_RUST_SSA_CONTROL x2;
             let x3 = MICRO_RUST_SSA_CONTROL x3;
             let x4 = MICRO_RUST_SSA_CONTROL x4;
             let x5 = MICRO_RUST_SSA_CONTROL x5;
             let x6 = MICRO_RUST_SSA_CONTROL x6;
             let x7 = MICRO_RUST_SSA_CONTROL x7;
                (bind8 exp (\<up>x0) (\<up>x1) (\<up>x2) (\<up>x3) (\<up>x4) (\<up>x5) (\<up>x6) (\<up>x7)))\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_23
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL exp\<close>;
    match x {
      None \<Rightarrow> \<epsilon>\<open>return \<up>None\<close>,
      Some (s) \<Rightarrow> s
    }
  \<close>
  with_args exp

lemma ssa_transform_option_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_option exp) =
    SSA_urust_site_23 exp\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_option_def
    by (clarsimp simp add: micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_24
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL exp\<close>;
    match x {
      Err(e) \<Rightarrow> \<epsilon>\<open>return \<up>(Err e)\<close>,
      Ok (a) \<Rightarrow> a
    }
  \<close>
  with_args exp

lemma ssa_transform_result_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_result exp) =
    SSA_urust_site_24 exp\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_result_def
    by (clarsimp simp add: micro_rust_simps)
subsection\<open>Single static assignment form for \<^emph>\<open>Bool\<close>\<close>

lemma ssa_transform_assert [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (assert e) = \<lbrace> let x = MICRO_RUST_SSA_CONTROL e; assert (\<up>x) \<rbrace>\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def assert_def micro_rust_simps)

urust_expr [urust_abbrev = true] SSA_urust_site_25
  \<open> assert_eq!(\<epsilon>\<open>e\<close>, \<epsilon>\<open>f\<close>) \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_26
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    assert_eq!(x, y)
  \<close>
  with_args e f

lemma ssa_transform_assert_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_25 e f) = SSA_urust_site_26 e f\<close>
unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; clarsimp simp add: bind2_def
  assert_eq_def bind_literal_unit)

urust_expr [urust_abbrev = true] SSA_urust_site_27
  \<open> assert_ne!(\<epsilon>\<open>e\<close>, \<epsilon>\<open>f\<close>) \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_28
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    assert_ne!(x, y)
  \<close>
  with_args e f

lemma ssa_transform_assert_ne [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_27 e f) = SSA_urust_site_28 e f\<close>
unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; clarsimp simp add: bind2_def
  assert_ne_def bind_literal_unit)

subsection\<open>Single static assignment form for numeric and bitwise operators\<close>

urust_expr [urust_abbrev = true] SSA_urust_site_29
  \<open>
    if \<epsilon>\<open>condition_exp\<close> {
      \<epsilon>\<open>true_branch\<close>
    } else {
      \<epsilon>\<open>false_branch\<close>
    }
  \<close>
  with_args condition_exp true_branch false_branch

urust_expr [urust_abbrev = true] SSA_urust_site_30
  \<open>
    let condition_val = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL condition_exp\<close>;
    if condition_val {
      \<epsilon>\<open>MICRO_RUST_SSA_CONTROL true_branch\<close>
    } else {
      \<epsilon>\<open>MICRO_RUST_SSA_CONTROL false_branch\<close>
    }
  \<close>
  with_args condition_exp true_branch false_branch

lemma ssa_transform_two_armed_conditional [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL
    (SSA_urust_site_29 condition_exp true_branch false_branch) =
    SSA_urust_site_30 condition_exp true_branch false_branch\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; elim micro_rust_elims;
      clarsimp; intro micro_rust_intros;
      clarsimp simp add: micro_rust_simps two_armed_conditional_def; force)

urust_expr [urust_abbrev = true] SSA_urust_site_31
  \<open> if (\<epsilon>\<open>e\<close>) { \<epsilon>\<open>t\<close> } \<close>
  with_args e t

urust_expr [urust_abbrev = true] SSA_urust_site_32
  \<open> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>; if (x) { \<epsilon>\<open>MICRO_RUST_SSA_CONTROL t\<close> } \<close>
  with_args e t

corollary ssa_transform_one_armed_conditional:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_31 e t) = SSA_urust_site_32 e t\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by(metis MICRO_RUST_SSA_CONTROL_def ssa_transform_two_armed_conditional)

urust_expr [urust_abbrev = true] SSA_urust_site_33
  \<open> !\<epsilon>\<open>e :: ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> \<close>
  with_args e

urust_expr [urust_abbrev = true] SSA_urust_site_34
  \<open> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (e :: ('s, bool, 'r, 'abort, 'i, 'o) expression)\<close>; !x \<close>
  with_args e
  against \<open>\<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>; !x \<rbrakk>\<close>

lemma ssa_transform_boolean_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_33 e) = SSA_urust_site_34 e\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps negation_def)

urust_expr [urust_abbrev = true] SSA_urust_site_35
  \<open> !\<epsilon>\<open>e :: ('s, 64 word, 'r, 'abort, 'i, 'o) expression\<close> \<close>
  with_args e

urust_expr [urust_abbrev = true] SSA_urust_site_36
  \<open> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL (e :: ('s, 64 word, 'r, 'abort, 'i, 'o) expression)\<close>; !x \<close>
  with_args e
  against \<open>\<lbrakk> let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>; !x \<rbrakk>\<close>

lemma ssa_transform_binary_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_35 e) = SSA_urust_site_36 e\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps word_bitwise_not_pure_def
                                              word_bitwise_not_def)

urust_expr [urust_abbrev = true] SSA_urust_site_37
  \<open> \<epsilon>\<open>e\<close> | \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_38
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x | y
  \<close>
  with_args e f

lemma ssa_transform_binary_or [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_37 e f) = SSA_urust_site_38 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps word_bitwise_or_pure_def
                                              word_bitwise_or_def)

urust_expr [urust_abbrev = true] SSA_urust_site_39
  \<open> \<epsilon>\<open>e\<close> + \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_40
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x + y
  \<close>
  with_args e f

lemma ssa_transform_add [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_39 e f) = SSA_urust_site_40 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_add_no_wrap_def)

urust_expr [urust_abbrev = true] SSA_urust_site_41
  \<open> \<epsilon>\<open>e\<close> - \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_42
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x - y
  \<close>
  with_args e f

lemma ssa_transform_minus [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_41 e f) = SSA_urust_site_42 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_minus_no_wrap_def)

urust_expr [urust_abbrev = true] SSA_urust_site_43
  \<open> \<epsilon>\<open>e\<close> * \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_44
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x * y
  \<close>
  with_args e f

lemma ssa_transform_mul [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_43 e f) = SSA_urust_site_44 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_mul_no_wrap_def)

urust_expr [urust_abbrev = true] SSA_urust_site_45
  \<open> \<epsilon>\<open>e\<close> / \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_46
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x / y
  \<close>
  with_args e f

lemma ssa_transform_div [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_45 e f) = SSA_urust_site_46 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_udiv_def)

urust_expr [urust_abbrev = true] SSA_urust_site_47
  \<open> \<epsilon>\<open>e\<close> % \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_48
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x % y
  \<close>
  with_args e f

lemma ssa_transform_mod [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_47 e f) = SSA_urust_site_48 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_umod_def)

urust_expr [urust_abbrev = true] SSA_urust_site_49
  \<open> \<epsilon>\<open>e\<close> ^ \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_50
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x ^ y
  \<close>
  with_args e f

lemma ssa_transform_binary_xor [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_49 e f) = SSA_urust_site_50 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

urust_expr [urust_abbrev = true] SSA_urust_site_51
  \<open> \<epsilon>\<open>e\<close> & \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_52
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x & y
  \<close>
  with_args e f

lemma ssa_transform_binary_and [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_51 e f) = SSA_urust_site_52 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

urust_expr [urust_abbrev = true] SSA_urust_site_53
  \<open> \<epsilon>\<open>e\<close> << \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_54
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x << y
  \<close>
  with_args e f

lemma ssa_transform_word_shift_left [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_53 e f) = SSA_urust_site_54 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_shift_left_shift64_def word_shift_left_def)

urust_expr [urust_abbrev = true] SSA_urust_site_55
  \<open> \<epsilon>\<open>e\<close> >> \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_56
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x >> y
  \<close>
  with_args e f

lemma ssa_transform_word_shift_right [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_55 e f) = SSA_urust_site_56 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_shift_right_shift64_def word_shift_right_def)

urust_expr [urust_abbrev = true] SSA_urust_site_57
  \<open> \<epsilon>\<open>e\<close> != \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_58
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x != y
  \<close>
  with_args e f

lemma ssa_transform_urust_neq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_57 e f) = SSA_urust_site_58 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_neq_def)

urust_expr [urust_abbrev = true] SSA_urust_site_59
  \<open> \<epsilon>\<open>e\<close> == \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_60
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x == y
  \<close>
  with_args e f

lemma ssa_transform_urust_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_59 e f) = SSA_urust_site_60 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_eq_def)

urust_expr [urust_abbrev = true] SSA_urust_site_61
  \<open> \<epsilon>\<open>e\<close> || \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_62
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    if x {
      True
    } else {
      let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
      y
    }
  \<close>
  with_args e f

lemma ssa_transform_urust_disj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_61 e f) = SSA_urust_site_62 e f\<close>
  by (simp add: urust_disj_def micro_rust_simps MICRO_RUST_SSA_CONTROL_def
    two_armed_conditional_def) (meson true_def)

urust_expr [urust_abbrev = true] SSA_urust_site_63
  \<open> \<epsilon>\<open>e\<close> && \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_64
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    if x {
      let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
      y
    } else {
      False
    }
  \<close>
  with_args e f

lemma ssa_transform_urust_conj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_63 e f) = SSA_urust_site_64 e f\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def micro_rust_simps urust_conj_def
    two_armed_conditional_def) (meson false_def)

urust_expr [urust_abbrev = true] SSA_urust_site_65
  \<open> \<epsilon>\<open>e\<close> >= \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_66
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x >= y
  \<close>
  with_args e f

lemma ssa_transform_urust_ge [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_65 e f) = SSA_urust_site_66 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_ge_def) 

urust_expr [urust_abbrev = true] SSA_urust_site_67
  \<open> \<epsilon>\<open>e\<close> <= \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_68
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x <= y
  \<close>
  with_args e f

lemma ssa_transform_urust_le [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_67 e f) = SSA_urust_site_68 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_le_def) 

urust_expr [urust_abbrev = true] SSA_urust_site_69
  \<open> \<epsilon>\<open>e\<close> > \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_70
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x > y
  \<close>
  with_args e f

lemma ssa_transform_urust_gt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_69 e f) = SSA_urust_site_70 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_gt_def) 

urust_expr [urust_abbrev = true] SSA_urust_site_71
  \<open> \<epsilon>\<open>e\<close> < \<epsilon>\<open>f\<close> \<close>
  with_args e f

urust_expr [urust_abbrev = true] SSA_urust_site_72
  \<open>
    let x = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL e\<close>;
    let y = \<epsilon>\<open>MICRO_RUST_SSA_CONTROL f\<close>;
    x < y
  \<close>
  with_args e f

lemma ssa_transform_urust_lt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (SSA_urust_site_71 e f) = SSA_urust_site_72 e f\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_lt_def) 

subsection\<open>Single static assignment form for loops\<close>

lemma ssa_transform_for_loop [micro_rust_ssa]:
  shows \<open>\<lbrace> MICRO_RUST_SSA_CONTROL (for_loop i body) \<rbrace> = 
         \<lbrace> let x = MICRO_RUST_SSA_CONTROL i;
           for_loop (literal x) (\<lambda>idx. MICRO_RUST_SSA_CONTROL (body idx)) \<rbrace>\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind_literal_unit for_loop_def)

(*<*)
end
(*>*)
