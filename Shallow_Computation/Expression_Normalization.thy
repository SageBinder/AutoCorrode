(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Expression_Normalization
  imports
    Control_Flow
    Core_Expression_Lemmas
begin

section\<open>Language-neutral expression normalization\<close>

text\<open>
Effectful operands are hoisted into explicit bindings before weakest-precondition
automation processes an expression.  The control wrapper marks the expression at
which one normalization step is requested and prevents a rewrite from recursively
rewriting the subexpressions it has just produced.
\<close>

definition SHALLOW_COMPUTATION_SSA_CONTROL ::
  \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  where \<open>SHALLOW_COMPUTATION_SSA_CONTROL e \<equiv> e\<close>

named_theorems shallow_computation_ssa

lemma ssa_transform_funcall1 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall1 f e) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e;
      funcall1 f (literal x0)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall2 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall2 fn e f) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL f;
      funcall2 fn (literal x0) (literal x1)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall3 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall3 fn e0 e1 e2) =
    do {
      v0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      v1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      v2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      funcall3 fn (literal v0) (literal v1) (literal v2)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall4 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall4 fn e0 e1 e2 e3) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      x2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      x3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e3;
      funcall4 fn (literal x0) (literal x1) (literal x2) (literal x3)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall5 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall5 fn e0 e1 e2 e3 e4) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      x2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      x3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e3;
      x4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e4;
      funcall5 fn (literal x0) (literal x1) (literal x2) (literal x3)
        (literal x4)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall6 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall6 fn e0 e1 e2 e3 e4 e5) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      x2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      x3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e3;
      x4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e4;
      x5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e5;
      funcall6 fn (literal x0) (literal x1) (literal x2) (literal x3)
        (literal x4) (literal x5)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall7 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall7 fn e0 e1 e2 e3 e4 e5 e6) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      x2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      x3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e3;
      x4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e4;
      x5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e5;
      x6 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e6;
      funcall7 fn (literal x0) (literal x1) (literal x2) (literal x3)
        (literal x4) (literal x5) (literal x6)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall8 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (funcall8 fn e0 e1 e2 e3 e4 e5 e6 e7) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      x2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      x3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e3;
      x4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e4;
      x5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e5;
      x6 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e6;
      x7 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e7;
      funcall8 fn (literal x0) (literal x1) (literal x2) (literal x3)
        (literal x4) (literal x5) (literal x6) (literal x7)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall9 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL
      (funcall9 fn e0 e1 e2 e3 e4 e5 e6 e7 e8) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      x2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      x3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e3;
      x4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e4;
      x5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e5;
      x6 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e6;
      x7 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e7;
      x8 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e8;
      funcall9 fn (literal x0) (literal x1) (literal x2) (literal x3)
        (literal x4) (literal x5) (literal x6) (literal x7) (literal x8)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_funcall10 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL
      (funcall10 fn e0 e1 e2 e3 e4 e5 e6 e7 e8 e9) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e0;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e1;
      x2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e2;
      x3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e3;
      x4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e4;
      x5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e5;
      x6 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e6;
      x7 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e7;
      x8 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e8;
      x9 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e9;
      funcall10 fn (literal x0) (literal x1) (literal x2) (literal x3)
        (literal x4) (literal x5) (literal x6) (literal x7) (literal x8)
        (literal x9)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_return [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (return_func r) =
    do {
      x \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL r;
      return_func (literal x)
    }\<close>
  by (simp add: SHALLOW_COMPUTATION_SSA_CONTROL_def return_func_def
      shallow_computation_simps)

lemma ssa_transform_bind2 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (bind2 exp e f) =
    do {
      x0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e;
      x1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL f;
      bind2 exp (literal x0) (literal x1)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_bind3 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (bind3 exp x0 x1 x2) =
    do {
      v0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x0;
      v1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x1;
      v2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x2;
      bind3 exp (literal v0) (literal v1) (literal v2)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_bind4 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (bind4 exp x0 x1 x2 x3) =
    do {
      y0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x0;
      y1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x1;
      y2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x2;
      y3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x3;
      bind4 exp (literal y0) (literal y1) (literal y2) (literal y3)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_bind5 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (bind5 exp x0 x1 x2 x3 x4) =
    do {
      y0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x0;
      y1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x1;
      y2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x2;
      y3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x3;
      y4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x4;
      bind5 exp (literal y0) (literal y1) (literal y2) (literal y3)
        (literal y4)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_bind6 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (bind6 exp x0 x1 x2 x3 x4 x5) =
    do {
      y0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x0;
      y1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x1;
      y2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x2;
      y3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x3;
      y4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x4;
      y5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x5;
      bind6 exp (literal y0) (literal y1) (literal y2) (literal y3)
        (literal y4) (literal y5)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_bind7 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL
      (bind7 exp x0 x1 x2 x3 x4 x5 x6) =
    do {
      y0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x0;
      y1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x1;
      y2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x2;
      y3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x3;
      y4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x4;
      y5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x5;
      y6 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x6;
      bind7 exp (literal y0) (literal y1) (literal y2) (literal y3)
        (literal y4) (literal y5) (literal y6)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_bind8 [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL
      (bind8 exp x0 x1 x2 x3 x4 x5 x6 x7) =
    do {
      y0 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x0;
      y1 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x1;
      y2 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x2;
      y3 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x3;
      y4 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x4;
      y5 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x5;
      y6 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x6;
      y7 \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL x7;
      bind8 exp (literal y0) (literal y1) (literal y2) (literal y3)
        (literal y4) (literal y5) (literal y6) (literal y7)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (clarsimp simp add: shallow_computation_simps)

lemma ssa_transform_two_armed_conditional [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL
      (two_armed_conditional condition_exp true_branch false_branch) =
    do {
      condition_val \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL condition_exp;
      two_armed_conditional (literal condition_val)
        (SHALLOW_COMPUTATION_SSA_CONTROL true_branch)
        (SHALLOW_COMPUTATION_SSA_CONTROL false_branch)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (simp add: shallow_computation_simps two_armed_conditional_def)

corollary ssa_transform_one_armed_conditional [shallow_computation_ssa]:
  shows \<open>SHALLOW_COMPUTATION_SSA_CONTROL (one_armed_conditional e t) =
    do {
      x \<leftarrow> SHALLOW_COMPUTATION_SSA_CONTROL e;
      one_armed_conditional (literal x)
        (SHALLOW_COMPUTATION_SSA_CONTROL t)
    }\<close>
  unfolding SHALLOW_COMPUTATION_SSA_CONTROL_def
  by (metis SHALLOW_COMPUTATION_SSA_CONTROL_def
      ssa_transform_two_armed_conditional)

end
