(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory SSA
  imports Core_Expression_Lemmas Bool_Type_Lemmas Rust_Iterator_Lemmas
          "HOL-Library.Rewrite"
begin
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



lemma ssa_transform_funcall1 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall1 f e)) = (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         funcall1 f (literal x0) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall2 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall2 fn e f)) = (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         funcall2 fn (literal x0) (literal x1) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall3 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall3 fn e0 e1 e2)) =
    (do { v0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         v1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         v2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         funcall3 fn (literal v0) (literal v1) (literal v2) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall4 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall4 fn e0 e1 e2 e3)) =
    (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         x2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         x3 \<leftarrow> MICRO_RUST_SSA_CONTROL e3;
         funcall4 fn (literal x0) (literal x1) (literal x2) (literal x3) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall5 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall5 fn e0 e1 e2 e3 e4)) =
    (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         x2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         x3 \<leftarrow> MICRO_RUST_SSA_CONTROL e3;
         x4 \<leftarrow> MICRO_RUST_SSA_CONTROL e4;
         funcall5 fn (literal x0) (literal x1) (literal x2) (literal x3)
           (literal x4) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall6 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall6 fn e0 e1 e2 e3 e4 e5)) =
    (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         x2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         x3 \<leftarrow> MICRO_RUST_SSA_CONTROL e3;
         x4 \<leftarrow> MICRO_RUST_SSA_CONTROL e4;
         x5 \<leftarrow> MICRO_RUST_SSA_CONTROL e5;
         funcall6 fn (literal x0) (literal x1) (literal x2) (literal x3)
           (literal x4) (literal x5) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall7 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall7 fn e0 e1 e2 e3 e4 e5 e6)) =
    (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         x2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         x3 \<leftarrow> MICRO_RUST_SSA_CONTROL e3;
         x4 \<leftarrow> MICRO_RUST_SSA_CONTROL e4;
         x5 \<leftarrow> MICRO_RUST_SSA_CONTROL e5;
         x6 \<leftarrow> MICRO_RUST_SSA_CONTROL e6;
         funcall7 fn (literal x0) (literal x1) (literal x2) (literal x3)
           (literal x4) (literal x5) (literal x6) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall8 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall8 fn e0 e1 e2 e3 e4 e5 e6 e7)) =
    (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         x2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         x3 \<leftarrow> MICRO_RUST_SSA_CONTROL e3;
         x4 \<leftarrow> MICRO_RUST_SSA_CONTROL e4;
         x5 \<leftarrow> MICRO_RUST_SSA_CONTROL e5;
         x6 \<leftarrow> MICRO_RUST_SSA_CONTROL e6;
         x7 \<leftarrow> MICRO_RUST_SSA_CONTROL e7;
         funcall8 fn (literal x0) (literal x1) (literal x2) (literal x3)
           (literal x4) (literal x5) (literal x6) (literal x7) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall9 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall9 fn e0 e1 e2 e3 e4 e5 e6 e7 e8)) =
    (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         x2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         x3 \<leftarrow> MICRO_RUST_SSA_CONTROL e3;
         x4 \<leftarrow> MICRO_RUST_SSA_CONTROL e4;
         x5 \<leftarrow> MICRO_RUST_SSA_CONTROL e5;
         x6 \<leftarrow> MICRO_RUST_SSA_CONTROL e6;
         x7 \<leftarrow> MICRO_RUST_SSA_CONTROL e7;
         x8 \<leftarrow> MICRO_RUST_SSA_CONTROL e8;
         funcall9 fn (literal x0) (literal x1) (literal x2) (literal x3)
           (literal x4) (literal x5) (literal x6) (literal x7) (literal x8) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)



lemma ssa_transform_funcall10 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((funcall10 fn e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)) =
    (do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e0;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL e1;
         x2 \<leftarrow> MICRO_RUST_SSA_CONTROL e2;
         x3 \<leftarrow> MICRO_RUST_SSA_CONTROL e3;
         x4 \<leftarrow> MICRO_RUST_SSA_CONTROL e4;
         x5 \<leftarrow> MICRO_RUST_SSA_CONTROL e5;
         x6 \<leftarrow> MICRO_RUST_SSA_CONTROL e6;
         x7 \<leftarrow> MICRO_RUST_SSA_CONTROL e7;
         x8 \<leftarrow> MICRO_RUST_SSA_CONTROL e8;
         x9 \<leftarrow> MICRO_RUST_SSA_CONTROL e9;
         funcall10 fn (literal x0) (literal x1) (literal x2) (literal x3)
           (literal x4) (literal x5) (literal x6) (literal x7) (literal x8)
           (literal x9) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

text\<open>We hoist the expression to be returned out of the \<^verbatim>\<open>return\<close> expression, simplify it recursively
and bind it to a variable.  We then return that variable:\<close>


lemma ssa_transform_return [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((return_func r)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL r; return_func (literal x) })\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def return_func_def micro_rust_simps)

lemma ssa_transform_bind2 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind2 exp e f) =
    do { x0 \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         x1 \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         bind2 exp (literal x0) (literal x1) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind3 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind3 exp x0 x1 x2) =
    do { v0 \<leftarrow> MICRO_RUST_SSA_CONTROL x0;
         v1 \<leftarrow> MICRO_RUST_SSA_CONTROL x1;
         v2 \<leftarrow> MICRO_RUST_SSA_CONTROL x2;
         bind3 exp (literal v0) (literal v1) (literal v2) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind4 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind4 exp x0 x1 x2 x3) =
    do { y0 \<leftarrow> MICRO_RUST_SSA_CONTROL x0;
         y1 \<leftarrow> MICRO_RUST_SSA_CONTROL x1;
         y2 \<leftarrow> MICRO_RUST_SSA_CONTROL x2;
         y3 \<leftarrow> MICRO_RUST_SSA_CONTROL x3;
         bind4 exp (literal y0) (literal y1) (literal y2) (literal y3) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind5 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind5 exp x0 x1 x2 x3 x4) =
    do { y0 \<leftarrow> MICRO_RUST_SSA_CONTROL x0;
         y1 \<leftarrow> MICRO_RUST_SSA_CONTROL x1;
         y2 \<leftarrow> MICRO_RUST_SSA_CONTROL x2;
         y3 \<leftarrow> MICRO_RUST_SSA_CONTROL x3;
         y4 \<leftarrow> MICRO_RUST_SSA_CONTROL x4;
         bind5 exp (literal y0) (literal y1) (literal y2) (literal y3)
           (literal y4) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind6 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind6 exp x0 x1 x2 x3 x4 x5) =
    do { y0 \<leftarrow> MICRO_RUST_SSA_CONTROL x0;
         y1 \<leftarrow> MICRO_RUST_SSA_CONTROL x1;
         y2 \<leftarrow> MICRO_RUST_SSA_CONTROL x2;
         y3 \<leftarrow> MICRO_RUST_SSA_CONTROL x3;
         y4 \<leftarrow> MICRO_RUST_SSA_CONTROL x4;
         y5 \<leftarrow> MICRO_RUST_SSA_CONTROL x5;
         bind6 exp (literal y0) (literal y1) (literal y2) (literal y3)
           (literal y4) (literal y5) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind7 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind7 exp x0 x1 x2 x3 x4 x5 x6) =
    do { y0 \<leftarrow> MICRO_RUST_SSA_CONTROL x0;
         y1 \<leftarrow> MICRO_RUST_SSA_CONTROL x1;
         y2 \<leftarrow> MICRO_RUST_SSA_CONTROL x2;
         y3 \<leftarrow> MICRO_RUST_SSA_CONTROL x3;
         y4 \<leftarrow> MICRO_RUST_SSA_CONTROL x4;
         y5 \<leftarrow> MICRO_RUST_SSA_CONTROL x5;
         y6 \<leftarrow> MICRO_RUST_SSA_CONTROL x6;
         bind7 exp (literal y0) (literal y1) (literal y2) (literal y3)
           (literal y4) (literal y5) (literal y6) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_bind8 [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (bind8 exp x0 x1 x2 x3 x4 x5 x6 x7) =
    do { y0 \<leftarrow> MICRO_RUST_SSA_CONTROL x0;
         y1 \<leftarrow> MICRO_RUST_SSA_CONTROL x1;
         y2 \<leftarrow> MICRO_RUST_SSA_CONTROL x2;
         y3 \<leftarrow> MICRO_RUST_SSA_CONTROL x3;
         y4 \<leftarrow> MICRO_RUST_SSA_CONTROL x4;
         y5 \<leftarrow> MICRO_RUST_SSA_CONTROL x5;
         y6 \<leftarrow> MICRO_RUST_SSA_CONTROL x6;
         y7 \<leftarrow> MICRO_RUST_SSA_CONTROL x7;
         bind8 exp (literal y0) (literal y1) (literal y2) (literal y3)
           (literal y4) (literal y5) (literal y6) (literal y7) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps)


lemma ssa_transform_option_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_option exp) =
    (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL exp;
         case x of None \<Rightarrow> return_func (literal None)
                 | Some s \<Rightarrow> literal s })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_option_def
    by (clarsimp simp add: micro_rust_simps)


lemma ssa_transform_result_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_result exp) =
    (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL exp;
         case x of Err e \<Rightarrow> return_func (literal (Err e))
                 | Ok a \<Rightarrow> literal a })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_result_def
    by (clarsimp simp add: micro_rust_simps)
subsection\<open>Single static assignment form for \<^emph>\<open>Bool\<close>\<close>

lemma ssa_transform_assert [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (assert e) =
    do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e; assert (literal x) }\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def assert_def micro_rust_simps)



lemma ssa_transform_assert_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((assert_eq e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         assert_eq (literal x) (literal y) })\<close>
unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; clarsimp simp add: bind2_def
  assert_eq_def bind_literal_unit)



lemma ssa_transform_assert_ne [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((assert_ne e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         assert_ne (literal x) (literal y) })\<close>
unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; clarsimp simp add: bind2_def
  assert_ne_def bind_literal_unit)

subsection\<open>Single static assignment form for numeric and bitwise operators\<close>



lemma ssa_transform_two_armed_conditional [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL
    ((two_armed_conditional condition_exp true_branch false_branch)) =
    (do { condition_val \<leftarrow> MICRO_RUST_SSA_CONTROL condition_exp;
         two_armed_conditional (literal condition_val)
           (MICRO_RUST_SSA_CONTROL true_branch)
           (MICRO_RUST_SSA_CONTROL false_branch) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (rule expression_eqI; elim micro_rust_elims;
      clarsimp; intro micro_rust_intros;
      clarsimp simp add: micro_rust_simps two_armed_conditional_def; force)



corollary ssa_transform_one_armed_conditional:
  shows \<open>MICRO_RUST_SSA_CONTROL ((one_armed_conditional e t)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         one_armed_conditional (literal x) (MICRO_RUST_SSA_CONTROL t) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
    by(metis MICRO_RUST_SSA_CONTROL_def ssa_transform_two_armed_conditional)



lemma ssa_transform_boolean_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((negation e)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e; negation (literal x) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps negation_def)



lemma ssa_transform_binary_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((Numeric_Types.word_bitwise_not e)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         Numeric_Types.word_bitwise_not (literal x) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps word_bitwise_not_pure_def
                                              word_bitwise_not_def)



lemma ssa_transform_binary_or [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((Numeric_Types.word_bitwise_or e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         Numeric_Types.word_bitwise_or (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2; clarsimp simp add:micro_rust_simps word_bitwise_or_pure_def
                                              word_bitwise_or_def)



lemma ssa_transform_add [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((word_add_no_wrap e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         word_add_no_wrap (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_add_no_wrap_def)



lemma ssa_transform_minus [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((word_minus_no_wrap e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         word_minus_no_wrap (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_minus_no_wrap_def)



lemma ssa_transform_mul [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((word_mul_no_wrap e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         word_mul_no_wrap (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def 
  by (simp add: bind2_def bind_literal_unit word_mul_no_wrap_def)



lemma ssa_transform_div [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((word_udiv e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         word_udiv (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_udiv_def)



lemma ssa_transform_mod [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((word_umod e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         word_umod (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_umod_def)



lemma ssa_transform_binary_xor [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((Numeric_Types.word_bitwise_xor e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         Numeric_Types.word_bitwise_xor (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)



lemma ssa_transform_binary_and [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((Numeric_Types.word_bitwise_and e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         Numeric_Types.word_bitwise_and (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)



lemma ssa_transform_word_shift_left [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((word_shift_left_shift64 e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         word_shift_left_shift64 (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_shift_left_shift64_def word_shift_left_def)



lemma ssa_transform_word_shift_right [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((word_shift_right_shift64 e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         word_shift_right_shift64 (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add:micro_rust_simps word_shift_right_shift64_def word_shift_right_def)



lemma ssa_transform_urust_neq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((urust_neq e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         urust_neq (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_neq_def)



lemma ssa_transform_urust_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((urust_eq e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         urust_eq (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_eq_def)



lemma ssa_transform_urust_disj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((urust_disj e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         two_armed_conditional (literal x) (literal True)
           (MICRO_RUST_SSA_CONTROL f) })\<close>
  by (simp add: urust_disj_def micro_rust_simps MICRO_RUST_SSA_CONTROL_def
    two_armed_conditional_def) (meson true_def)



lemma ssa_transform_urust_conj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((urust_conj e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         two_armed_conditional (literal x) (MICRO_RUST_SSA_CONTROL f)
           (literal False) })\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def micro_rust_simps urust_conj_def
    two_armed_conditional_def) (meson false_def)



lemma ssa_transform_urust_ge [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((comp_ge e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         comp_ge (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_ge_def) 



lemma ssa_transform_urust_le [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((comp_le e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         comp_le (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_le_def) 



lemma ssa_transform_urust_gt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((comp_gt e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         comp_gt (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_gt_def) 



lemma ssa_transform_urust_lt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL ((comp_lt e f)) = (do { x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
         y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
         comp_lt (literal x) (literal y) })\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def by (clarsimp simp add: micro_rust_simps comp_lt_def) 

subsection\<open>Single static assignment form for loops\<close>

lemma ssa_transform_for_loop [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (for_loop i body) =
    do { x \<leftarrow> MICRO_RUST_SSA_CONTROL i;
         for_loop (literal x) (\<lambda>idx. MICRO_RUST_SSA_CONTROL (body idx)) }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind_literal_unit for_loop_def)

(*<*)
end
(*>*)
