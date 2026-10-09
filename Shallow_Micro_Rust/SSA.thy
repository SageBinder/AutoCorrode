(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory SSA
  imports
    Shallow_Computation.Expression_Normalization
    Core_Expression_Lemmas_Profile
    Bool_Type_Lemmas
    Rust_Iterator_Lemmas
    Numeric_Types
    Option_Type
    Result_Type
    "HOL-Library.Rewrite"
begin
(*>*)

section\<open>Micro Rust expression normalization extensions\<close>

text\<open>
The language-neutral call, bind, return, and conditional normalization rules live in
\<^theory>\<open>Shallow_Computation.Expression_Normalization\<close>.  This theory extends that
foundation with transformations for Rust-specific propagation, assertions, operators,
and iterators.

The identity wrapper keeps application of the Rust extension rules under the same
explicit control as the language-neutral rules.
\<close>

definition MICRO_RUST_SSA_CONTROL ::
  \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  where \<open>MICRO_RUST_SSA_CONTROL e \<equiv> e\<close>

lemma ssa_transform_option_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_option exp) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL exp;
      case x of
        None \<Rightarrow> return_func (literal None)
      | Some s \<Rightarrow> literal s
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_option_def
  by (clarsimp simp add: micro_rust_simps)

lemma ssa_transform_result_propagate [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (propagate_result exp) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL exp;
      case x of
        Err e \<Rightarrow> return_func (literal (Err e))
      | Ok a \<Rightarrow> literal a
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def propagate_result_def
  by (clarsimp simp add: micro_rust_simps)

subsection\<open>Assertions\<close>

lemma ssa_transform_assert [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (assert e) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      assert (literal x)
    }\<close>
  by (simp add: MICRO_RUST_SSA_CONTROL_def assert_def micro_rust_simps)

lemma ssa_transform_assert_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (assert_eq e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      assert_eq (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI;
      clarsimp simp add: bind2_def assert_eq_def bind_literal_unit)

lemma ssa_transform_assert_ne [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (assert_ne e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      assert_ne (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI;
      clarsimp simp add: bind2_def assert_ne_def bind_literal_unit)

subsection\<open>Boolean, numeric, and bitwise operators\<close>

lemma ssa_transform_boolean_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (negation e) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      negation (literal x)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2;
      clarsimp simp add: micro_rust_simps negation_def)

lemma ssa_transform_binary_not [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (Numeric_Types.word_bitwise_not e) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      Numeric_Types.word_bitwise_not (literal x)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2;
      clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def
        word_bitwise_not_def)

lemma ssa_transform_binary_or [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (Numeric_Types.word_bitwise_or e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      Numeric_Types.word_bitwise_or (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (rule expression_eqI2;
      clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def
        word_bitwise_or_def)

lemma ssa_transform_add [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (word_add_no_wrap e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      word_add_no_wrap (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_add_no_wrap_def)

lemma ssa_transform_minus [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (word_minus_no_wrap e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      word_minus_no_wrap (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_minus_no_wrap_def)

lemma ssa_transform_mul [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (word_mul_no_wrap e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      word_mul_no_wrap (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_mul_no_wrap_def)

lemma ssa_transform_div [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (word_udiv e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      word_udiv (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_udiv_def)

lemma ssa_transform_mod [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (word_umod e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      word_umod (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind2_def bind_literal_unit word_umod_def)

lemma ssa_transform_binary_xor [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (Numeric_Types.word_bitwise_xor e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      Numeric_Types.word_bitwise_xor (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def
      word_bitwise_xor_def)

lemma ssa_transform_binary_and [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (Numeric_Types.word_bitwise_and e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      Numeric_Types.word_bitwise_and (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def
      word_bitwise_and_def)

lemma ssa_transform_word_shift_left [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (word_shift_left_shift64 e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      word_shift_left_shift64 (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps word_shift_left_shift64_def
      word_shift_left_def)

lemma ssa_transform_word_shift_right [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (word_shift_right_shift64 e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      word_shift_right_shift64 (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps word_shift_right_shift64_def
      word_shift_right_def)

lemma ssa_transform_urust_neq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (urust_neq e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      urust_neq (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_neq_def)

lemma ssa_transform_urust_eq [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (urust_eq e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      urust_eq (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps urust_eq_def)

lemma ssa_transform_urust_disj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (urust_disj e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      two_armed_conditional (literal x) (literal True)
        (MICRO_RUST_SSA_CONTROL f)
    }\<close>
  by (simp add: urust_disj_def micro_rust_simps
      MICRO_RUST_SSA_CONTROL_def two_armed_conditional_def)
    (meson true_def)

lemma ssa_transform_urust_conj [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (urust_conj e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      two_armed_conditional (literal x)
        (MICRO_RUST_SSA_CONTROL f) (literal False)
    }\<close>
  by (clarsimp simp add: MICRO_RUST_SSA_CONTROL_def micro_rust_simps
      urust_conj_def two_armed_conditional_def)
    (meson false_def)

lemma ssa_transform_urust_ge [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (comp_ge e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      comp_ge (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

lemma ssa_transform_urust_le [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (comp_le e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      comp_le (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps comp_le_def)

lemma ssa_transform_urust_gt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (comp_gt e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      comp_gt (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

lemma ssa_transform_urust_lt [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (comp_lt e f) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL e;
      y \<leftarrow> MICRO_RUST_SSA_CONTROL f;
      comp_lt (literal x) (literal y)
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

subsection\<open>Rust iterator loops\<close>

lemma ssa_transform_for_loop [micro_rust_ssa]:
  shows \<open>MICRO_RUST_SSA_CONTROL (for_loop i body) =
    do {
      x \<leftarrow> MICRO_RUST_SSA_CONTROL i;
      for_loop (literal x)
        (\<lambda>idx. MICRO_RUST_SSA_CONTROL (body idx))
    }\<close>
  unfolding MICRO_RUST_SSA_CONTROL_def
  by (simp add: bind_literal_unit for_loop_def)

(*<*)
end
(*>*)
