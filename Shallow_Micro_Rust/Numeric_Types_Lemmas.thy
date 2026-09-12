(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types_Lemmas
  imports Core_Expression_Lemmas Shallow_Micro_Rust_Base.Numeric_Types
begin
declare [[urust_conformance_check = true]]
(*>*)

urust_expr [abbrev = true] evaluate_lt_literal_1
  (c, d)
  \<open> c < d \<close>

urust_expr [abbrev = true] evaluate_lt_literal_2
  (c, d)
  \<open> \<llangle>c < d\<rrangle> \<close>

lemma evaluate_lt_literal [micro_rust_simps]:
  shows \<open>evaluate_lt_literal_1 c d = evaluate_lt_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

urust_expr [abbrev = true] evaluate_gt_literal_1
  (c, d)
  \<open> c > d \<close>

urust_expr [abbrev = true] evaluate_gt_literal_2
  (c, d)
  \<open> \<llangle>c > d\<rrangle> \<close>

lemma evaluate_gt_literal [micro_rust_simps]:
  shows \<open>evaluate_gt_literal_1 c d = evaluate_gt_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

urust_expr [abbrev = true] evaluate_ge_literal_1
  (c, d)
  \<open> c >= d \<close>

urust_expr [abbrev = true] evaluate_ge_literal_2
  (c, d)
  \<open> \<llangle>c \<ge> d\<rrangle> \<close>

lemma evaluate_ge_literal [micro_rust_simps]:
  shows \<open>evaluate_ge_literal_1 c d = evaluate_ge_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

urust_expr [abbrev = true] evaluate_le_literal_1
  (c, d)
  \<open> c <= d \<close>

urust_expr [abbrev = true] evaluate_le_literal_2
  (c, d)
  \<open> \<llangle>c \<le> d\<rrangle> \<close>

lemma evaluate_le_literal [micro_rust_simps]:
  shows \<open>evaluate_le_literal_1 c d = evaluate_le_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_le_def)

urust_expr [abbrev = true] evaluate_word_bitwise_or_literal_1
  (c, d)
  \<open> c | d \<close>

urust_expr [abbrev = true] evaluate_word_bitwise_or_literal_2
  (c, d)
  \<open> \<llangle>c OR d\<rrangle> \<close>

lemma evaluate_word_bitwise_or_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_or_literal_1 c d = evaluate_word_bitwise_or_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def word_bitwise_or_def)

urust_expr [abbrev = true] evaluate_word_bitwise_xor_literal_1
  (c, d)
  \<open> c ^ d \<close>

urust_expr [abbrev = true] evaluate_word_bitwise_xor_literal_2
  (c, d)
  \<open> \<llangle>c XOR d\<rrangle> \<close>

lemma evaluate_word_bitwise_xor_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_xor_literal_1 c d = evaluate_word_bitwise_xor_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

urust_expr [abbrev = true] evaluate_word_bitwise_and_literal_1
  (c, d)
  \<open> c & d \<close>

urust_expr [abbrev = true] evaluate_word_bitwise_and_literal_2
  (c, d)
  \<open> \<llangle>c AND d\<rrangle> \<close>

lemma evaluate_word_bitwise_and_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_and_literal_1 c d = evaluate_word_bitwise_and_literal_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

urust_expr [abbrev = true] evaluate_word_bitwise_not_literal_1 ::
  \<open>'l::len word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close>
  (d)
  \<open> !d \<close>

urust_expr [abbrev = true] evaluate_word_bitwise_not_literal_2
  (d)
  \<open> \<llangle>NOT d\<rrangle> \<close>

lemma evaluate_word_bitwise_not_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_not_literal_1 d = evaluate_word_bitwise_not_literal_2 d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def word_bitwise_not_def)

urust_expr [abbrev = true] evaluate_word_shift_left_literal_1
  (c, d)
  \<open> c << d \<close>

urust_expr [abbrev = true] evaluate_word_shift_left_literal_2
  (d, c)
  \<open> \<llangle>push_bit (unat d) c\<rrangle> \<close>

lemma evaluate_word_shift_left_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>evaluate_word_shift_left_literal_1 c d =
    evaluate_word_shift_left_literal_2 d c\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_left_def 
    word_shift_left_shift64_def
    word_shift_left_pure_def word_shift_left_core_def word_shift_left_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

urust_expr [abbrev = true] evaluate_word_shift_right_literal_1
  (c, d)
  \<open> c >> d \<close>

urust_expr [abbrev = true] evaluate_word_shift_right_literal_2
  (d, c)
  \<open> \<llangle>drop_bit (unat d) c\<rrangle> \<close>

lemma evaluate_word_shift_right_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>evaluate_word_shift_right_literal_1 c d =
    evaluate_word_shift_right_literal_2 d c\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_right_def 
    word_shift_right_shift64_def
    word_shift_right_pure_def word_shift_right_core_def word_shift_right_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

(*<*)
end
(*>*)
