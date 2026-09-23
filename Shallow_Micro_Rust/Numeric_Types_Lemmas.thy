(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types_Lemmas
  imports Core_Expression_Lemmas Shallow_Micro_Rust_Base.Numeric_Types
begin
(*>*)

abbreviation evaluate_lt_literal_expr1 where
  \<open>evaluate_lt_literal_expr1 c d \<equiv> comp_lt (literal c) (literal d)\<close>

abbreviation evaluate_lt_literal_expr2 where
  \<open>evaluate_lt_literal_expr2 c d \<equiv> literal (c < d)\<close>

lemma evaluate_lt_literal [micro_rust_simps]:
  shows \<open>evaluate_lt_literal_expr1 c d = evaluate_lt_literal_expr2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

abbreviation evaluate_gt_literal_expr1 where
  \<open>evaluate_gt_literal_expr1 c d \<equiv> comp_gt (literal c) (literal d)\<close>

abbreviation evaluate_gt_literal_expr2 where
  \<open>evaluate_gt_literal_expr2 c d \<equiv> literal (c > d)\<close>

lemma evaluate_gt_literal [micro_rust_simps]:
  shows \<open>evaluate_gt_literal_expr1 c d = evaluate_gt_literal_expr2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

abbreviation evaluate_ge_literal_expr1 where
  \<open>evaluate_ge_literal_expr1 c d \<equiv> comp_ge (literal c) (literal d)\<close>

abbreviation evaluate_ge_literal_expr2 where
  \<open>evaluate_ge_literal_expr2 c d \<equiv> literal (c \<ge> d)\<close>

lemma evaluate_ge_literal [micro_rust_simps]:
  shows \<open>evaluate_ge_literal_expr1 c d = evaluate_ge_literal_expr2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

abbreviation evaluate_le_literal_expr1 where
  \<open>evaluate_le_literal_expr1 c d \<equiv> comp_le (literal c) (literal d)\<close>

abbreviation evaluate_le_literal_expr2 where
  \<open>evaluate_le_literal_expr2 c d \<equiv> literal (c \<le> d)\<close>

lemma evaluate_le_literal [micro_rust_simps]:
  shows \<open>evaluate_le_literal_expr1 c d = evaluate_le_literal_expr2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_le_def)

abbreviation evaluate_word_bitwise_or_literal_expr1 where
  \<open>evaluate_word_bitwise_or_literal_expr1 c d \<equiv>
    word_bitwise_or (literal c) (literal d)\<close>

abbreviation evaluate_word_bitwise_or_literal_expr2 where
  \<open>evaluate_word_bitwise_or_literal_expr2 c d \<equiv> literal (c OR d)\<close>

lemma evaluate_word_bitwise_or_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_or_literal_expr1 c d = evaluate_word_bitwise_or_literal_expr2 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def word_bitwise_or_def)

abbreviation evaluate_word_bitwise_xor_literal_expr1 where
  \<open>evaluate_word_bitwise_xor_literal_expr1 c d \<equiv>
    word_bitwise_xor (literal c) (literal d)\<close>

abbreviation evaluate_word_bitwise_xor_literal_expr2 where
  \<open>evaluate_word_bitwise_xor_literal_expr2 c d \<equiv> literal (c XOR d)\<close>

lemma evaluate_word_bitwise_xor_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_xor_literal_expr1 c d = evaluate_word_bitwise_xor_literal_expr2 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

abbreviation evaluate_word_bitwise_and_literal_expr1 where
  \<open>evaluate_word_bitwise_and_literal_expr1 c d \<equiv>
    word_bitwise_and (literal c) (literal d)\<close>

abbreviation evaluate_word_bitwise_and_literal_expr2 where
  \<open>evaluate_word_bitwise_and_literal_expr2 c d \<equiv> literal (c AND d)\<close>

lemma evaluate_word_bitwise_and_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_and_literal_expr1 c d = evaluate_word_bitwise_and_literal_expr2 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

abbreviation evaluate_word_bitwise_not_literal_expr1 ::
  \<open>'l::len word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close>
  where \<open>evaluate_word_bitwise_not_literal_expr1 d \<equiv>
    word_bitwise_not (literal d)\<close>

abbreviation evaluate_word_bitwise_not_literal_expr2 where
  \<open>evaluate_word_bitwise_not_literal_expr2 d \<equiv> literal (NOT d)\<close>

lemma evaluate_word_bitwise_not_literal [micro_rust_simps]:
  shows \<open>evaluate_word_bitwise_not_literal_expr1 d = evaluate_word_bitwise_not_literal_expr2 d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def word_bitwise_not_def)

abbreviation evaluate_word_shift_left_literal_expr1 where
  \<open>evaluate_word_shift_left_literal_expr1 c d \<equiv>
    word_shift_left_shift64 (literal c) (literal d)\<close>

abbreviation evaluate_word_shift_left_literal_expr2 where
  \<open>evaluate_word_shift_left_literal_expr2 d c \<equiv>
    literal (push_bit (unat d) c)\<close>

lemma evaluate_word_shift_left_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>evaluate_word_shift_left_literal_expr1 c d =
    evaluate_word_shift_left_literal_expr2 d c\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_left_def 
    word_shift_left_shift64_def
    word_shift_left_pure_def word_shift_left_core_def word_shift_left_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

abbreviation evaluate_word_shift_right_literal_expr1 where
  \<open>evaluate_word_shift_right_literal_expr1 c d \<equiv>
    word_shift_right_shift64 (literal c) (literal d)\<close>

abbreviation evaluate_word_shift_right_literal_expr2 where
  \<open>evaluate_word_shift_right_literal_expr2 d c \<equiv>
    literal (drop_bit (unat d) c)\<close>

lemma evaluate_word_shift_right_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>evaluate_word_shift_right_literal_expr1 c d =
    evaluate_word_shift_right_literal_expr2 d c\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_right_def 
    word_shift_right_shift64_def
    word_shift_right_pure_def word_shift_right_core_def word_shift_right_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

(*<*)
end
(*>*)
