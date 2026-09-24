(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types_Lemmas
  imports Core_Expression_Lemmas Numeric_Types
begin
(*>*)

lemma evaluate_lt_literal [micro_rust_simps]:
  shows \<open>comp_lt (literal c) (literal d) = literal (c < d)\<close>
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

lemma evaluate_gt_literal [micro_rust_simps]:
  shows \<open>comp_gt (literal c) (literal d) = literal (c > d)\<close>
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

lemma evaluate_ge_literal [micro_rust_simps]:
  shows \<open>comp_ge (literal c) (literal d) = literal (c \<ge> d)\<close>
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

lemma evaluate_le_literal [micro_rust_simps]:
  shows \<open>comp_le (literal c) (literal d) = literal (c \<le> d)\<close>
  by (clarsimp simp add: micro_rust_simps comp_le_def)

lemma evaluate_word_bitwise_or_literal [micro_rust_simps]:
  shows \<open>word_bitwise_or (literal c) (literal d) = literal (c OR d)\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def word_bitwise_or_def)

lemma evaluate_word_bitwise_xor_literal [micro_rust_simps]:
  shows \<open>word_bitwise_xor (literal c) (literal d) = literal (c XOR d)\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

lemma evaluate_word_bitwise_and_literal [micro_rust_simps]:
  shows \<open>word_bitwise_and (literal c) (literal d) = literal (c AND d)\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

lemma evaluate_word_bitwise_not_literal [micro_rust_simps]:
  shows \<open>word_bitwise_not (literal d) = literal (NOT d)\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def word_bitwise_not_def)

lemma evaluate_word_shift_left_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>word_shift_left_shift64 (literal c) (literal d) =
    literal (push_bit (unat d) c)\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_left_def 
    word_shift_left_shift64_def
    word_shift_left_pure_def word_shift_left_core_def word_shift_left_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

lemma evaluate_word_shift_right_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>word_shift_right_shift64 (literal c) (literal d) =
    literal (drop_bit (unat d) c)\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_right_def 
    word_shift_right_shift64_def
    word_shift_right_pure_def word_shift_right_core_def word_shift_right_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

(*<*)
end
(*>*)
