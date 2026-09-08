(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types_Lemmas
  imports Core_Expression_Lemmas Shallow_Micro_Rust_Base.Numeric_Types
begin
(*>*)

lemma evaluate_lt_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>c < d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

lemma evaluate_gt_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c > d \<rbrakk> = \<lbrakk> \<llangle>c > d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

lemma evaluate_ge_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c >= d \<rbrakk> = \<lbrakk> \<llangle>c \<ge> d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

lemma evaluate_le_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c <= d \<rbrakk> = \<lbrakk> \<llangle>c \<le> d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_le_def)

lemma evaluate_word_bitwise_or_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c | d \<rbrakk> = \<lbrakk> \<llangle>c OR d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def word_bitwise_or_def)

lemma evaluate_word_bitwise_xor_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c ^ d \<rbrakk> = \<lbrakk> \<llangle>c XOR d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

lemma evaluate_word_bitwise_and_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c & d \<rbrakk> = \<lbrakk> \<llangle>c AND d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

lemma evaluate_word_bitwise_not_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> !d \<rbrakk> = \<lbrakk> \<llangle>NOT d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def word_bitwise_not_def)

lemma evaluate_word_shift_left_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>\<lbrakk> c << d \<rbrakk> = \<lbrakk> \<llangle>push_bit (unat d) c\<rrangle> \<rbrakk>\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_left_def 
    word_shift_left_shift64_def
    word_shift_left_pure_def word_shift_left_core_def word_shift_left_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

lemma evaluate_word_shift_right_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>\<lbrakk> c >> d \<rbrakk> = \<lbrakk> \<llangle>drop_bit (unat d) c\<rrangle> \<rbrakk>\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_right_def 
    word_shift_right_shift64_def
    word_shift_right_pure_def word_shift_right_core_def word_shift_right_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

(*<*)
end
(*>*)
