(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types_Lemmas
  imports Core_Expression_Lemmas Shallow_Micro_Rust_Base.Numeric_Types
begin
declare [[urust_conformance_check = true]]
(*>*)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_1
  \<open> c < d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_2
  \<open> \<llangle>c < d\<rrangle> \<close>
  with_args c d

lemma evaluate_lt_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_1 c d = Numeric_Types_Lemmas_urust_site_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_3
  \<open> c > d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_4
  \<open> \<llangle>c > d\<rrangle> \<close>
  with_args c d

lemma evaluate_gt_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_3 c d = Numeric_Types_Lemmas_urust_site_4 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_5
  \<open> c >= d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_6
  \<open> \<llangle>c \<ge> d\<rrangle> \<close>
  with_args c d

lemma evaluate_ge_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_5 c d = Numeric_Types_Lemmas_urust_site_6 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_7
  \<open> c <= d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_8
  \<open> \<llangle>c \<le> d\<rrangle> \<close>
  with_args c d

lemma evaluate_le_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_7 c d = Numeric_Types_Lemmas_urust_site_8 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_le_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_9
  \<open> c | d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_10
  \<open> \<llangle>c OR d\<rrangle> \<close>
  with_args c d

lemma evaluate_word_bitwise_or_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_9 c d = Numeric_Types_Lemmas_urust_site_10 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def word_bitwise_or_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_11
  \<open> c ^ d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_12
  \<open> \<llangle>c XOR d\<rrangle> \<close>
  with_args c d

lemma evaluate_word_bitwise_xor_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_11 c d = Numeric_Types_Lemmas_urust_site_12 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_13
  \<open> c & d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_14
  \<open> \<llangle>c AND d\<rrangle> \<close>
  with_args c d

lemma evaluate_word_bitwise_and_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_13 c d = Numeric_Types_Lemmas_urust_site_14 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_15 ::
  \<open>'l::len word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> !d \<close>
  with_args d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_16
  \<open> \<llangle>NOT d\<rrangle> \<close>
  with_args d

lemma evaluate_word_bitwise_not_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_15 d = Numeric_Types_Lemmas_urust_site_16 d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def word_bitwise_not_def)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_17
  \<open> c << d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_18
  \<open> \<llangle>push_bit (unat d) c\<rrangle> \<close>
  with_args d c

lemma evaluate_word_shift_left_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>Numeric_Types_Lemmas_urust_site_17 c d =
    Numeric_Types_Lemmas_urust_site_18 d c\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_left_def 
    word_shift_left_shift64_def
    word_shift_left_pure_def word_shift_left_core_def word_shift_left_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_19
  \<open> c >> d \<close>
  with_args c d

urust_expr [urust_abbrev = true] Numeric_Types_Lemmas_urust_site_20
  \<open> \<llangle>drop_bit (unat d) c\<rrangle> \<close>
  with_args d c

lemma evaluate_word_shift_right_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>Numeric_Types_Lemmas_urust_site_19 c d =
    Numeric_Types_Lemmas_urust_site_20 d c\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_right_def 
    word_shift_right_shift64_def
    word_shift_right_pure_def word_shift_right_core_def word_shift_right_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

(*<*)
end
(*>*)
