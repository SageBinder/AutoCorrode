(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types_Lemmas
  imports Core_Expression_Lemmas Shallow_Micro_Rust_Base.Numeric_Types
begin
declare [[urust_conformance_check = true]]
(*>*)

abbreviation Numeric_Types_Lemmas_urust_site_1 where
  "Numeric_Types_Lemmas_urust_site_1 c d \<equiv> \<mu>(c := c, d := d)\<open> c < d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_2 where
  "Numeric_Types_Lemmas_urust_site_2 c d \<equiv>
    \<mu>(value := c < d)\<open> value \<close>"

lemma evaluate_lt_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_1 c d = Numeric_Types_Lemmas_urust_site_2 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

abbreviation Numeric_Types_Lemmas_urust_site_3 where
  "Numeric_Types_Lemmas_urust_site_3 c d \<equiv> \<mu>(c := c, d := d)\<open> c > d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_4 where
  "Numeric_Types_Lemmas_urust_site_4 c d \<equiv>
    \<mu>(value := c > d)\<open> value \<close>"

lemma evaluate_gt_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_3 c d = Numeric_Types_Lemmas_urust_site_4 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

abbreviation Numeric_Types_Lemmas_urust_site_5 where
  "Numeric_Types_Lemmas_urust_site_5 c d \<equiv> \<mu>(c := c, d := d)\<open> c >= d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_6 where
  "Numeric_Types_Lemmas_urust_site_6 c d \<equiv>
    \<mu>(value := c \<ge> d)\<open> value \<close>"

lemma evaluate_ge_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_5 c d = Numeric_Types_Lemmas_urust_site_6 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

abbreviation Numeric_Types_Lemmas_urust_site_7 where
  "Numeric_Types_Lemmas_urust_site_7 c d \<equiv> \<mu>(c := c, d := d)\<open> c <= d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_8 where
  "Numeric_Types_Lemmas_urust_site_8 c d \<equiv>
    \<mu>(value := c \<le> d)\<open> value \<close>"

lemma evaluate_le_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_7 c d = Numeric_Types_Lemmas_urust_site_8 c d\<close>
  by (clarsimp simp add: micro_rust_simps comp_le_def)

abbreviation Numeric_Types_Lemmas_urust_site_9 where
  "Numeric_Types_Lemmas_urust_site_9 c d \<equiv> \<mu>(c := c, d := d)\<open> c | d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_10 where
  "Numeric_Types_Lemmas_urust_site_10 c d \<equiv>
    \<mu>(value := c OR d)\<open> value \<close>"

lemma evaluate_word_bitwise_or_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_9 c d = Numeric_Types_Lemmas_urust_site_10 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def word_bitwise_or_def)

abbreviation Numeric_Types_Lemmas_urust_site_11 where
  "Numeric_Types_Lemmas_urust_site_11 c d \<equiv> \<mu>(c := c, d := d)\<open> c ^ d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_12 where
  "Numeric_Types_Lemmas_urust_site_12 c d \<equiv>
    \<mu>(value := c XOR d)\<open> value \<close>"

lemma evaluate_word_bitwise_xor_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_11 c d = Numeric_Types_Lemmas_urust_site_12 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

abbreviation Numeric_Types_Lemmas_urust_site_13 where
  "Numeric_Types_Lemmas_urust_site_13 c d \<equiv> \<mu>(c := c, d := d)\<open> c & d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_14 where
  "Numeric_Types_Lemmas_urust_site_14 c d \<equiv>
    \<mu>(value := c AND d)\<open> value \<close>"

lemma evaluate_word_bitwise_and_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_13 c d = Numeric_Types_Lemmas_urust_site_14 c d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

abbreviation Numeric_Types_Lemmas_urust_site_15 ::
  \<open>'l::len word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close>
  where
  "Numeric_Types_Lemmas_urust_site_15 d \<equiv>
    \<mu>(d := d)\<open> !d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_16 where
  "Numeric_Types_Lemmas_urust_site_16 d \<equiv>
    \<mu>(value := NOT d)\<open> value \<close>"

lemma evaluate_word_bitwise_not_literal [micro_rust_simps]:
  shows \<open>Numeric_Types_Lemmas_urust_site_15 d = Numeric_Types_Lemmas_urust_site_16 d\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def word_bitwise_not_def)

abbreviation Numeric_Types_Lemmas_urust_site_17 where
  "Numeric_Types_Lemmas_urust_site_17 c d \<equiv> \<mu>(c := c, d := d)\<open> c << d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_18 where
  "Numeric_Types_Lemmas_urust_site_18 d c \<equiv>
    \<mu>(value := push_bit (unat d) c)\<open> value \<close>"

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

abbreviation Numeric_Types_Lemmas_urust_site_19 where
  "Numeric_Types_Lemmas_urust_site_19 c d \<equiv> \<mu>(c := c, d := d)\<open> c >> d \<close>"

abbreviation Numeric_Types_Lemmas_urust_site_20 where
  "Numeric_Types_Lemmas_urust_site_20 d c \<equiv>
    \<mu>(value := drop_bit (unat d) c)\<open> value \<close>"

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
