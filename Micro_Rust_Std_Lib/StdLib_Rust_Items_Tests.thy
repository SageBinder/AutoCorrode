(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Rust_Items_Tests
  imports StdLib_Arithmetic
begin
(*>*)

section\<open>Tests for the primitive bounds and the \<^verbatim>\<open>NonZeroU64\<close> type mapping\<close>

declare [[urust_pp_test = true]]

subsection\<open>Primitive integer bounds\<close>

text\<open>Every bound resolves through its primitive path head to the library constant.\<close>

urust_expr stdlib_u8_min \<open> u8::MIN \<close>
urust_expr stdlib_u8_max \<open> u8::MAX \<close>
urust_expr stdlib_u16_min \<open> u16::MIN \<close>
urust_expr stdlib_u16_max \<open> u16::MAX \<close>
urust_expr stdlib_u32_min \<open> u32::MIN \<close>
urust_expr stdlib_u32_max \<open> u32::MAX \<close>
urust_expr stdlib_u64_min \<open> u64::MIN \<close>
urust_expr stdlib_u64_max \<open> u64::MAX \<close>
urust_expr stdlib_usize_min \<open> usize::MIN \<close>
urust_expr stdlib_usize_max \<open> usize::MAX \<close>
urust_expr stdlib_i32_min \<open> i32::MIN \<close>
urust_expr stdlib_i32_max \<open> i32::MAX \<close>
urust_expr stdlib_i64_min \<open> i64::MIN \<close>
urust_expr stdlib_i64_max \<open> i64::MAX \<close>

lemma stdlib_bound_paths:
  shows \<open> stdlib_u8_min = literal u8_min \<close>
    and \<open> stdlib_u8_max = literal u8_max \<close>
    and \<open> stdlib_u16_min = literal u16_min \<close>
    and \<open> stdlib_u16_max = literal u16_max \<close>
    and \<open> stdlib_u32_min = literal u32_min \<close>
    and \<open> stdlib_u32_max = literal u32_max \<close>
    and \<open> stdlib_u64_min = literal u64_min \<close>
    and \<open> stdlib_u64_max = literal u64_max \<close>
    and \<open> stdlib_usize_min = literal usize_min \<close>
    and \<open> stdlib_usize_max = literal usize_max \<close>
    and \<open> stdlib_i32_min = literal i32_min \<close>
    and \<open> stdlib_i32_max = literal i32_max \<close>
    and \<open> stdlib_i64_min = literal i64_min \<close>
    and \<open> stdlib_i64_max = literal i64_max \<close>
  unfolding stdlib_u8_min_def stdlib_u8_max_def stdlib_u16_min_def stdlib_u16_max_def
    stdlib_u32_min_def stdlib_u32_max_def stdlib_u64_min_def stdlib_u64_max_def
    stdlib_usize_min_def stdlib_usize_max_def stdlib_i32_min_def stdlib_i32_max_def
    stdlib_i64_min_def stdlib_i64_max_def
  by (rule refl)+

text\<open>The bounds have Rust's values: unsigned bounds as unsigned and signed bounds as signed
integers.\<close>

lemma stdlib_unsigned_bound_values:
  shows \<open> unat u8_min = 0 \<close> and \<open> unat u8_max = 2 ^ 8 - 1 \<close>
    and \<open> unat u16_min = 0 \<close> and \<open> unat u16_max = 2 ^ 16 - 1 \<close>
    and \<open> unat u32_min = 0 \<close> and \<open> unat u32_max = 2 ^ 32 - 1 \<close>
    and \<open> unat u64_min = 0 \<close> and \<open> unat u64_max = 2 ^ 64 - 1 \<close>
    and \<open> unat usize_min = 0 \<close> and \<open> unat usize_max = 2 ^ 64 - 1 \<close>
  by (simp_all add: u8_min_def u8_max_def u16_min_def u16_max_def u32_min_def u32_max_def
    u64_min_def u64_max_def usize_min_def usize_max_def unat_minus_one_word)

lemma stdlib_signed_bound_values:
  shows \<open> sint i32_min = - (2 ^ 31) \<close> and \<open> sint i32_max = 2 ^ 31 - 1 \<close>
    and \<open> sint i64_min = - (2 ^ 63) \<close> and \<open> sint i64_max = 2 ^ 63 - 1 \<close>
  by (simp_all add: i32_min_def i32_max_def i64_min_def i64_max_def)

text\<open>Bounds take part in ordinary expressions, casts and patterns.\<close>

urust_expr stdlib_bound_cast \<open> u8::MAX as u64 \<close>

urust_expr stdlib_bound_cast_literal \<open> 255u8 as u64 \<close>

lemma stdlib_bound_cast_value:
  shows \<open> stdlib_bound_cast = stdlib_bound_cast_literal \<close>
proof -
  have \<open> u8_max = 0xFF \<close>
    by (simp add: u8_max_def)
  then show ?thesis
    unfolding stdlib_bound_cast_def stdlib_bound_cast_literal_def
    by (simp only:)
qed

urust_expr stdlib_bound_pattern (bits) \<open>
  match bits {
    u64::MAX => true,
    _ => false,
  }
\<close>

ML_val \<open>
  @{assert}
    (exists_Const (fn (name, _) => name = \<^const_name>\<open>u64_max\<close>)
      (Thm.prop_of @{thm stdlib_bound_pattern_def}))
\<close>

subsection\<open>The \<^verbatim>\<open>NonZeroU64\<close> type mapping\<close>

text\<open>Each mapped signature is identical to the same function written with HOL type escapes.\<close>

urust_fn \<open>
  fn stdlib_nonzero_identity(value: NonZeroU64) -> NonZeroU64 { value }
\<close>

urust_fn \<open>
  fn stdlib_nonzero_identity_escaped(value: \<tau>\<open>nonzero_u64\<close>) -> \<tau>\<open>nonzero_u64\<close> {
    value
  }
\<close>

lemma stdlib_nonzero_identity_same:
  shows \<open> stdlib_nonzero_identity = stdlib_nonzero_identity_escaped \<close>
  unfolding stdlib_nonzero_identity_def stdlib_nonzero_identity_escaped_def
  by (rule refl)

urust_fn \<open>
  fn stdlib_nonzero_nested(value: Option<(NonZeroU64, u64)>) -> Result<NonZeroU64, ()> {
    match value {
      Some((nonzero, _)) => Ok(nonzero),
      None => Err(()),
    }
  }
\<close>

urust_fn \<open>
  fn stdlib_nonzero_nested_escaped(value: \<tau>\<open>(nonzero_u64 \<times> 64 word \<times> tnil) option\<close>)
    -> \<tau>\<open>(nonzero_u64, unit) result\<close> {
    match value {
      Some((nonzero, _)) => Ok(nonzero),
      None => Err(()),
    }
  }
\<close>

lemma stdlib_nonzero_nested_same:
  shows \<open> stdlib_nonzero_nested = stdlib_nonzero_nested_escaped \<close>
  unfolding stdlib_nonzero_nested_def stdlib_nonzero_nested_escaped_def
  by (rule refl)

(*<*)
end
(*>*)
