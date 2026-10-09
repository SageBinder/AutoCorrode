theory Parser_Primitive_Path_Heads_Tests
  imports
    Parser_Array_Repeats_Tests
    Parser_Improvements_Tests
begin

section\<open> Primitive-type path heads \<close>

declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]

definition primitive_head_u8_max :: \<open> 8 word \<close>
  where \<open> primitive_head_u8_max = 7 \<close>

definition primitive_head_u16_max :: \<open> 16 word \<close>
  where \<open> primitive_head_u16_max = 17 \<close>

definition primitive_head_u32_max :: \<open> 32 word \<close>
  where \<open> primitive_head_u32_max = 37 \<close>

definition primitive_head_u64_max :: \<open> 64 word \<close>
  where \<open> primitive_head_u64_max = 67 \<close>

definition primitive_head_usize_max :: \<open> 64 word \<close>
  where \<open> primitive_head_usize_max = 3 \<close>

definition primitive_head_i32_max :: \<open> 32 word \<close>
  where \<open> primitive_head_i32_max = 47 \<close>

definition primitive_head_i64_max :: \<open> 64 word \<close>
  where \<open> primitive_head_i64_max = 79 \<close>

definition primitive_head_u64_min :: \<open> 64 word \<close>
  where \<open> primitive_head_u64_min = 0 \<close>

definition primitive_head_flag :: bool
  where \<open> primitive_head_flag = True \<close>

definition primitive_head_option :: \<open> 64 word option \<close>
  where \<open> primitive_head_option = Some 11 \<close>

definition primitive_head_values :: \<open> 64 word list \<close>
  where \<open> primitive_head_values = [13, 17] \<close>

definition primitive_head_pair :: \<open> 64 word \<times> 64 word \<close>
  where \<open> primitive_head_pair = (19, 23) \<close>

datatype_record primitive_head_record =
  primitive_head_record_value :: \<open> 64 word \<close>
micro_rust_record primitive_head_record

definition primitive_head_record_constant :: primitive_head_record
  where \<open> primitive_head_record_constant = make_primitive_head_record 29 \<close>

definition primitive_head_zero ::
    \<open> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_zero = lift_fun0 0 \<close>

definition primitive_head_from ::
    \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_from = lift_fun1 id \<close>

definition primitive_head_combine ::
    \<open> 64 word \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_combine = lift_fun2 (+) \<close>

definition primitive_head_bump ::
    \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_bump = lift_fun1 (\<lambda>x. x + 1) \<close>

definition primitive_head_dual_literal :: \<open> 64 word \<close>
  where \<open> primitive_head_dual_literal = 31 \<close>

definition primitive_head_dual_call ::
    \<open> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_dual_call = lift_fun0 31 \<close>

definition primitive_head_ambiguous_left :: \<open> 64 word \<close>
  where \<open> primitive_head_ambiguous_left = 41 \<close>

definition primitive_head_ambiguous_right :: \<open> 64 word \<close>
  where \<open> primitive_head_ambiguous_right = 43 \<close>

datatype primitive_head_constructor_backend =
  PrimitiveHeadConstructor

micro_rust_notation (literal) primitive_head_u8_max ("u8::MAX")
micro_rust_notation (literal) primitive_head_u16_max ("u16::MAX")
micro_rust_notation (literal) primitive_head_u32_max ("u32::MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u64::MAX")
micro_rust_notation (literal) primitive_head_usize_max ("usize::MAX")
micro_rust_notation (literal) primitive_head_i32_max ("i32::MAX")
micro_rust_notation (literal) primitive_head_i64_max ("i64::MAX")
micro_rust_notation (literal) primitive_head_u64_min ("u64::MIN")
micro_rust_notation (literal) primitive_head_flag ("u64::FLAG")
micro_rust_notation (literal) primitive_head_option ("u64::OPTION")
micro_rust_notation (literal) primitive_head_values ("u64::VALUES")
micro_rust_notation (literal) primitive_head_pair ("u64::PAIR")
micro_rust_notation (literal)
  primitive_head_record_constant ("u64::RECORD")
urust_notation (literal)
  primitive_head_u64_max ("u64::Nested::MAX")

micro_rust_notation (call) primitive_head_zero ("u64::zero")
micro_rust_notation (call) primitive_head_from ("u64::from")
micro_rust_notation (call) primitive_head_combine ("u64::combine")
micro_rust_notation (call)
  primitive_head_from ("u64::from::<PrimitiveParam>")
micro_rust_notation (call) primitive_head_bump ("primitive_head_bump")

micro_rust_notation (literal)
  primitive_head_dual_literal ("u64::DUAL")
micro_rust_notation (call)
  primitive_head_dual_call ("u64::DUAL")

micro_rust_notation (literal)
  primitive_head_ambiguous_left ("u64::AMBIGUOUS")
micro_rust_notation (literal)
  primitive_head_ambiguous_right ("u64::AMBIGUOUS")

micro_rust_notation (literal)
  PrimitiveHeadConstructor ("u64::CONSTRUCTOR_VALUE")

micro_rust_notation (literal)
  primitive_head_u8_max ("PrimitiveCompat::U8Max")
micro_rust_notation (literal)
  primitive_head_u16_max ("PrimitiveCompat::U16Max")
micro_rust_notation (literal)
  primitive_head_u32_max ("PrimitiveCompat::U32Max")
micro_rust_notation (literal)
  primitive_head_u64_max ("PrimitiveCompat::U64Max")
micro_rust_notation (literal)
  primitive_head_usize_max ("PrimitiveCompat::UsizeMax")
micro_rust_notation (literal)
  primitive_head_i32_max ("PrimitiveCompat::I32Max")
micro_rust_notation (literal)
  primitive_head_i64_max ("PrimitiveCompat::I64Max")
micro_rust_notation (literal)
  primitive_head_u64_min ("PrimitiveCompat::U64Min")
micro_rust_notation (call)
  primitive_head_zero ("PrimitiveCompat::zero")
micro_rust_notation (call)
  primitive_head_from ("PrimitiveCompat::convert")
micro_rust_notation (call)
  primitive_head_combine ("PrimitiveCompat::combine")
micro_rust_notation (call)
  primitive_head_from ("PrimitiveCompat::convert::<PrimitiveParam>")
micro_rust_notation (literal)
  primitive_head_dual_literal ("PrimitiveCompat::DUAL")
micro_rust_notation (call)
  primitive_head_dual_call ("PrimitiveCompat::DUAL")

micro_rust_notation (literal) primitive_head_u64_max ("u64_MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u64x::MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u64x'::MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u128::MAX")

bundle primitive_path_cast_aliases begin
  urust_type_alias \<open> type PrimitivePathAlias = u64; \<close>
end

subsection\<open> Exact literal and call resolution \<close>

urust_expr primitive_path_u8 \<open> u8::MAX \<close>

urust_expr primitive_path_u8_compat
  \<open> PrimitiveCompat::U8Max \<close>

lemma primitive_path_u8_equal:
  \<open> primitive_path_u8 = primitive_path_u8_compat \<close>
  unfolding primitive_path_u8_def primitive_path_u8_compat_def
  by (rule refl)

urust_expr primitive_path_u16 \<open> u16::MAX \<close>

urust_expr primitive_path_u16_compat
  \<open> PrimitiveCompat::U16Max \<close>

lemma primitive_path_u16_equal:
  \<open> primitive_path_u16 = primitive_path_u16_compat \<close>
  unfolding primitive_path_u16_def primitive_path_u16_compat_def
  by (rule refl)

urust_expr primitive_path_u32 \<open> u32::MAX \<close>

urust_expr primitive_path_u32_compat
  \<open> PrimitiveCompat::U32Max \<close>

lemma primitive_path_u32_equal:
  \<open> primitive_path_u32 = primitive_path_u32_compat \<close>
  unfolding primitive_path_u32_def primitive_path_u32_compat_def
  by (rule refl)

urust_expr primitive_path_u64 \<open> u64::MAX \<close>

urust_expr primitive_path_u64_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_u64_equal:
  \<open> primitive_path_u64 = primitive_path_u64_compat \<close>
  unfolding primitive_path_u64_def primitive_path_u64_compat_def
  by (rule refl)

urust_expr primitive_path_usize \<open> usize::MAX \<close>

urust_expr primitive_path_usize_compat
  \<open> PrimitiveCompat::UsizeMax \<close>

lemma primitive_path_usize_equal:
  \<open> primitive_path_usize = primitive_path_usize_compat \<close>
  unfolding primitive_path_usize_def primitive_path_usize_compat_def
  by (rule refl)

urust_expr primitive_path_i32 \<open> i32::MAX \<close>

urust_expr primitive_path_i32_compat
  \<open> PrimitiveCompat::I32Max \<close>

lemma primitive_path_i32_equal:
  \<open> primitive_path_i32 = primitive_path_i32_compat \<close>
  unfolding primitive_path_i32_def primitive_path_i32_compat_def
  by (rule refl)

urust_expr primitive_path_i64 \<open> i64::MAX \<close>

urust_expr primitive_path_i64_compat
  \<open> PrimitiveCompat::I64Max \<close>

lemma primitive_path_i64_equal:
  \<open> primitive_path_i64 = primitive_path_i64_compat \<close>
  unfolding primitive_path_i64_def primitive_path_i64_compat_def
  by (rule refl)

urust_expr primitive_path_call_zero \<open> u64::zero() \<close>

urust_expr primitive_path_call_zero_compat
  \<open> PrimitiveCompat::zero() \<close>

lemma primitive_path_call_zero_equal:
  \<open> primitive_path_call_zero = primitive_path_call_zero_compat \<close>
  unfolding primitive_path_call_zero_def primitive_path_call_zero_compat_def
  by (rule refl)

urust_expr primitive_path_call_one \<open> u64::from(5u64) \<close>

urust_expr primitive_path_call_one_compat
  \<open> PrimitiveCompat::convert(5_u64) \<close>

lemma primitive_path_call_one_equal:
  \<open> primitive_path_call_one = primitive_path_call_one_compat \<close>
  unfolding primitive_path_call_one_def primitive_path_call_one_compat_def
  by (rule refl)

urust_expr primitive_path_call_multiple
  \<open> u64::combine(5u64, 7u64) \<close>

urust_expr primitive_path_call_multiple_compat
  \<open> PrimitiveCompat::combine(5_u64, 7_u64) \<close>

lemma primitive_path_call_multiple_equal:
  \<open> primitive_path_call_multiple = primitive_path_call_multiple_compat \<close>
  unfolding primitive_path_call_multiple_def primitive_path_call_multiple_compat_def
  by (rule refl)

urust_expr primitive_path_call_turbofish
  \<open> u64::from::<PrimitiveParam>(5u64) \<close>

urust_expr primitive_path_call_turbofish_compat
  \<open> PrimitiveCompat::convert::<PrimitiveParam>(5_u64) \<close>

lemma primitive_path_call_turbofish_equal:
  \<open> primitive_path_call_turbofish = primitive_path_call_turbofish_compat \<close>
  unfolding primitive_path_call_turbofish_def primitive_path_call_turbofish_compat_def
  by (rule refl)

urust_expr primitive_path_dual_literal \<open> u64::DUAL \<close>

urust_expr primitive_path_dual_literal_compat
  \<open> PrimitiveCompat::DUAL \<close>

lemma primitive_path_dual_literal_equal:
  \<open> primitive_path_dual_literal = primitive_path_dual_literal_compat \<close>
  unfolding primitive_path_dual_literal_def primitive_path_dual_literal_compat_def
  by (rule refl)

urust_expr primitive_path_dual_call \<open> u64::DUAL() \<close>

urust_expr primitive_path_dual_call_compat
  \<open> PrimitiveCompat::DUAL() \<close>

lemma primitive_path_dual_call_equal:
  \<open> primitive_path_dual_call = primitive_path_dual_call_compat \<close>
  unfolding primitive_path_dual_call_def primitive_path_dual_call_compat_def
  by (rule refl)


subsection\<open> Layout and lexical boundaries \<close>

urust_expr primitive_path_spaces \<open> u64 :: MAX \<close>

urust_expr primitive_path_spaces_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_spaces_equal:
  \<open> primitive_path_spaces = primitive_path_spaces_compat \<close>
  unfolding primitive_path_spaces_def primitive_path_spaces_compat_def
  by (rule refl)

urust_expr primitive_path_newlines
  \<open>
    u64
      ::
    MAX
  \<close>

urust_expr primitive_path_newlines_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_newlines_equal:
  \<open> primitive_path_newlines = primitive_path_newlines_compat \<close>
  unfolding primitive_path_newlines_def primitive_path_newlines_compat_def
  by (rule refl)

urust_expr primitive_path_line_comment
  \<open>
    u64 // before separator
      :: // before item
    MAX
  \<close>

urust_expr primitive_path_line_comment_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_line_comment_equal:
  \<open> primitive_path_line_comment = primitive_path_line_comment_compat \<close>
  unfolding primitive_path_line_comment_def primitive_path_line_comment_compat_def
  by (rule refl)

urust_expr primitive_path_block_comment
  \<open> u64 /* outer /* nested */ comment */ :: MAX \<close>

urust_expr primitive_path_block_comment_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_block_comment_equal:
  \<open> primitive_path_block_comment = primitive_path_block_comment_compat \<close>
  unfolding primitive_path_block_comment_def primitive_path_block_comment_compat_def
  by (rule refl)

urust_expr primitive_path_formal_comment
  \<open>
    u64
      \<comment> \<open> formal layout with \<^term>\<open>True\<close>\<close>
      ::
      MAX
  \<close>

urust_expr primitive_path_formal_comment_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_formal_comment_equal:
  \<open> primitive_path_formal_comment = primitive_path_formal_comment_compat \<close>
  unfolding primitive_path_formal_comment_def primitive_path_formal_comment_compat_def
  by (rule refl)

urust_expr primitive_path_identifier_boundary \<open> u64_MAX \<close>

urust_expr primitive_path_identifier_boundary_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_identifier_boundary_equal:
  \<open> primitive_path_identifier_boundary = primitive_path_identifier_boundary_compat \<close>
  unfolding primitive_path_identifier_boundary_def primitive_path_identifier_boundary_compat_def
  by (rule refl)

urust_expr primitive_path_identifier_prefix \<open> u64x::MAX \<close>

urust_expr primitive_path_identifier_prefix_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_identifier_prefix_equal:
  \<open> primitive_path_identifier_prefix = primitive_path_identifier_prefix_compat \<close>
  unfolding primitive_path_identifier_prefix_def primitive_path_identifier_prefix_compat_def
  by (rule refl)

urust_expr primitive_path_apostrophe \<open> u64x'::MAX \<close>

urust_expr primitive_path_apostrophe_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_apostrophe_equal:
  \<open> primitive_path_apostrophe = primitive_path_apostrophe_compat \<close>
  unfolding primitive_path_apostrophe_def primitive_path_apostrophe_compat_def
  by (rule refl)

urust_expr primitive_path_unsupported_width \<open> u128::MAX \<close>

urust_expr primitive_path_unsupported_width_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_unsupported_width_equal:
  \<open> primitive_path_unsupported_width = primitive_path_unsupported_width_compat \<close>
  unfolding primitive_path_unsupported_width_def primitive_path_unsupported_width_compat_def
  by (rule refl)

urust_expr_rejects \<open> u64 \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64:: \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64::::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64:::::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64::u8 \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> Module::u64::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects
  \<open> u64::<PrimitiveParam>::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects
  \<open> u64::from::<>() \<close> \<open> syntax error \<close>
urust_expr_rejects
  \<open> u64::from::<PrimitiveParam,>() \<close> \<open> syntax error \<close>

subsection\<open> Expression composition \<close>

urust_expr primitive_path_prefix \<open> !u64::MAX \<close>
urust_expr primitive_path_dereference \<open> *u64::MAX \<close>
urust_expr primitive_path_cast_u8 \<open> u64::MIN as u8 \<close>
urust_expr primitive_path_cast_u16 \<open> u64::MIN as u16 \<close>
urust_expr primitive_path_cast_u32 \<open> u64::MIN as u32 \<close>
urust_expr primitive_path_cast_u64 \<open> u8::MAX as u64 \<close>
urust_expr primitive_path_cast_usize \<open> u64::MIN as usize \<close>
urust_expr primitive_path_cast_i32 \<open> u64::MIN as i32 \<close>
urust_expr primitive_path_cast_i64 \<open> u64::MIN as i64 \<close>

context includes primitive_path_cast_aliases
begin

urust_expr primitive_path_named_cast_alias
  \<open> u8::MAX as PrimitivePathAlias \<close>

urust_expr primitive_path_named_cast_alias_compat
  \<open> PrimitiveCompat::U8Max as u64 \<close>

lemma primitive_path_named_cast_alias_equal:
  \<open> primitive_path_named_cast_alias = primitive_path_named_cast_alias_compat \<close>
  unfolding primitive_path_named_cast_alias_def primitive_path_named_cast_alias_compat_def
  by (rule refl)

end

urust_expr primitive_path_binary \<open> u64::MAX + 1u64 \<close>
urust_expr primitive_path_comparison \<open> u64::MIN < u64::MAX \<close>
urust_expr primitive_path_range \<open> u64::MIN..u64::MAX \<close>
urust_expr primitive_path_group \<open> (u64::MAX) \<close>
urust_expr primitive_path_block \<open> { u64::MAX } \<close>
urust_expr primitive_path_unsafe \<open> unsafe { u64::MAX } \<close>
urust_expr primitive_path_propagate \<open> u64::OPTION? \<close>
urust_expr primitive_path_field
  \<open> u64::RECORD.primitive_head_record_value \<close>
urust_expr primitive_path_method
  \<open> u64::MAX.primitive_head_bump() \<close>
urust_expr primitive_path_index \<open> u64::VALUES[0_usize] \<close>
urust_expr primitive_path_projection \<open> u64::PAIR.0 \<close>
urust_expr primitive_path_array \<open> [u64::MIN, u64::MAX] \<close>
urust_expr primitive_path_repeat
  \<open> [u64::MAX; usize::MAX] \<close>
urust_expr primitive_path_repeat_arithmetic
  \<open> [u64::MAX; usize::MAX + 1] \<close>
urust_expr primitive_path_macro_argument
  \<open> assert!(u64::MIN < u64::MAX) \<close>

urust_expr primitive_path_let
  \<open> let value = u64::MAX; value \<close>

urust_expr primitive_path_let_mut
  \<open> let mut value = u64::MAX; *value \<close>

urust_expr primitive_path_const
  \<open> const value = u64::MAX; value \<close>

urust_expr primitive_path_sequence
  \<open> u64::MIN; u64::MAX \<close>

urust_expr primitive_path_closure
  \<open> |value| value + u64::MAX \<close>

urust_expr primitive_path_return
  \<open> return u64::MAX \<close>

urust_expr primitive_path_if
  \<open> if u64::FLAG { u64::MAX } else { u64::MIN } \<close>

urust_expr primitive_path_if_let
  \<open>
    if let Some(value) = u64::OPTION {
      value
    } else {
      u64::MIN
    }
  \<close>

urust_expr primitive_path_if_let_constant
  \<open>
    if let u64::MAX = u64::MAX {
      true
    } else {
      false
    }
  \<close>

urust_expr primitive_path_for
  \<open> for value in u64::VALUES { let _ = value; () } \<close>

urust_expr primitive_path_while
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    while (u64::FLAG) { () }
  \<close>

urust_expr primitive_path_loop
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    loop { let value = u64::MAX; let _ = value; () }
  \<close>

urust_expr primitive_path_while_let
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    while let Some(value) = u64::OPTION {
      let _ = value;
      ()
    }
  \<close>

urust_expr primitive_path_while_let_constant
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    while let u64::MAX = u64::MAX { () }
  \<close>

urust_expr primitive_path_match
  \<open>
    match u64::MAX {
      u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_match_case
  \<open>
    match_case Some(u64::MAX) {
      Some(u64::MAX) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_match_switch
  \<open>
    match_switch u64::MAX {
      u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_semicolon_free_control
  \<open>
    if u64::FLAG { () }
    u64::MAX
  \<close>

subsection\<open> Pattern roles and place rejection \<close>

urust_expr primitive_path_tuple_pattern
  \<open>
    match_case (u64::MAX, Some(u64::MAX)) {
      (u64::MAX, Some(u64::MAX)) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_slice_pattern
  \<open>
    match_case [u64::MAX, u64::MIN] {
      [u64::MAX, _] \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_range_pattern
  \<open>
    match_case u64::MAX {
      u64::MIN..=u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_alias_pattern
  \<open>
    match_case u64::MAX {
      whole @ u64::MAX \<Rightarrow> whole,
      _ \<Rightarrow> u64::MIN
    }
  \<close>

urust_expr primitive_path_or_pattern
  \<open>
    match_case u64::MAX {
      u64::MIN | u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_guarded_pattern
  \<open>
    match_case u64::MAX {
      u64::MAX if u64::FLAG \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_matches_pattern
  \<open> matches!(u64::MAX, u64::MAX) \<close>

urust_expr_rejects
  \<open> let u64::MAX = u64::MAX; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> for u64::MAX in u64::VALUES { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> |u64::MAX| () \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::MAX = u64::MIN \<close>
  \<open> primitive associated-item path is not an assignment target \<close>

urust_expr_rejects
  \<open> u64::MAX { field: u64::MIN } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> match_case u64::MAX { u64::MAX { field: _ } \<Rightarrow> true } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> PrimitiveRecord { u64: u64::MAX } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::MAX.u64() \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> &u64::MAX \<close> \<open> no backend matches the use-site type \<close>

urust_expr_rejects
  \<open> *u64::MAX + true \<close> \<open> Unresolved adhoc overloading \<close>

subsection\<open> Exact-registration failures \<close>

urust_expr_rejects
  \<open> u64::MISSING \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> u64::MISSING() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

urust_expr_rejects
  \<open> u64::zero \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> u64::MAX() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

urust_expr_rejects
  \<open> u64::AMBIGUOUS \<close>
  \<open> Ambiguous uRust notation \<close>

urust_expr_rejects
  \<open> u64::MAX as u64::MAX \<close> \<open> syntax error \<close>

ML_val\<open>
  local
    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    val source_name = "primitive-headed-cast-alias-declaration"
    val result =
      Exn.result
        (run_command source_name
          ("urust_type_alias \"u64::PrimitiveAlias\" " ^ Symbol.open_ ^ " type PrimitiveAlias = u64; " ^ Symbol.close)) ()
    val _ =
      (case result of
         Exn.Res _ =>
           error
             "primitive-headed cast-target alias declaration was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               if String.isSubstring "reserved segment" message andalso
                  String.isSubstring source_name message
               then ()
               else
                 error
                   ("wrong primitive-headed cast-target alias diagnostic:\n" ^
                     message)
             end)
  in
    val _ = ()
  end
\<close>

urust_expr primitive_path_recovery_after_rejections
  \<open> u64::MAX \<close>

subsection\<open> AST, positions, markup, and recovery \<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "primitive path AST audit: empty parse")

    fun assert message condition =
      if condition then ()
      else error ("primitive path AST audit: " ^ message)

    fun names path =
      map (#1 o segment_identifier) (path_segments path)

    val _ =
      (case parse "u64::Nested::MAX" of
         UE_Path path =>
           (case path_head path of
              Primitive_Head (Primitive_Unsigned UT_U64) => ()
            | _ => error "primitive path AST audit: wrong primitive head";
            assert "segment order changed"
              (names path = ["u64", "Nested", "MAX"]);
            assert "canonical rendering changed"
              (render_path path = "u64::Nested::MAX"))
       | _ => error "primitive path AST audit: primitive value shape changed")

    val _ =
      (case parse "u64::from::<PrimitiveParam>(5u64)" of
         UE_Call (UC_Path path, [_], _) =>
           (assert "call head kind changed" (is_primitive_path path);
            assert "call canonical rendering changed"
              (render_path path =
                "u64::from::<PrimitiveParam>"))
       | _ => error "primitive path AST audit: primitive call shape changed")

    val _ =
      (case parse "u128::MAX" of
         UE_Path path =>
           (case path_head path of
              Identifier_Head => ()
            | _ =>
                error
                  "primitive path AST audit: unsupported width stopped being an identifier")
       | _ => error "primitive path AST audit: identifier boundary changed")

    val constructor_path =
      (case parse "u64::CONSTRUCTOR_VALUE" of
         UE_Path path => path
       | _ => error "primitive path AST audit: constructor-backed value shape changed")
    val constructor_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (path_position constructor_path)
    val _ =
      assert "constructor-backed primitive literal was not classified as a value"
        (URust_Resolution.classify_registered_literal ctxt
          constructor_resolver constructor_path =
            URust_Resolution.Registered_Value_Literal)
    val _ =
      assert "constructor fallback remained enabled for a primitive path"
        (is_none
          (URust_Resolution.resolve_constructor ctxt
            constructor_resolver constructor_path))

    val source_start =
      Position.make0 31 1000 0 "" ""
        "primitive-path-position-audit"
    val source =
      Parser_Lex_Util.positioned_content_source
        "u64::Nested::MAX" source_start
    val path =
      (case URust_Parser.parse_source ctxt source of
         SOME (UE_Path parsed) => parsed
       | _ => error "primitive path AST audit: positioned parse changed")
    val terminal_pos = #2 (segment_identifier (final_segment path))
    val _ =
      assert "complete path start changed"
        (Position.offset_of (path_position path) =
          Position.offset_of source_start)
    val _ =
      assert "complete path end changed"
        (Position.end_offset_of (path_position path) =
          Position.end_offset_of terminal_pos)
  in
    val _ = writeln "Primitive path AST and position audits passed"
  end
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then ()
      else error ("primitive path markup audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("primitive path markup audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun count_markup name position markup =
      length
        (filter
          (fn (candidate, properties) =>
            candidate = name andalso has_position properties position)
          markup)

    fun count_entity kind identity position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val text = "\<y>\<i>\<e>\<l>\<d>; u64::Nested::MAX"
    val start =
      Position.make0 37 1400 0 "" ""
        "primitive-path-markup-audit"
    val source =
      Parser_Lex_Util.positioned_content_source text start
    val captured =
      Synchronized.var "primitive_path_markup_reports" ([]: string list)
    fun capture chunks =
      Synchronized.change captured (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt source)) ())
          ())
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured)) []
    val (_, primitive_pos) =
      token_position text start "u64" 0
    val (first_separator_raw, first_separator_pos) =
      token_position text start "::" 0
    val (_, second_separator_pos) =
      token_position text start "::" (first_separator_raw + 2)
    val (_, nested_pos) =
      token_position text start "Nested" 0
    val (_, terminal_pos) =
      token_position text start "MAX" 0

    val _ =
      assert "primitive head lost keyword markup"
        (count_markup Markup.keyword1N primitive_pos markup = 1)
    val _ =
      assert "primitive head lost typing report"
        (count_markup Markup.typingN primitive_pos markup = 1)
    val _ =
      assert "primitive head gained free markup"
        (count_markup Markup.freeN primitive_pos markup = 0)
    val _ =
      assert "primitive head gained bound markup"
        (count_markup Markup.boundN primitive_pos markup = 0)
    val _ =
      assert "primitive head gained constructor styling"
        (count_markup Markup.keyword3N primitive_pos markup = 0)
    val _ =
      assert "primitive head gained notation navigation"
        (count_entity Micro_Rust_Names.notationN
          "u64::Nested::MAX" primitive_pos markup = 0)
    val _ =
      assert "first separator lost delimiter markup"
        (count_markup Markup.delimiterN first_separator_pos markup = 1)
    val _ =
      assert "second separator lost delimiter markup"
        (count_markup Markup.delimiterN second_separator_pos markup = 1)
    val _ =
      assert "registered continuation gained free markup"
        (count_markup Markup.freeN nested_pos markup = 0)
    val _ =
      assert "registered continuation lost notation navigation"
        (count_entity Micro_Rust_Names.notationN
          "u64::Nested::MAX" nested_pos markup = 1)
    val _ =
      assert "terminal lost notation navigation"
        (count_entity Micro_Rust_Names.notationN
          "u64::Nested::MAX" terminal_pos markup = 1)
    val _ =
      assert "terminal lost notation styling"
        (count_markup Markup.keyword3N terminal_pos markup = 1)

    fun checked source_text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source source_text)

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun range_of position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

    val failure_text =
      "\<y>\<i>\<e>\<l>\<d>; u64::UNREGISTERED"
    val failure_start =
      Position.make0 41 1800 0 "" ""
        "primitive-path-diagnostic-audit"
    val failure_source =
      Parser_Lex_Util.positioned_content_source
        failure_text failure_start
    val (_, failure_position) =
      token_position failure_text failure_start "UNREGISTERED" 0
    val failure =
      Exn.result
        (fn () =>
          Parser_Test_Elaboration.expression ctxt failure_source)
        ()
    val _ =
      (case failure of
         Exn.Res _ =>
           error "primitive path markup audit: missing registration unexpectedly succeeded"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
             in
               assert "missing-registration diagnostic changed"
                 (String.isSubstring
                   "requires an exact micro_rust_notation (literal) declaration"
                   (XML.content_of body));
               assert "missing-registration diagnostic range changed"
                 (diagnostic_ranges body =
                   [range_of failure_position])
             end)
    val recovered = checked "u64::MAX"
    val _ =
      assert "recovery after rejection changed"
        (Term.exists_subterm
          (fn Const (name, _) =>
                name = \<^const_name>\<open>primitive_head_u64_max\<close>
            | _ => false)
          recovered)
  in
    val _ =
      writeln "Primitive path markup and recovery audits passed"
  end
\<close>
subsection\<open> Exact generic paths and role boundaries \<close>

micro_rust_notation (call) primitive_head_zero ("u8::zero")
micro_rust_notation (call) primitive_head_zero ("u16::zero")
micro_rust_notation (call) primitive_head_zero ("u32::zero")
micro_rust_notation (call) primitive_head_zero ("usize::zero")
micro_rust_notation (call) primitive_head_zero ("i32::zero")
micro_rust_notation (call) primitive_head_zero ("i64::zero")

urust_expr primitive_path_all_call_heads
  \<open>
    (u8::zero(), u16::zero(), u32::zero(), u64::zero(),
     usize::zero(), i32::zero(), i64::zero())
  \<close>

urust_expr primitive_path_all_call_heads_compat
  \<open>
    (PrimitiveCompat::zero(), PrimitiveCompat::zero(), PrimitiveCompat::zero(),
     PrimitiveCompat::zero(), PrimitiveCompat::zero(), PrimitiveCompat::zero(),
     PrimitiveCompat::zero())
  \<close>

lemma primitive_path_all_call_heads_equal:
  \<open> primitive_path_all_call_heads = primitive_path_all_call_heads_compat \<close>
  unfolding primitive_path_all_call_heads_def primitive_path_all_call_heads_compat_def
  by (rule refl)

micro_rust_notation (literal)
  primitive_head_u64_max ("u64::Nested::<PrimitiveParam>::MAX")
micro_rust_notation (call)
  primitive_head_from ("u64::Nested::<PrimitiveParam>::from::<PrimitiveParam>")

urust_expr primitive_path_exact_generic_literal
  \<open> u64::Nested::<PrimitiveParam>::MAX \<close>

lemma primitive_path_exact_generic_literal_equal:
  \<open> primitive_path_exact_generic_literal = primitive_path_u64 \<close>
  unfolding primitive_path_exact_generic_literal_def primitive_path_u64_def
  by (rule refl)

urust_expr primitive_path_exact_generic_call
  \<open> u64::Nested::<PrimitiveParam>::from::<PrimitiveParam>(5u64) \<close>

lemma primitive_path_exact_generic_call_equal:
  \<open> primitive_path_exact_generic_call = primitive_path_call_one \<close>
  unfolding primitive_path_exact_generic_call_def primitive_path_call_one_def
  by (rule refl)

urust_expr_rejects
  \<open> u64::from::<UnregisteredParam>(5u64) \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>
urust_expr_rejects
  \<open> u64::MAX::<PrimitiveParam> \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>
urust_expr_rejects
  \<open> u64::Nested::<UnregisteredParam>::MAX \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

context
begin

micro_rust_notation (field) lens_id ("u64::FIELD_ONLY")

urust_expr_rejects
  \<open> u64::FIELD_ONLY \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>
urust_expr_rejects
  \<open> u64::FIELD_ONLY() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

end

urust_expr_rejects
  \<open> u64::MAX!() \<close> \<open> syntax error \<close>
urust_expr_rejects
  \<open> match u64::MAX { u64::MAX() => true, _ => false } \<close>
  \<open> syntax error \<close>
urust_expr_rejects
  \<open> match u64::MAX { u64::MISSING => true, _ => false } \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>
urust_expr_rejects
  \<open> [u64::MAX; usize::MISSING] \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

subsection\<open> Contextual repeat lengths with primitive operands \<close>

context
  includes primitive_path_cast_aliases
  fixes count :: \<open> 64 word \<close>
begin

micro_rust_notation (literal) count ("usize::CONTEXT_COUNT")

urust_expr primitive_path_context_repeat
  \<open> [u64::MAX; count] \<close>

urust_expr primitive_path_context_repeat_registered
  \<open> [u64::MAX; usize::CONTEXT_COUNT] \<close>

lemma primitive_path_context_repeat_equal:
  \<open> primitive_path_context_repeat = primitive_path_context_repeat_registered \<close>
  unfolding primitive_path_context_repeat_def primitive_path_context_repeat_registered_def
  by (rule refl)

urust_expr primitive_path_context_inline_alias
  \<open> [const { u8::MAX as PrimitivePathAlias }; usize::CONTEXT_COUNT] \<close>

urust_expr primitive_path_context_inline_compat
  \<open> [const { PrimitiveCompat::U8Max as u64 }; count] \<close>

lemma primitive_path_context_inline_alias_equal:
  \<open> primitive_path_context_inline_alias = primitive_path_context_inline_compat \<close>
  unfolding primitive_path_context_inline_alias_def primitive_path_context_inline_compat_def
  by (rule refl)

urust_expr_rejects
  \<open> let count = 2usize; [u64::MAX; count] \<close>
  \<open> cannot use lexical local \<close>

end


end
