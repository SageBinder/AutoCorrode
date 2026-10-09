theory Parser_Cast_Alias_Fixtures
  imports Parser_Test_Utils
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

bundle module_cast_aliases begin
  urust_type_alias \<open> type U8Alias = u8; \<close>
  urust_type_alias "types::U16Alias" \<open> type U16Alias = u16; \<close>
  urust_type_alias \<open> type U32Alias = u32; \<close>
  urust_type_alias \<open> type U64Alias = u64; \<close>
  urust_type_alias \<open> type UsizeAlias = usize; \<close>
  urust_type_alias \<open> type I32Alias = i32; \<close>
  urust_type_alias \<open> type I64Alias = i64; \<close>

  urust_type_alias \<open> type ConstU8Pointer = *const u8; \<close>
  urust_type_alias \<open> type ConstU16Pointer = *const u16; \<close>
  urust_type_alias \<open> type ConstU32Pointer = *const u32; \<close>
  urust_type_alias \<open> type ConstU64Pointer = *const u64; \<close>
  urust_type_alias \<open> type ConstUsizePointer = *const usize; \<close>
  urust_type_alias \<open> type MutU8Pointer = *mut u8; \<close>
  urust_type_alias \<open> type MutU16Pointer = *mut u16; \<close>
  urust_type_alias \<open> type MutU32Pointer = *mut u32; \<close>
  urust_type_alias \<open> type MutU64Pointer = *mut u64; \<close>
  urust_type_alias \<open> type MutUsizePointer = *mut usize; \<close>
end

bundle conflict_u8_aliases begin
  urust_type_alias \<open> type SharedWidth = u8; \<close>
end

bundle conflict_u16_aliases begin
  urust_type_alias \<open> type SharedWidth = u16; \<close>
end

bundle idempotent_cast_aliases begin
  urust_type_alias \<open> type StableWidth = u16; \<close>
  urust_type_alias \<open> type StableWidth = u16; \<close>
end

locale cast_alias_scope =
  fixes scope_word :: "64 word"

end
