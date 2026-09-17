theory Parser_Cast_Alias_Fixtures
  imports Parser_Test_Utils
begin

bundle module_cast_aliases begin
  urust_cast_alias "U8Alias" = "u8"
  urust_cast_alias "types::U16Alias" = "u16"
  urust_cast_alias "U32Alias" = "u32"
  urust_cast_alias "U64Alias" = "u64"
  urust_cast_alias "UsizeAlias" = "usize"
  urust_cast_alias "I32Alias" = "i32"
  urust_cast_alias "I64Alias" = "i64"

  urust_cast_alias "ConstU8Pointer" = "*const u8"
  urust_cast_alias "ConstU16Pointer" = "*const u16"
  urust_cast_alias "ConstU32Pointer" = "*const u32"
  urust_cast_alias "ConstU64Pointer" = "*const u64"
  urust_cast_alias "ConstUsizePointer" = "*const usize"
  urust_cast_alias "MutU8Pointer" = "*mut u8"
  urust_cast_alias "MutU16Pointer" = "*mut u16"
  urust_cast_alias "MutU32Pointer" = "*mut u32"
  urust_cast_alias "MutU64Pointer" = "*mut u64"
  urust_cast_alias "MutUsizePointer" = "*mut usize"
end

bundle conflict_u8_aliases begin
  urust_cast_alias "SharedWidth" = "u8"
end

bundle conflict_u16_aliases begin
  urust_cast_alias "SharedWidth" = "u16"
end

bundle idempotent_cast_aliases begin
  urust_cast_alias "StableWidth" = "u16"
  urust_cast_alias "StableWidth" = "u16"
end

locale cast_alias_scope =
  fixes scope_word :: "64 word"

end
