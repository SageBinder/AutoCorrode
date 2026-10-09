(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Type_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Primitive types, aliases, enums, and generated records\<close>

c_source Types \<open>
  typedef unsigned int count_t;
  typedef count_t alias_t;
  struct pair { unsigned int left; unsigned int right; };
  enum colour { RED = 3, GREEN, BLUE = 9, LAST };
  unsigned char u8(unsigned char x) { return x; }
  signed char i8(signed char x) { return x; }
  unsigned short u16(unsigned short x) { return x; }
  short i16(short x) { return x; }
  unsigned int u32(unsigned int x) { return x; }
  int i32(int x) { return x; }
  unsigned long u64(unsigned long x) { return x; }
  long i64(long x) { return x; }
  unsigned __int128 u128(unsigned __int128 x) { return x; }
  __int128 i128(__int128 x) { return x; }
  _Bool boolean(_Bool x) { return x; }
  alias_t alias(alias_t x) { return x; }
  unsigned int enum_values(void) { return GREEN + LAST; }
  unsigned int promote(unsigned char a, unsigned short b) { return a + b; }
  unsigned int mixed(int a, unsigned int b) { return a + b; }
  unsigned long record_size(void) { return sizeof(struct pair); }
  unsigned long record_offset(void) { return __builtin_offsetof(struct pair, right); }
\<close>

ML_val \<open>
  val signatures =
    [("u8", \<^typ>\<open>c_char\<close>), ("i8", \<^typ>\<open>c_schar\<close>),
     ("u16", \<^typ>\<open>c_ushort\<close>), ("i16", \<^typ>\<open>c_short\<close>),
     ("u32", \<^typ>\<open>c_uint\<close>), ("i32", \<^typ>\<open>c_int\<close>),
     ("u64", \<^typ>\<open>c_ulong\<close>), ("i64", \<^typ>\<open>c_long\<close>),
     ("u128", \<^typ>\<open>c_uint128\<close>), ("i128", \<^typ>\<open>c_int128\<close>),
     ("boolean", \<^typ>\<open>bool\<close>), ("alias", \<^typ>\<open>c_uint\<close>)]
  val _ = List.app (fn (name, ty) =>
    C_Parser_Test.require_arguments \<^context> ("Types." ^ name) [ty]) signatures
  val _ = C_Parser_Test.check_definitions \<^context> "Types"
    (map #1 signatures @ ["enum_values", "promote", "mixed",
      "record_size", "record_offset"])
  val _ = Proof_Context.get_thms \<^context> "Types.pair.record_simps"
  val _ = C_Parser_Test.require_consts \<^context> "Types.promote"
    [\<^const_name>\<open>c_signed_add_with_abort\<close>]
    [\<^const_name>\<open>c_unsigned_add\<close>]
  val _ = C_Parser_Test.require_consts \<^context> "Types.mixed"
    [\<^const_name>\<open>c_unsigned_add\<close>]
    [\<^const_name>\<open>c_signed_add_with_abort\<close>]
\<close>

end
