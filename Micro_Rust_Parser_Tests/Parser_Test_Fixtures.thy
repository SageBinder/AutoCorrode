(* Declaration-only fixtures shared by the parser tests. *)

theory Parser_Test_Fixtures
  imports
    Parser_Test_Utils
    Shallow_Micro_Rust.Eval
begin

chapter\<open> Iterator fixtures \<close>

section\<open>Shared iterator fixtures\<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

type_synonym zip_left_iterator =
  \<open>(nat list, nat, unit, unit, unit) iterator\<close>

type_synonym zip_right_iterator =
  \<open>(nat list, bool, unit, unit, unit) iterator\<close>

type_synonym zip_pair_iterator =
  \<open>(nat list, nat \<times> bool \<times> tnil, unit, unit, unit) iterator\<close>

definition zip_left_empty :: zip_left_iterator where
  \<open>zip_left_empty \<equiv> make_iterator []\<close>

definition zip_left_two :: zip_left_iterator where
  \<open>zip_left_two \<equiv> make_iterator [fun_literal 1, fun_literal 2]\<close>

definition zip_left_one :: zip_left_iterator where
  \<open>zip_left_one \<equiv> make_iterator [fun_literal 1]\<close>

definition zip_right_one :: zip_right_iterator where
  \<open>zip_right_one \<equiv> make_iterator [fun_literal True]\<close>

definition zip_right_two :: zip_right_iterator where
  \<open>zip_right_two \<equiv> make_iterator [fun_literal True, fun_literal False]\<close>

definition zip_effect_thunk ::
    \<open>nat \<Rightarrow> 'value \<Rightarrow>
     (nat list, 'value, unit, unit, unit) function_body\<close>
  where
  \<open>zip_effect_thunk marker value \<equiv> FunctionBody (
    bind (put (\<lambda>trace. trace @ [marker])) (\<lambda>_. literal value))\<close>

chapter\<open> Registered constructor fixtures \<close>

text\<open>
Shared registered-constructor fixtures used by negative tests and the structural regression
audits. Keeping these declarations neutral avoids making either test suite import the other.
\<close>

datatype negative_registered_constructor_fixture =
    NegativeRegisteredNullary
  | NegativeRegisteredUnary nat
  | NegativeRegisteredOther

datatype 'a negative_registered_phantom =
  NegativeRegisteredPhantom

definition negative_registered_nonconstructor ::
  negative_registered_constructor_fixture where
  \<open>
    negative_registered_nonconstructor \<equiv>
      NegativeRegisteredNullary
  \<close>

definition negative_registered_number :: nat where
  \<open> negative_registered_number \<equiv> 42 \<close>

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Nullary")

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredUnary
  ("NegativeRegistered::Unary")

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredOther
  ("NegativeRegistered::Other")

micro_rust_notation (literal)
  negative_registered_nonconstructor
  ("NegativeRegistered::Value")

micro_rust_notation (literal)
  negative_registered_number
  ("NegativeRegistered::Number")

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Ambiguous")

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredOther
  ("NegativeRegistered::Ambiguous")

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::ConstructorWins")

micro_rust_notation (literal)
  negative_registered_nonconstructor
  ("NegativeRegistered::ConstructorWins")

micro_rust_notation (literal)
  \<open> NegativeRegisteredUnary 0 \<close>
  ("NegativeRegistered::Applied")

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Duplicate")

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Duplicate")

micro_rust_notation (literal)
  \<open>
    NegativeRegisteredPhantom ::
      nat negative_registered_phantom
  \<close>
  ("NegativeRegistered::Phantom")

micro_rust_notation (literal)
  \<open>
    NegativeRegisteredPhantom ::
      bool negative_registered_phantom
  \<close>
  ("NegativeRegistered::Phantom")

definition integration_registered_value_audit :: nat
  where \<open> integration_registered_value_audit = 42 \<close>

micro_rust_notation (literal)
  integration_registered_value_audit
  ("IntegrationAudit::Value")

chapter\<open> Cast-target alias fixtures \<close>

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

urust_type_alias \<open> type StableWidth = u16; \<close>

urust_type_alias \<open> type StableWidth = u16; \<close>

locale cast_alias_scope =
  fixes scope_word :: "64 word"
begin

urust_type_alias \<open> type LocaleWidth = u16; \<close>

end

end
