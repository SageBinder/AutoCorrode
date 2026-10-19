(* Right branch of the fixture merge diamond: constructor and struct basenames that become
   ambiguous only in a theory that imports both branches. *)

theory Parser_Test_Fixtures_Right
  imports
    Parser_Test_Fixtures
    Enum_Theory.Enum_Theory
    Misc.Simple_Word_Enums
begin

chapter\<open> Constructor ambiguity \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

enum constructor_ambiguity_right =
    Shared
  | RightOnly

simple_word_enum (plugins del: word_conversion) (8)
  word_constructor_ambiguity_right =
    SharedWordState = 21
  | RightWordState = 22

chapter\<open> Struct ambiguity \<close>

datatype struct_ambiguity_right =
  AmbiguousStruct (ambiguous_field: nat)

datatype nullary_ambiguity_right =
  AmbiguousNullary

end
