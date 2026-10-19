(* Left branch of the fixture merge diamond: constructor and struct basenames that become
   ambiguous only in a theory that imports both branches. *)

theory Parser_Test_Fixtures_Left
  imports
    Parser_Test_Fixtures
    Enum_Theory.Enum_Theory
    Misc.Simple_Word_Enums
begin

chapter\<open> Constructor ambiguity \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

enum constructor_ambiguity_left =
    Shared
  | LeftOnly

simple_word_enum (plugins del: word_conversion) (8)
  word_constructor_ambiguity_left =
    SharedWordState = 11
  | LeftWordState = 12

chapter\<open> Struct ambiguity \<close>

datatype struct_ambiguity_left =
  AmbiguousStruct (ambiguous_field: nat)

datatype nullary_ambiguity_left =
  AmbiguousNullary

end
