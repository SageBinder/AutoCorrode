theory Parser_Constructor_Ambiguity_Left_Fixtures
  imports
    Enum_Theory.Enum_Theory
    Misc.Simple_Word_Enums
begin

enum constructor_ambiguity_left =
    Shared
  | LeftOnly

simple_word_enum (plugins del: word_conversion) (8)
  word_constructor_ambiguity_left =
    SharedWordState = 11
  | LeftWordState = 12

end
