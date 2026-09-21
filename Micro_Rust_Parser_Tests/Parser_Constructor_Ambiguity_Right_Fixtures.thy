theory Parser_Constructor_Ambiguity_Right_Fixtures
  imports
    Enum_Theory.Enum_Theory
    Misc.Simple_Word_Enums
begin

enum constructor_ambiguity_right =
    Shared
  | RightOnly

simple_word_enum (plugins del: word_conversion) (8)
  word_constructor_ambiguity_right =
    SharedWordState = 21
  | RightWordState = 22

end
