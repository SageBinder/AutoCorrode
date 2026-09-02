theory Struct_Ambiguity_Right
  imports Parser_Impl
begin

datatype struct_ambiguity_right =
  AmbiguousStruct (ambiguous_field: nat)

datatype nullary_ambiguity_right =
  AmbiguousNullary

end
