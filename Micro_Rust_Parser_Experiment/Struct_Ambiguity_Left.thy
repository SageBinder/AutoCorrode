theory Struct_Ambiguity_Left
  imports Parser_Impl
begin

datatype struct_ambiguity_left =
  AmbiguousStruct (ambiguous_field: nat)

datatype nullary_ambiguity_left =
  AmbiguousNullary

end
