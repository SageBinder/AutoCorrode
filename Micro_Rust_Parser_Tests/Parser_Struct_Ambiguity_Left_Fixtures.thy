theory Parser_Struct_Ambiguity_Left_Fixtures
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

datatype struct_ambiguity_left =
  AmbiguousStruct (ambiguous_field: nat)

datatype nullary_ambiguity_left =
  AmbiguousNullary

end
