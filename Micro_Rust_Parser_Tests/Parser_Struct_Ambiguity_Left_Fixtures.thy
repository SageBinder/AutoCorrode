theory Parser_Struct_Ambiguity_Left_Fixtures
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

datatype struct_ambiguity_left =
  AmbiguousStruct (ambiguous_field: nat)

datatype nullary_ambiguity_left =
  AmbiguousNullary

end
