theory Struct_Ambiguity_Right
  imports Micro_Rust_Parser
begin

datatype struct_ambiguity_right =
  AmbiguousStruct (ambiguous_field: nat)

end
