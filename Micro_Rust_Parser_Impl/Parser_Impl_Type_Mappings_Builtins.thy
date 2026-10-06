theory Parser_Impl_Type_Mappings_Builtins
  imports
    Parser_Impl_Type_Mappings
    Shallow_Micro_Rust.Micro_Rust_Parser_Target
begin

section\<open> Initial uRust type mappings \<close>

text\<open>
The initial primitive spellings are ordinary registry entries. The resolver has no primitive
fallback: removing one of these declarations makes that spelling unknown, while adding another
mapping requires no ML or grammar change.
\<close>

urust_type "u8" = \<open>8 word\<close>
urust_type "u16" = \<open>16 word\<close>
urust_type "u32" = \<open>32 word\<close>
urust_type "u64" = \<open>64 word\<close>
urust_type "usize" = \<open>64 word\<close>
urust_type "i32" = \<open>32 word\<close>
urust_type "i64" = \<open>64 word\<close>
urust_type "bool" = \<open>bool\<close>
urust_type "()" = \<open>unit\<close>

end
