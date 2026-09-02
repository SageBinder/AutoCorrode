(* Compatibility facade for the custom uRust parser. *)

theory Parser_Impl
  imports Parser_Impl_Command
begin

section\<open> Smoke test \<close>

text\<open>
Smoke definitions only; frontend conformance is tested in
\<open>Parser_Test_Conformance.thy\<close>.
\<close>
urust_expr smoke_num  \<open> 42 \<close>
urust_expr smoke_sfx  \<open> 1_u32 \<close>
urust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def

end
