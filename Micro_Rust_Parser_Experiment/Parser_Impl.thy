(* Roll-up facade for the custom uRust parser. *)

theory Parser_Impl
  imports Parser_Impl_Command
begin

section\<open> Smoke test \<close>

text\<open>
Parser clients import this roll-up facade. Programmatic clients use the sealed
\<open>URust_Command\<close> interface. Frontend conformance is tested in
\<open>Parser_Test_Conformance.thy\<close>; the definitions below are smoke tests only.
\<close>

urust_expr smoke_num  \<open> 42 \<close>
urust_expr smoke_sfx  \<open> 1_u32 \<close>
urust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def

end
