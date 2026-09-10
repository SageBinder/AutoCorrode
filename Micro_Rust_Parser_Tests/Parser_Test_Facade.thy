theory Parser_Test_Facade
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

section\<open> Parser facade smoke test \<close>

urust_expr smoke_num  \<open> 42 \<close>
urust_expr smoke_sfx  \<open> 1_u32 \<close>
urust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def

ML_val\<open>
  val _ =
    if Global_Theory.defined_fact \<^theory> "smoke_num_conformance"
    then error "default urust_conformance_check unexpectedly generated a theorem"
    else ()
\<close>

end
