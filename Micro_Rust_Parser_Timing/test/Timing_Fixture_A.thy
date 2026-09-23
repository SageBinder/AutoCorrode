theory Timing_Fixture_A
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

declare [[urust_timing_info = true]]

urust_expr
  timing_fixture_alpha
  \<open> let value = 1_u32; value + 2_u32 \<close>

urust_fn
  timing_fixture_beta ::
  \<open>32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body\<close>
  (item)
  \<open> item + 1_u32 \<close>

end
