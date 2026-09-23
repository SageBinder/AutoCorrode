theory Timing_Fixture_B
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

declare [[urust_timing_info = true]]

urust_expr
  timing_fixture_gamma
  \<open> let first = 3_u16; let second = 4_u16; first + second \<close>

urust_fn
  timing_fixture_delta ::
  \<open>16 word \<Rightarrow> (unit, 16 word, unit, unit, unit) function_body\<close>
  (item)
  \<open> item + 2_u16 \<close>

end
