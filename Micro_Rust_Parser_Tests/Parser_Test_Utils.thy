theory Parser_Test_Utils
  imports Micro_Rust_Parser_Impl.Parser_Impl
begin

ML\<open>
structure Parser_Test_Report_Lock =
struct
  val lock = Synchronized.var "parser_test_report_lock" ()
  fun run action =
    Synchronized.change_result lock (fn () => (action (), ()))
end
\<close>

end
