theory Parser_Test_Utils
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

ML\<open>
structure Parser_Test_Report_Lock =
struct
  val lock = Synchronized.var "parser_test_report_lock" ()
  fun run action =
    Synchronized.change_result lock (fn () => (action (), ()))
end

structure Parser_Test_Elaboration =
struct
  fun expression ctxt source =
    URust_Command.elaborate ctxt
      {kind = URust_Command.Expression,
       source = source,
       arguments = [],
       arguments_pos = #2 (Input.range_of source),
       declared_type = NONE}

  fun expression_with_arguments ctxt arguments source =
    URust_Command.elaborate ctxt
      {kind = URust_Command.Expression,
       source = source,
       arguments = arguments,
       arguments_pos = #2 (Input.range_of source),
       declared_type = NONE}

  fun function ctxt
      {raw_type, parameters, parameters_pos, body} =
    URust_Command.elaborate ctxt
      {kind = URust_Command.Function,
       source = body,
       arguments = parameters,
       arguments_pos = parameters_pos,
       declared_type = SOME raw_type}
end
\<close>

end
