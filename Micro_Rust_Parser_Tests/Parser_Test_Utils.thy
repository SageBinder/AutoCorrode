(* Shared ML support and test-only commands for the parser tests. *)

theory Parser_Test_Utils
  imports
    Micro_Rust_Parser_Impl.Parser_Impl_Command
  keywords "urust_expr_rejects" :: thy_decl
begin

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

ML\<open>
(* Queries for automatic call registrations use the same notation owner as explicit ones. *)
structure Parser_Test_Calls =
struct
  fun entries ctxt name = Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction name
  fun lookup ctxt name = try hd (entries ctxt name)
  fun dump ctxt =
    Micro_Rust_Names.dump ctxt
    |> map_filter (fn (kind, name, entry) =>
         if kind = Micro_Rust_Names.NFunction then SOME (name, entry) else NONE)
  fun declare {rust_name, rust_pos, function} lthy =
    lthy |> Local_Theory.declaration {pervasive = false, syntax = true, pos = rust_pos}
      (fn phi => Micro_Rust_Names.reserve_declaration Micro_Rust_Names.Function_Declaration
          rust_name rust_pos #>
        Micro_Rust_Names.register_with_source Micro_Rust_Names.NFunction rust_name
          (Morphism.term phi function) NONE rust_pos)
end

structure Parser_Test_Report_Lock =
struct
  val lock = Synchronized.var "parser_test_report_lock" ()
  fun run action =
    Synchronized.change_result lock (fn () => (action (), ()))
end

structure Parser_Test_Reports =
struct
  fun collect_markup (XML.Text _) result = result
    | collect_markup (XML.Elem (markup, body)) result =
        fold collect_markup body (markup :: result)

  fun chunks action =
    let
      val captured = Synchronized.var "parser_test_reports" ([]: string list)
      fun capture output =
        Synchronized.change captured (append output)
      val result =
        Parser_Test_Report_Lock.run (fn () =>
          Unsynchronized.setmp Private_Output.report_fn capture
            (fn () => Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
    in (result, Synchronized.value captured) end

  fun markup action =
    let
      val (result, reports) = chunks action
      val markup =
        fold collect_markup (maps YXML.parse_body reports) []
    in (result, markup) end
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

fun parser_test_rejects (source, expected) lthy =
  let
    val pos = Input.pos_of source
    val expected = Symbol.trim_blanks (Input.string_of expected)
    val rejection_lthy =
      Config.put URust_Command.urust_pp_test false lthy
    fun fail msg =
      error ("urust_expr_rejects: " ^ msg ^ Position.here pos)
  in
    (case Exn.result
        (fn () =>
          Parser_Test_Elaboration.expression rejection_lthy source) () of
       Exn.Res term =>
         fail
           ("expected the parser to reject, but it accepted and elaborated to: " ^
             Syntax.string_of_term rejection_lthy term)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn in
             if String.isSubstring expected message
             then writeln ("parser rejected as expected: " ^ message)
             else
               fail
                 ("parser rejected, but not for the expected reason.\n" ^
                   "  expected substring: " ^ quote expected ^
                   "\n  actual message: " ^ message)
           end);
    lthy
  end

val parser_test_rejection_args =
  (Parse.token Parse.cartouche >>
    Parser_Lex_Util.cartouche_source) --
  (Parse.token Parse.cartouche >>
    Parser_Lex_Util.cartouche_source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_rejects\<close>
  "Assert that the uRust parser rejects an expression for the expected reason"
  (parser_test_rejection_args >> parser_test_rejects)
\<close>

end
