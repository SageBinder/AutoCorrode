theory Parser_Test_Utils
  imports
    Micro_Rust_Shallow_Embedding
    Micro_Rust_Parser_Impl.Parser_Impl_Command
  keywords
    "old_urust_rejects" :: thy_decl
    and "urust_expr_rejects" :: thy_decl
    and "new_urust_rejects" :: thy_decl
begin

ML\<open>
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

fun parser_test_frontend_source source = "\<lbrakk> " ^ source ^ " \<rbrakk>"

val _ = Syntax.read_term \<^context> (parser_test_frontend_source "()")

fun old_urust_rejects source lthy =
  let
    val pos = Input.pos_of source
    val wrapped = parser_test_frontend_source (Input.string_of source)
    fun fail term =
      error ("old_urust_rejects: expected the old frontend to reject, but it accepted:\n" ^
        Syntax.string_of_term lthy term ^ Position.here pos)
  in
    (case Exn.result (Syntax.read_term lthy) wrapped of
       Exn.Res term => fail term
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           (writeln ("old frontend rejected as expected: " ^ Runtime.exn_message exn);
            lthy))
  end

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>old_urust_rejects\<close>
  "Assert that the old inner-syntax uRust frontend rejects a source expression"
  (Parse.token Parse.cartouche >>
    Parser_Lex_Util.cartouche_source >>
    old_urust_rejects)

datatype parser_test_rejection_tag =
    Parser_Test_Fidelity
  | Parser_Test_Frontend_Accepts
  | Parser_Test_Divergent
  | Parser_Test_Audit

fun validate_parser_test_rejection_tag check_frontend tag =
  (case (check_frontend, tag) of
     (true, Parser_Test_Fidelity) => ()
   | (true, _) =>
       error "urust_expr_rejects requires the `fidelity` tag"
   | (false, Parser_Test_Fidelity) =>
       error
         "new_urust_rejects requires the `frontend_accepts`, `divergent`, or `audit` tag"
   | (false, _) => ())

fun parse_parser_test_rejection_tag (name, pos) =
  (case name of
     "fidelity" => Parser_Test_Fidelity
   | "frontend_accepts" => Parser_Test_Frontend_Accepts
   | "divergent" => Parser_Test_Divergent
   | "audit" => Parser_Test_Audit
   | _ =>
       error
         ("unknown rejection tag " ^ quote name ^
           "; expected `fidelity`, `frontend_accepts`, `divergent`, or `audit`" ^
           Position.here pos))

fun parser_test_rejects check_frontend ((tag, source), expected) lthy =
  let
    val _ = validate_parser_test_rejection_tag check_frontend tag
    val pos = Input.pos_of source
    val expected = Symbol.trim_blanks (Input.string_of expected)
    fun fail msg = error ("urust_expr_rejects: " ^ msg ^ Position.here pos)

    fun check_parser_rejection () =
      (case Exn.result (fn () => Parser_Test_Elaboration.expression lthy source) () of
         Exn.Res term =>
           fail ("expected the new parser to reject, but it accepted and elaborated to: " ^
             Syntax.string_of_term lthy term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               if String.isSubstring expected message
               then writeln ("new parser rejected as expected: " ^ message)
               else
                 fail ("new parser rejected, but not for the expected reason.\n" ^
                   "  expected substring: " ^ quote expected ^
                   "\n  actual message: " ^ message)
             end)

    fun check_frontend_rejection () =
      (case Exn.result (Syntax.read_term lthy)
          (parser_test_frontend_source (Input.string_of source)) of
         Exn.Res term =>
           fail ("expected the existing frontend to reject, but it accepted and elaborated to: " ^
             Syntax.string_of_term lthy term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             writeln
               ("existing frontend rejected as expected: " ^
                 Runtime.exn_message exn))

    fun check_frontend_acceptance () =
      (case Exn.result (Syntax.read_term lthy)
          (parser_test_frontend_source (Input.string_of source)) of
         Exn.Res _ => writeln "existing frontend accepted as expected"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             fail
               ("expected the existing frontend to accept, but it rejected: " ^
                 Runtime.exn_message exn))

    val _ = check_parser_rejection ()
    val _ =
      (case (check_frontend, tag) of
         (true, Parser_Test_Fidelity) => check_frontend_rejection ()
       | (false, Parser_Test_Frontend_Accepts) => check_frontend_acceptance ()
       | _ => ())
  in lthy end

val parser_test_rejection_args =
  (Parse.name_position >> parse_parser_test_rejection_tag) --
    (Parse.token Parse.cartouche >>
      Parser_Lex_Util.cartouche_source) --
    (Parse.token Parse.cartouche >>
      Parser_Lex_Util.cartouche_source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_rejects\<close>
  "Assert that both uRust frontends reject; check the new parser's reason"
  (parser_test_rejection_args >> parser_test_rejects true)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>new_urust_rejects\<close>
  "Assert that the new uRust parser rejects under the selected frontend policy"
  (parser_test_rejection_args >> parser_test_rejects false)
\<close>

end
