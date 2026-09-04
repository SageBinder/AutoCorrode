theory Parser_Test_Turbofish
  imports Parser_Test_Regression_Audit
begin

section\<open> Additive payload fixtures \<close>

definition generic_dimension_call ::
  \<open>nat \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_dimension_call _ \<equiv> cf0 \<close>

definition GENERIC_LIMIT_A :: nat where
  \<open> GENERIC_LIMIT_A = 11 \<close>

definition GENERIC_LIMIT_B :: nat where
  \<open> GENERIC_LIMIT_B = 13 \<close>

urust_expr generic_payload_01 \<open> generic_dimension_call::<1>() \<close>
urust_expr generic_payload_02 \<open> generic_dimension_call::<GENERIC_LIMIT_A>() \<close>
urust_expr generic_payload_03 \<open> generic_dimension_call::<1 + GENERIC_LIMIT_A>() \<close>
urust_expr generic_payload_04
  \<open> generic_dimension_call::<GENERIC_LIMIT_A + 3 + GENERIC_LIMIT_B>() \<close>

section\<open> Exact canonical names \<close>

urust_notation (call) cf0 ("GenericFactory::<TypeA>::make")
urust_notation (call) cf0 ("GenericContainer::<2>::make")

urust_expr generic_exact_type_a \<open> GenericFactory::<TypeA>::make() \<close>
urust_expr generic_exact_container_2 \<open> GenericContainer::<2>::make() \<close>

definition exact_fallback ::
  \<open>int \<Rightarrow> int \<Rightarrow>
    (unit, int, unit, unit, unit) function_body\<close>
  where \<open> exact_fallback parameter \<equiv>
      lift_fun1 (\<lambda>argument. parameter + argument) \<close>

micro_rust_notation (call) exact_fallback ("Exact::f")
urust_notation (call) cf0 ("Exact::f::<N>")

urust_expr exact_generic_wins \<open> Exact::f::<N>() \<close>
urust_expr exact_generic_fallback \<open> Exact::f::<1>(2) \<close>

section\<open> Structural and semantic audit \<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("restricted turbofish audit: " ^ message)

    fun parse_source source =
      (case URust_Diagnostics.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "restricted turbofish audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun generic_arguments text =
      (case parse text of
         UE_Call
           (UC_Path
             (UR_Path
               ([Path_Segment
                  ("f", _, SOME (Generic_Args (arguments, _)))], _)),
            [], _) => arguments
       | _ =>
           error ("restricted turbofish audit: call shape changed for " ^
             quote text))

    fun one_generic text =
      (case generic_arguments text of
         [Generic_Arg (canonical, source)] => (canonical, source)
       | _ =>
           error ("restricted turbofish audit: expected one argument for " ^
             quote text))

    val canonical_cases =
      [("f::<a + b + c>()", "a+b+c"),
       ("f::<(a + b) + c>()", "(a+b)+c"),
       ("f::<Module::Value>()", "Module::Value"),
       ("f::<42>()", "42"),
       ("f::<0x2a>()", "0x2a")]
    val _ =
      List.app
        (fn (source, expected) =>
          audit_assert ("canonical fragment changed for " ^ quote source)
            (#1 (one_generic source) = expected))
        canonical_cases

    val spaced_text = "f::\n <  a +\n b + c  ,  (d) >()"
    val spaced_start =
      Position.make0 11 40 400 "" "" "restricted-turbofish-source-audit"
    val spaced =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          spaced_text spaced_start)
    val _ =
      (case spaced of
         UE_Call
           (UC_Path
             (UR_Path
               ([Path_Segment
                  ("f", _,
                   SOME (Generic_Args
                     ([Generic_Arg (first_canonical, first_source),
                       Generic_Arg (second_canonical, second_source)],
                      generic_pos)))], _)),
            [], _) =>
           let
             val expected_generic_start =
               Position.symbol_explode "f" spaced_start
             val first_start =
               Position.symbol_explode "f::\n <  " spaced_start
             val first_stop =
               Position.symbol_explode "f::\n <  a +\n b + c" spaced_start
             val second_start =
               Position.symbol_explode "f::\n <  a +\n b + c  ,  " spaced_start
             val second_stop =
               Position.symbol_explode "f::\n <  a +\n b + c  ,  (d)" spaced_start
           in
             audit_assert "canonical rendering retained trivia"
               (first_canonical = "a+b+c" andalso
                second_canonical = "(d)");
             audit_assert "first original source slice changed"
               (Input.string_of first_source = "a +\n b + c" andalso
                Position.offset_of (#1 (Input.range_of first_source)) =
                  Position.offset_of first_start andalso
                Position.offset_of (#2 (Input.range_of first_source)) =
                  Position.offset_of first_stop);
             audit_assert "second original source slice changed"
               (Input.string_of second_source = "(d)" andalso
                Position.offset_of (#1 (Input.range_of second_source)) =
                  Position.offset_of second_start andalso
                Position.offset_of (#2 (Input.range_of second_source)) =
                  Position.offset_of second_stop);
             audit_assert "generic span did not start at the path separator"
               (Position.offset_of generic_pos =
                  Position.offset_of expected_generic_start)
           end
       | _ => error "restricted turbofish audit: multiline call shape changed")

    fun checked_generic_argument source =
      let
        val checked =
          Syntax.check_term ctxt
            (URust_Translate.mk_closed ctxt (parse source))
        val function =
          (case Term.strip_comb checked of
             (_, function :: _) => function
           | _ => error "restricted turbofish audit: checked call shape changed")
      in
        (case Term.strip_comb
            (Term_Position.strip_positions function) of
           (_, [argument]) => Term_Position.strip_positions argument
         | _ =>
             error "restricted turbofish audit: generic application shape changed")
      end

    fun check_semantic source expected =
      let
        val actual = checked_generic_argument source
        val wanted =
          Syntax.read_term ctxt expected
          |> Term_Position.strip_positions
      in
        audit_assert ("checked HOL shape changed for " ^ quote source)
          (actual aconv wanted)
      end

    val _ =
      List.app (fn (source, expected) => check_semantic source expected)
        [("turbofish_int_one::<1 + 2 + 3>(0)", "(1 + 2 + 3 :: int)"),
         ("turbofish_int_one::<(1 + 2) + 3>(0)", "((1 + 2) + 3 :: int)")]

    val exact_term =
      URust_Command.elab_urust ctxt
        (Parser_Lex_Util.text_source "Exact::f::<N>()")
    val fallback_term =
      URust_Command.elab_urust ctxt
        (Parser_Lex_Util.text_source "Exact::f::<1>(2)")
    val _ =
      audit_assert "complete exact registration did not win"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>cf0\<close>
            | _ => false)
          exact_term)
    val _ =
      audit_assert "final exact miss did not use semantic fallback"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>exact_fallback\<close>
            | _ => false)
          fallback_term)

    fun expect_rejection text expected =
      (case Exn.result
          (fn () =>
            URust_Command.elab_urust ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error ("restricted turbofish audit: unexpectedly accepted " ^
             quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (Runtime.exn_message exn)))

    val _ =
      expect_rejection "GenericFactory::<Missing>::make()"
        "generic arguments on an intermediate path segment require an exact registration"
    val malformed =
      [("f::<>()", "syntax error"),
       ("f::<,1>()", "syntax error"),
       ("f::<1,,2>()", "syntax error"),
       ("f::<1,>()", "syntax error"),
       ("f::<1 a>()", "syntax error"),
       ("f::<1 +>()", "syntax error"),
       ("f::<-1>()", "unexpected input"),
       ("f::<1 - 2>()", "unexpected input"),
       ("f::<1 * 2>()", "unexpected input"),
       ("f::<1 / 2>()", "unexpected input"),
       ("f::<((1)>()", "syntax error"),
       ("f::<1)>()", "syntax error"),
       ("f::<1(", "unterminated turbofish"),
       ("f::<1>>()",
        "generic arguments on a bare value require an exact literal registration"),
       ("f::<1u8>()", "syntax error"),
       ("f::<Suc 4>()", "syntax error"),
       ("f::<a div b>()", "syntax error"),
       ("f::<a mod b>()", "syntax error"),
       ("f::<(1, 2)>()", "syntax error"),
       ("f::<[1, 2]>()", "unexpected input"),
       ("f::<\"text\">()", "unexpected input"),
       ("f::<STR ''text''>()", "unexpected input"),
       ("f::<1 :: nat>()", "syntax error"),
       ("f::<a < b>()", "unexpected input"),
       ("f::<a << b>()", "unexpected input"),
       ("f::<a & b>()", "unexpected input"),
       ("f::<a && b>()", "unexpected input"),
       ("f::<a % b>()", "unexpected input"),
       ("f::<a ^ b>()", "unexpected input"),
       ("f::<\<clubsuit>>()", "unexpected input"),
       ("f::<" ^ Symbol.open_ ^ "opaque" ^ Symbol.close ^ ">()",
        "unexpected input"),
       ("f::<\<epsilon>\<open>1\<close>>()", "unexpected input"),
       ("f::<1 // comment\n + 2>()", "unexpected input")]
    val _ =
      List.app
        (fn (source, expected) =>
          (expect_rejection source expected;
           case parse "cf0()" of
             UE_Call (UC_Path path, [], _) =>
               audit_assert "lexer state leaked after malformed generic input"
                 (render_path path = "cf0")
           | _ => error "restricted turbofish audit: recovery parse changed"))
        malformed
  in
    val _ = writeln "Restricted turbofish AST, semantics, lookup, and recovery passed"
  end
\<close>

section\<open> Markup and diagnostics \<close>

definition generic_markup_value :: int where
  \<open> generic_markup_value = 8 \<close>

definition generic_markup_call ::
  \<open>nat \<Rightarrow> int \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_markup_call _ _ \<equiv> cf1 \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("restricted turbofish markup audit: " ^ message)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_reports action =
      let
        val captured = Unsynchronized.ref ([]: string list)
        fun capture chunks =
          Unsynchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (! captured)) []
      in (result, markup) end

    fun source_position start prefix text =
      let
        val token_start = Position.symbol_explode prefix start
        val token_stop = Position.symbol_explode text token_start
      in Position.range_position (Position.range (token_start, token_stop)) end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup

    val text = "generic_markup_call::\n <(1+2), generic_markup_value+2+1>(0)"
    val start =
      Position.make0 31 80 800 "" "" "restricted-turbofish-markup"
    val (_, markup) =
      capture_reports
        (fn () =>
          ignore
            (URust_Command.elab_urust ctxt
              (Parser_Lex_Util.positioned_content_source text start)))
    val delimiters =
      [source_position start "generic_markup_call" "::",
       source_position start "generic_markup_call::\n " "<",
       source_position start "generic_markup_call::\n <" "(",
       source_position start "generic_markup_call::\n <(1+2" ")",
       source_position start "generic_markup_call::\n <(1+2)" ",",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2+1" ">"]
    val operators =
      [source_position start "generic_markup_call::\n <(1" "+",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value" "+",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2" "+"]
    val numerals =
      [source_position start "generic_markup_call::\n <(" "1",
       source_position start "generic_markup_call::\n <(1+" "2",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+" "2",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2+" "1"]
    val _ =
      List.app
        (fn position =>
          audit_assert "generic delimiter markup moved"
            (has_markup markup Markup.delimiterN position))
        delimiters
    val _ =
      List.app
        (fn position =>
          audit_assert "generic operator markup moved"
            (has_markup markup Markup.operatorN position))
        operators
    val _ =
      List.app
        (fn position =>
          audit_assert "generic numeral markup moved"
            (has_markup markup Markup.numeralN position))
        numerals

    val operator_text = "f::<1+2+3>()"
    val operator_start =
      Position.make0 37 100 1000 "" "" "restricted-turbofish-all-operators"
    val (_, operator_markup) =
      capture_reports
        (fn () =>
          ignore
            (URust_Diagnostics.parse_source ctxt
              (Parser_Lex_Util.positioned_content_source
                operator_text operator_start)))
    val all_operators =
      [source_position operator_start "f::<1" "+",
       source_position operator_start "f::<1+2" "+"]
    val _ =
      List.app
        (fn position =>
          audit_assert "arithmetic operator markup moved"
            (has_markup operator_markup Markup.operatorN position))
        all_operators

    val malformed_text = "// \<clubsuit>\nf::<1 + %>()"
    val malformed_start =
      Position.make0 41 120 1200 "" "" "restricted-turbofish-symbol-offset"
    val expected_position =
      Position.symbol_explode "// \<clubsuit>\nf::<1 + " malformed_start
    val message =
      (case Exn.result
          (fn () =>
            URust_Diagnostics.parse_source ctxt
              (Parser_Lex_Util.positioned_content_source
                malformed_text malformed_start)) () of
         Exn.Res _ => error "restricted turbofish markup audit: malformed input accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)
    val plain = XML.content_of (YXML.parse_body message)
    val message_markup =
      fold collect_markup (YXML.parse_body message) []
    val _ =
      audit_assert "smallest offending generic token changed"
        (String.isSubstring "unexpected input \"%\"" plain)
    val _ =
      audit_assert "Isabelle-symbol-counted diagnostic offset changed"
        (exists
          (fn (_, properties) =>
            Properties.get properties Markup.offsetN =
              Option.map Value.print_int
                (Position.offset_of expected_position))
          message_markup)
  in
    val _ = writeln "Restricted turbofish markup and diagnostics passed"
  end
\<close>

definition generic_navigation_call ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_navigation_call _ _ \<equiv> cf1 \<close>

context
  fixes generic_free :: nat
begin

ML_val\<open>
  local
    val ctxt = \<^context>
    val text =
      "let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
      "generic_navigation_call::<generic_free, generic_bound>(0)"
    val start =
      Position.make0 47 140 1400 "" "" "restricted-turbofish-identifier-markup"
    val captured = Unsynchronized.ref ([]: string list)
    fun capture chunks =
      Unsynchronized.change captured (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (URust_Command.elab_urust ctxt
                    (Parser_Lex_Util.positioned_content_source text start))) ()) ())
    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (! captured)) []
    fun token_position prefix token =
      let
        val token_start = Position.symbol_explode prefix start
        val token_stop = Position.symbol_explode token token_start
      in Position.range_position (Position.range (token_start, token_stop)) end
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup
    val free_position =
      token_position
        ("let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
          "generic_navigation_call::<")
        "generic_free"
    val bound_position =
      token_position
        ("let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
          "generic_navigation_call::<generic_free, ")
        "generic_bound"
    val _ =
      if has_markup Markup.freeN free_position then ()
      else error "restricted turbofish markup audit: context fix lost free markup"
    val _ =
      if has_markup Markup.boundN bound_position then ()
      else error "restricted turbofish markup audit: generic binder lost bound markup"
  in end
\<close>

end

section\<open> Canonical exact-key regressions \<close>

urust_notation (call) cf0 ("AuditSpaced::<a + b>::new")
urust_notation cf0 ("AuditAuto::<a + b>::new")
urust_notation (call) cf0 ("AuditIdentifier::<div>::new")
urust_notation (call) cf0 ("AuditIdentifier::<mod>::new")
urust_notation (call) macro_shout ("AuditMacro::<a + b>::shout!")
urust_notation (config) [shadow_no_warn] "AuditConfig::<a + b>::new"

urust_expr audit_spaced_compact \<open> AuditSpaced::<a+b>::new() \<close>
urust_expr audit_spaced_spaced \<open> AuditSpaced::<a + b>::new() \<close>
urust_expr audit_spaced_multiline
  \<open>
    AuditSpaced::<
      a +
      b
    >::new()
  \<close>
urust_expr audit_auto \<open> AuditAuto::<a+b>::new() \<close>
urust_expr audit_div_identifier \<open> AuditIdentifier::<div>::new() \<close>
urust_expr audit_mod_identifier \<open> AuditIdentifier::<mod>::new() \<close>
urust_expr audit_macro \<open> AuditMacro::<a+b>::shout!(true) \<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun parse_path text =
      (case URust_Diagnostics.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME (UE_Call (UC_Path path, [], _)) => path
       | _ => error ("canonical exact-key regression: unexpected AST for " ^ quote text))

    val identifier = render_path (parse_path "f::<adivb>()")
    val _ =
      if identifier = "f::<adivb>" then ()
      else error "canonical exact-key regression: identifier rendering changed"
    val _ =
      (case Exn.result
          (fn () =>
            URust_Command.elab_urust ctxt
              (Parser_Lex_Util.text_source
                "f::<a div b>()")) () of
         Exn.Res _ =>
           error "canonical exact-key regression: a div b was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else ())
    val {suppress_warning, ...} =
      Micro_Rust_Names.shadow_opts ctxt Micro_Rust_Names.NFunction
        "AuditConfig::<a+b>::new"
    val _ =
      if suppress_warning then ()
      else error "urust_notation configuration did not canonicalize its name"
  in end
\<close>

end
