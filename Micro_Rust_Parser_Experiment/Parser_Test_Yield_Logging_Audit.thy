theory Parser_Test_Yield_Logging_Audit
  imports Parser_Test_Logging_Negative Parser_Test_Utils
begin

section\<open> Yield and logging structural audit \<close>

text\<open>
This theory audits parser properties that equation-based conformance tests cannot expose directly:
the yield, primitive-log, and log-data ASTs and source spans; exact lowering shape; local-first
identifier resolution; editor markup; positioned diagnostics; and lexer/parser recovery after
malformed input.
\<close>

definition yield_logging_audit_collision :: nat
  where \<open> yield_logging_audit_collision = 17 \<close>

definition yield_logging_audit_notation_target :: nat
  where \<open> yield_logging_audit_notation_target = 99 \<close>

micro_rust_notation (literal) yield_logging_audit_notation_target
  ("yield_logging_audit_collision")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("yield/logging regression audit: " ^ message)

    fun parse source =
      (case URust_Diagnostics.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "yield/logging regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      URust_Command.elab_urust ctxt
        (Parser_Lex_Util.text_source text)

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("yield/logging regression audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun dest_application expected term =
      (case Term.strip_comb (Term_Position.strip_positions term) of
         (Const (name, _), arguments) =>
           if name = expected then arguments
           else
             error
               ("yield/logging regression audit: expected " ^ quote expected ^
                ", found " ^ quote name)
       | _ =>
           error
             ("yield/logging regression audit: expected application of " ^
              quote expected))

    fun append_entries term =
      (case Term.strip_comb (Term_Position.strip_positions term) of
         (Const (name, _), [first, rest]) =>
           if name = \<^const_name>\<open>List.append\<close>
           then first :: append_entries rest
           else [term]
       | _ => [term])

    val yield_text = "\<y>\<i>\<e>\<l>\<d>"
    val yield_start =
      Position.make0 11 100 0 "" "" "yield-logging-yield-ast"
    val yield_source =
      Parser_Lex_Util.positioned_content_source yield_text yield_start
    val yield_span =
      Position.range_position
        (yield_start, Position.symbol_explode yield_text yield_start)
    val _ =
      (case parse yield_source of
         UE_Yield pos =>
           audit_assert "yield AST span changed"
             (same_range pos yield_span)
       | _ => error "yield/logging regression audit: yield AST changed")

    val primitive_text =
      "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 1]\<rrangle>"
    val primitive_start =
      Position.make0 21 200 0 "" "" "yield-logging-log-ast"
    val primitive_stop =
      Position.symbol_explode primitive_text primitive_start
    val primitive_source =
      Parser_Lex_Util.positioned_content_source
        primitive_text primitive_start
    val _ =
      (case parse primitive_source of
         UE_Log (priority, data, pos) =>
           (audit_assert "primitive-log priority source changed"
              (Symbol.trim_blanks (Input.string_of priority) = "Error");
            audit_assert "primitive-log data source changed"
              (Symbol.trim_blanks (Input.string_of data) = "[LogNat 1]");
            audit_assert "primitive-log span changed"
              (Position.offset_of pos =
                 Position.offset_of primitive_start andalso
               Position.end_offset_of pos =
                 Position.offset_of primitive_stop))
       | _ => error "yield/logging regression audit: primitive-log AST changed")

    val data_text =
      "l\<llangle>\"left, // \<rrangle> text\", True\<rrangle>"
    val data_start =
      Position.make0 31 300 0 "" "" "yield-logging-data-ast"
    val data_stop =
      Position.symbol_explode data_text data_start
    val data_source =
      Parser_Lex_Util.positioned_content_source data_text data_start
    val (string_raw, string_pos, identifier_pos, data_pos) =
      (case parse data_source of
         UE_LogData
           ([LDE_String (raw, first_pos),
             LDE_Identifier ("True", second_pos)],
            pos) =>
           (raw, first_pos, second_pos, pos)
       | _ => error "yield/logging regression audit: log-data AST changed")
    val _ =
      audit_assert "log-data string terminated at embedded syntax"
        (string_raw = "\"left, // \<rrangle> text\"")
    val _ =
      audit_assert "log-data span changed"
        (Position.offset_of data_pos = Position.offset_of data_start andalso
         Position.end_offset_of data_pos = Position.offset_of data_stop)
    val (_, expected_string_pos) =
      token_position data_text data_start
        "\"left, // \<rrangle> text\"" 0
    val (_, expected_identifier_pos) =
      token_position data_text data_start "True" 0
    val _ =
      audit_assert "log-data entry spans changed"
        (same_range string_pos expected_string_pos andalso
         same_range identifier_pos expected_identifier_pos)

    val yield_term = checked yield_text
    val _ =
      audit_assert "yield no longer lowers directly to pause"
        (case Term_Position.strip_positions yield_term of
           Const (name, _) => name = \<^const_name>\<open>pause\<close>
         | _ => false)

    val primitive_term = checked primitive_text
    val primitive_arguments =
      dest_application \<^const_name>\<open>log\<close> primitive_term
    val _ =
      audit_assert "primitive log is not a direct two-argument log"
        (length primitive_arguments = 2)
    val _ =
      audit_assert "primitive-log operands gained literal wrappers"
        (count_constant \<^const_name>\<open>literal\<close> primitive_term = 0)

    val singleton_string = checked "l\<llangle>\"only\"\<rrangle>"
    val singleton_string_value =
       (case dest_application \<^const_name>\<open>literal\<close>
          singleton_string of
         [value] => value
       | _ => error "yield/logging regression audit: string literal arity changed")
    val _ =
      audit_assert "singleton string gained List.append"
        (count_constant \<^const_name>\<open>List.append\<close>
           singleton_string = 0)
    val singleton_elements =
      dest_application \<^const_name>\<open>List.Cons\<close>
        singleton_string_value
    val _ =
      audit_assert "singleton string lost its LogString list"
        (case singleton_elements of
           [head, tail] =>
             length
               (dest_application \<^const_name>\<open>LogString\<close>
                 head) = 1 andalso
             (case Term_Position.strip_positions tail of
                Const (name, _) =>
                  name = \<^const_name>\<open>List.Nil\<close>
              | _ => false)
         | _ => false)

    val singleton_identifier = checked "l\<llangle>True\<rrangle>"
    val _ =
      audit_assert "singleton identifier gained List.append"
        (count_constant \<^const_name>\<open>List.append\<close>
           singleton_identifier = 0)
    val _ =
      audit_assert "singleton identifier did not lower once through generate_debug"
        (count_constant \<^const_name>\<open>generate_debug\<close>
           singleton_identifier = 1)

    val mixed =
      checked "l\<llangle>\"a\", True, \"b\", False\<rrangle>"
    val mixed_value =
      (case dest_application \<^const_name>\<open>literal\<close> mixed of
         [value] => value
       | _ => error "yield/logging regression audit: mixed literal arity changed")
    val source_entries = append_entries mixed_value
    val _ =
      audit_assert "log data did not use a right-associated append tree"
        (length source_entries = 4 andalso
         count_constant \<^const_name>\<open>List.append\<close> mixed = 3)
    val _ =
      (case source_entries of
         [first, second, third, fourth] =>
           (audit_assert "first source entry changed"
              (count_constant \<^const_name>\<open>LogString\<close> first = 1);
            audit_assert "second source entry changed"
              (count_constant \<^const_name>\<open>generate_debug\<close> second = 1 andalso
               count_constant \<^const_name>\<open>True\<close> second = 1);
            audit_assert "third source entry changed"
              (count_constant \<^const_name>\<open>LogString\<close> third = 1);
            audit_assert "fourth source entry changed"
              (count_constant \<^const_name>\<open>generate_debug\<close> fourth = 1 andalso
               count_constant \<^const_name>\<open>False\<close> fourth = 1))
       | _ => error "yield/logging regression audit: mixed source order changed")
    val _ =
      audit_assert "log data no longer has exactly one literal wrapper"
        (count_constant \<^const_name>\<open>literal\<close> mixed = 1)

    val collision = checked "l\<llangle>yield_logging_audit_collision\<rrangle>"
    val _ =
      audit_assert "log-data identifier used micro_rust_notation dispatch"
        (count_constant \<^const_name>\<open>yield_logging_audit_collision\<close>
           collision = 1 andalso
         count_constant \<^const_name>\<open>yield_logging_audit_notation_target\<close>
           collision = 0 andalso
         count_constant \<^const_name>\<open>urust_dispatch\<close>
           collision = 0)

    val shadowed =
      checked
        ("let yield_logging_audit_collision = \<llangle>5 :: nat\<rrangle>; " ^
         "l\<llangle>yield_logging_audit_collision, yield_logging_audit_collision\<rrangle>")
    val _ =
      audit_assert "lexical log-data identifier did not shadow the HOL constant"
        (count_constant \<^const_name>\<open>yield_logging_audit_collision\<close>
           shadowed = 0 andalso
         count_constant \<^const_name>\<open>yield_logging_audit_notation_target\<close>
           shadowed = 0 andalso
         count_constant \<^const_name>\<open>generate_debug\<close>
           shadowed = 2)

    val markup_text =
      "let local = \<llangle>True\<rrangle>; " ^
      "{ \<y>\<i>\<e>\<l>\<d>; " ^
      "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[]\<rrangle>; " ^
      "l\<llangle>\"text, //\", local, True\<rrangle> }"
    val markup_start =
      Position.make0 41 400 0 "" "" "yield-logging-markup"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        markup_text markup_start
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (URust_Command.elab_urust ctxt markup_source)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)
    fun has_markup name pos =
      exists
        (fn (candidate, properties) =>
          candidate = name andalso has_position properties pos)
        markup
    fun has_any_entity pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun entity_id property pos =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties pos
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ => error "yield/logging regression audit: binder entity markup changed")
      end

    val (local_def_raw, local_definition) =
      token_position markup_text markup_start "local" 0
    val (yield_raw, yield_keyword) =
      token_position markup_text markup_start yield_text 0
    val (log_raw, log_keyword) =
      token_position markup_text markup_start
        "\<l>\<o>\<g>" yield_raw
    val (data_open_raw, data_l) =
      token_position markup_text markup_start
        "l\<llangle>" log_raw
    val data_open_symbol =
      Position.range_position
        (Position.symbol_explode "l" data_l,
         Position.symbol_explode "l\<llangle>" data_l)
    val data_l_symbol =
      Position.range_position
        (data_l, Position.symbol_explode "l" data_l)
    val (string_token_raw, string_token_pos) =
      token_position markup_text markup_start "\"text, //\"" data_open_raw
    val (first_separator_raw, first_separator_pos) =
      token_position markup_text markup_start ","
        (string_token_raw + size "\"text, //\"")
    val (local_ref_raw, local_reference) =
      token_position markup_text markup_start "local"
        (local_def_raw + size "local")
    val (_, second_separator_pos) =
      token_position markup_text markup_start ","
        (local_ref_raw + size "local")
    val (true_ref_raw, true_reference) =
      token_position markup_text markup_start "True"
        (local_ref_raw + size "local")
    val (_, data_close_pos) =
      token_position markup_text markup_start "\<rrangle>" true_ref_raw
    val (_, internal_comma_pos) =
      token_position markup_text markup_start "," string_token_raw

    val _ =
      List.app
        (fn (label, pos) =>
          (audit_assert (label ^ " lost role markup")
             (has_markup Markup.keyword1N pos);
           audit_assert (label ^ " lost typing markup")
             (has_markup Markup.typingN pos);
           audit_assert (label ^ " received identifier entity markup")
             (not (has_any_entity pos))))
        [("yield keyword", yield_keyword),
         ("log keyword", log_keyword),
         ("log-data l", data_l_symbol)]
    val _ =
      List.app
        (fn (label, pos) =>
          (audit_assert (label ^ " lost delimiter markup")
             (has_markup Markup.delimiterN pos);
           audit_assert (label ^ " lost typing markup")
             (has_markup Markup.typingN pos)))
        [("log-data opener", data_open_symbol),
         ("log-data closer", data_close_pos),
         ("first separator", first_separator_pos),
         ("second separator", second_separator_pos)]
    val _ =
      (audit_assert "log-data string lost inner-string markup"
         (has_markup Markup.inner_stringN string_token_pos);
       audit_assert "log-data string lost typing markup"
         (has_markup Markup.typingN string_token_pos);
       audit_assert "comma inside a string received delimiter markup"
         (not (has_markup Markup.delimiterN internal_comma_pos)))
    val _ =
      (audit_assert "local log-data reference lost bound markup"
         (has_markup Markup.boundN local_reference);
       audit_assert "local log-data reference lost typing markup"
         (has_markup Markup.typingN local_reference);
       audit_assert "local log-data reference stopped targeting its binder"
         (entity_id Markup.defN local_definition =
          entity_id Markup.refN local_reference);
       audit_assert "ordinary HOL log-data identifier lost typing markup"
         (has_markup Markup.typingN true_reference);
       audit_assert "ordinary HOL log-data identifier lost constant markup"
         (has_entity_markup Markup.constantN true_reference))

    fun expect_failure operation source =
      (case Exn.result operation source of
         Exn.Res _ =>
           error
             ("yield/logging regression audit: expected rejection of " ^
              quote source)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())

    fun assert_recovered () =
      (case parse_text yield_text of
         UE_Yield _ => ()
       | _ => error "yield/logging regression audit: yield did not recover";
       case parse_text primitive_text of
         UE_Log _ => ()
       | _ => error "yield/logging regression audit: primitive log did not recover";
       case parse_text "l\<llangle>\"ok\", True\<rrangle>" of
         UE_LogData _ => ()
       | _ => error "yield/logging regression audit: log data did not recover";
       ignore (checked yield_text);
       ignore (checked primitive_text);
       ignore (checked "l\<llangle>True\<rrangle>"))

    val malformed =
      ["l\<llangle>\<rrangle>",
       "l\<llangle>, True\<rrangle>",
       "l\<llangle>True,\<rrangle>",
       "l\<llangle>True,, False\<rrangle>",
       "l\<llangle>True False\<rrangle>",
       "l\<llangle>1\<rrangle>",
       "l\<llangle>\<llangle>True\<rrangle>\<rrangle>",
       "l\<llangle>Foo::Bar\<rrangle>",
       "l\<llangle>True()\<rrangle>",
       "l\<llangle>True + False\<rrangle>",
       "l\<llangle>l\<llangle>True\<rrangle>\<rrangle>",
       "l \<llangle>True\<rrangle>",
       "\<rrangle>",
       "l\<llangle>\"unterminated",
       "l\<llangle>\"text\", True",
       "\<l>\<o>\<g>",
       "\<l>\<o>\<g> \<llangle>Error\<rrangle>",
       "\<l>\<o>\<g> \<epsilon>\<open>literal Error\<close> \<llangle>[]\<rrangle>",
       "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[]\<rrangle> \<llangle>[]\<rrangle>",
       "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[]"]
    val _ =
      List.app
        (fn source =>
          (expect_failure
             (fn text => parse_text text) source;
           assert_recovered ()))
        malformed

    fun failure_message source =
      (case Exn.result
         (fn () => parse source) () of
         Exn.Res _ =>
           error "yield/logging regression audit: positioned malformed source parsed"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else XML.content_of (YXML.parse_body (Runtime.exn_message exn)))

    val opener_source =
      Parser_Lex_Util.positioned_content_source
        "l\<llangle>\n\"text\", True"
        (Position.make0 101 1000 0 "" "" "yield-logging-opener-error")
    val _ =
      audit_assert "unterminated log data moved away from its opener"
        (String.isSubstring "unterminated log data"
           (failure_message opener_source) andalso
         String.isSubstring "line 101"
           (failure_message opener_source))

    val grammar_source =
      Parser_Lex_Util.positioned_content_source
        "l\<llangle>\n, True\<rrangle>"
        (Position.make0 201 2000 0 "" "" "yield-logging-grammar-error")
    val _ =
      audit_assert "log-data grammar error moved away from the bad separator"
        (String.isSubstring "line 202"
           (failure_message grammar_source))

    val string_source =
      Parser_Lex_Util.positioned_content_source
        "l\<llangle>\n\"unterminated"
        (Position.make0 301 3000 0 "" "" "yield-logging-string-error")
    val _ =
      audit_assert "log-data string error moved away from its quote"
        (String.isSubstring "malformed or unterminated string literal"
           (failure_message string_source) andalso
         String.isSubstring "line 302"
           (failure_message string_source))
  in
    val _ =
      writeln
        "Yield/log AST, term-shape, scope, markup, diagnostics, and recovery regressions passed"
  end
\<close>

end
