theory Parser_Test_Printer
  imports Parser_Test_Utils
begin

declare [[urust_pp_test = true]]

section\<open> Canonical AST printer \<close>

ML\<open>
structure Parser_Printer_Test =
struct
  fun assert label condition =
    if condition then () else error label

  fun parse_input source =
    (case URust_Parser.parse_source \<^context>
        source of
       SOME expression => expression
     | NONE => error "printer test parsed empty source")

  fun parse source =
    parse_input (Parser_Lex_Util.text_source source)

  fun render options source =
    URust_Printer.string_of_expr options (parse source)

  fun render_margin margin options source =
    URust_Printer.pretty_expr options (parse source)
    |> Pretty.string_of_ops (Pretty.pure_output_ops (SOME margin))

  fun human_idempotence source =
    let
      val first = render URust_Printer.human_options source
      val second = render URust_Printer.human_options first
    in
      assert
        ("human printer idempotence failed for " ^ quote source ^
          "\nfirst:\n" ^ first ^ "\nsecond:\n" ^ second)
        (first = second)
    end

  fun canonical source expected =
    let val actual = render URust_Printer.serialized_options source in
      assert
        ("canonical printer output changed for " ^ quote source ^
          "\nexpected: " ^ quote expected ^
          "\nactual:   " ^ quote actual)
        (actual = expected)
    end

  fun expect_error label fragment action =
    (case Exn.result action () of
       Exn.Res _ => error (label ^ " unexpectedly succeeded")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           assert
             (label ^ " produced the wrong diagnostic:\n" ^
               Runtime.exn_message exn)
             (String.isSubstring fragment (Runtime.exn_message exn)))
end
\<close>

subsection\<open> Human-readable printer examples \<close>

text\<open>
The declaration corpus enables \<open>urust_pp_test\<close>, so every ordinary
\<open>urust_expr\<close> and \<open>urust_fn\<close> instance exercises serialized roundtripping.
The common \<open>pretty\<close> option changes verbosity-controlled declaration output to the
position-independent human mode inside a symbolic \<open>\<mu>\<open>...\<close>\<close> wrapper. This visual
wrapper is unrelated to source quotation syntax. Human mode removes redundant groups while retaining
groups required by precedence and grammar.
\<close>

urust_expr [pretty, verbosity = 1, conformance = false]
  printer_human_expression
  \<open>
    (((let value = 1 + 2 * 3; value)))
  \<close>

urust_fn [pretty, verbosity = 1, conformance = false]
  printer_human_function ::
  \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    let value = (((item)));
    (value + 1u64) * 2u64
  \<close>

subsection\<open> Complex human-readable printer examples \<close>

text\<open>
These declarations are deliberately large enough for the human-mode output to demonstrate
multiline blocks, indentation, nested control flow, pattern guards, precedence-sensitive grouping,
and binder markup. With this theory open in Isabelle/jEdit, the rendered right-hand sides appear in
the output panel as ordinary readable uRust, visibly enclosed by \<open>\<mu>\<open>...\<close>\<close>, rather than
elaborated HOL.
\<close>

text\<open>
The first example is a typed function with mutable state, array iteration, compound assignment, and
a final conditional. Its two command parameters appear as closure formals on the rendered
right-hand side. The printer keeps the source-level function shape while laying out each block and
statement independently.
\<close>

urust_fn [pretty, verbosity = 1, conformance = false]
  printer_human_accumulate ::
  \<open>32 word \<Rightarrow> 32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body\<close>
  (seed, limit)
  \<open>
    let mut total = seed;
    for value in [1_u32, 2_u32, 3_u32] {
      *total += value;
    }
    if *total > limit {
      *total
    } else {
      *total * 2_u32
    }
  \<close>

text\<open>
This function is a focused line-layout demonstration. Each branch contains a statement before its
result, so the InfoView output must put code after an opening brace on a new line, indent nested
blocks by two spaces, and retain \<open>} else {\<close> on one line.
\<close>

urust_fn [pretty, verbosity = 1, conformance = false]
  printer_human_line_breaks ::
  \<open>32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body\<close>
  (number)
  \<open>
    if number > 10_u32 {
      let reduced = number / 2_u32;
      if reduced > 3_u32 {
        let adjusted = reduced + 1_u32;
        adjusted
      } else {
        let unchanged = reduced;
        unchanged
      }
    } else {
      let raised = number + 10_u32;
      raised * 2_u32
    }
  \<close>

text\<open>
The second example combines nested bindings with an option match, guarded arms, and a block-valued
arm. It makes the printer's match-arm alignment and nested indentation visible.
\<close>

urust_expr [pretty, verbosity = 1, conformance = false]
  printer_human_decision_tree
  \<open>
    let floor = \<llangle>0 :: 32 word\<rrangle>;
    let candidate = \<llangle>Some (12 :: 32 word)\<rrangle>;
    match candidate {
      Some(value) if value > 10_u32 => {
        let reduced = value / 2_u32;
        reduced + 1_u32
      },
      Some(value) if value > floor => value,
      None => floor
    }
  \<close>

text\<open>
The final example returns a closure that captures an outer value. Its body contains another binding
and conditional, showing that closure bars, captured binders, and nested blocks retain their
source-level presentation.
\<close>

urust_expr [pretty, verbosity = 1, conformance = false]
  printer_human_closure_pipeline
  \<open>
    let offset = \<llangle>1 :: 32 word\<rrangle>;
    |value| {
      let adjusted = value + offset;
      if adjusted > 10_u32 {
        adjusted
      } else {
        adjusted * 2_u32
      }
    }
  \<close>

subsection\<open> Human-mode constructor and enum instances \<close>

ML_val\<open>
  let
    open Parser_Printer_Test

    val sources =
      [
        "()",
        "(left, right)",
        "[]",
        "[left, right]",
        "[value; 3]",
        "[const { value }; (COUNT + 1) as usize]",
        "Record { left: 1, right: let item = 2; item }",
        "value",
        "Module::value::<N + 1>",
        "u64::MAX",
        "0xff_u32",
        "true",
        "false",
        "\"text\\\\n\"",
        "\<llangle>1 :: nat\<rrangle>",
        "\<epsilon>\<open>undefined\<close>",
        "\<y>\<i>\<e>\<l>\<d>",
        "\<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 1]\<rrangle>",
        "l\<llangle>\"value \", item\<rrangle>",
        "|| value",
        "|left, right| left + right",
        "let item = value; item",
        "let mut item = value; item",
        "const item = value; item",
        "left; right",
        "left;",
        "return",
        "return value",
        "!value",
        "&value",
        "& mut value",
        "*value",
        "value?",
        "(value)",
        "{ value }",
        "{}",
        "if condition { left }",
        "if condition { left } else { right }",
        "if let Some(item) = value { item } else if condition { other }",
        "let Some(item) = value else { return }; item",
        "#[fuel(\<epsilon>\<open>10\<close>)] while (condition) { value }",
        "#[fuel(\<epsilon>\<open>10\<close>)] loop { value }",
        "for item in values { item }",
        "#[fuel(\<epsilon>\<open>10\<close>)] while let Some(item) = value { item }",
        "function(left, right)",
        "receiver.method::<N>(value)",
        "\<epsilon>\<open>callee\<close>(value)",
        "\<llangle>callee\<rrangle>\<^sub>1(value)",
        "\<llangle>callee\<rrangle>\<^sub>1::<N + 1>(value)",
        "record.field",
        "values[index]",
        "tuple.0",
        "tuple.15",
        "lower..upper",
        "lower..=upper",
        "target = value",
        "target += value",
        "target -= value",
        "target *= value",
        "target %= value",
        "target &= value",
        "target |= value",
        "target ^= value",
        "target <<= value",
        "target >>= value",
        "*target = value",
        "record.field = value",
        "values[index] = value",
        "\<epsilon>\<open>target\<close> = value",
        "macro_name!(left, right)",
        "macro_name![left, right]",
        "macro_name!(let item = left; item, if condition { right } else { left })",
        "matches!(value, Some(item) | None)",
        "match value { _ => 0 }",
        "match_switch value { 0 => left, 1 => right }",
        "match_case value { Some(item) => item, None => 0 }",
        "match value { item if let other = value; other == item => item }",
        "match value { Module::VALUE => 0 }",
        "match value { u64::MAX => 0 }",
        "match value { \"text\" => 0 }",
        "match value { \<llangle>expected\<rrangle> => 0 }",
        "match value { Some(item) => item }",
        "match value { (left, right) => left }",
        "match value { (item) => item }",
        "match value { &item => item }",
        "match value { & mut item => item }",
        "match value { whole @ Some(item) => whole }",
        "match value { 0..3 => 0, 3..=7 => 1 }",
        "match value { [] => 0, [head, .., tail] => head }",
        "match value { Node { left: item, right, .. } => item }",
        "match value { Some(item) | None => 0 }",
        "1 as u8",
        "1 as u16",
        "1 as u32",
        "1 as u64",
        "1 as usize",
        "1 as i32",
        "1 as i64",
        "pointer as * const u8",
        "pointer as * mut u64",
        "1 as Width"
      ]

    val operators =
      ["+", "-", "*", "/", "%", "<<", ">>", "&", "|", "^",
       "==", "!=", "<", "<=", ">", ">=", "&&", "||"]

    val operator_sources =
      map (fn operator => "left " ^ operator ^ " right") operators

    val _ = List.app human_idempotence (sources @ operator_sources)
  in
    ()
  end
\<close>

subsection\<open> Canonicalization and grouping \<close>

ML_val\<open>
  let
    open Parser_Printer_Test
    val _ = canonical "1 /* comment */ + 2" "1 + 2"
    val _ = canonical "unsafe { 1 }" "{ 1 }"
    val _ = canonical "macro_name![1, 2]" "macro_name!(1, 2)"
    val _ = canonical "match value { _ \<Rightarrow> 0, }"
      "match value { _ => 0 }"
    val _ = canonical "array::<  N + 1 , M  >" "array::<N+1, M>"
    val _ = canonical "[1, 2,]" "[1, 2]"
    val _ = canonical "{}" "{}"
    val _ = canonical "1;" "1;"
    val _ = canonical "return 1;" "return 1"
    val _ =
      assert "serialized mode discarded explicit groups"
        (render URust_Printer.serialized_options "(((1)))" = "(((1)))")
    val _ =
      assert "human mode retained redundant groups"
        (render URust_Printer.human_options "(((1)))" = "1")
    val _ =
      assert "human mode omitted a precedence-required group"
        (render URust_Printer.human_options "(1 + 2) * 3" =
          "(1 + 2) * 3")
    val _ =
      assert "right-nested subtraction lost grouping"
        (render URust_Printer.human_options "1 - (2 - 3)" =
          "1 - (2 - 3)")
    val _ =
      assert "comparison grouping was not retained"
        (render URust_Printer.human_options "(1 == 2) == false" =
          "(1 == 2) == false")
    val _ =
      assert "D134 dereference/postfix tree changed"
        (render URust_Printer.human_options "*base[index]" =
          "*base[index]")
    val _ =
      assert "D134 explicit dereference grouping was removed"
        (render URust_Printer.human_options "(*base)[index]" =
          "(*base)[index]")
    val _ =
      assert "no-struct control head lost required grouping"
        (render URust_Printer.human_options
          "if (Record { left: 1 }) { 0 }" =
          "if (Record { left: 1 }) {\n  0\n}")
  in
    ()
  end
\<close>

subsection\<open> Positions and rendering \<close>

ML_val\<open>
  let
    open Parser_Printer_Test
    val text = "let item = 1; item + 2"
    val left_source =
      Parser_Lex_Util.positioned_content_source text
        (Position.make0 10 100 0 "" "printer-left" "")
    val right_source =
      Parser_Lex_Util.positioned_content_source text
        (Position.make0 40 900 0 "" "printer-right" "")
    fun parse_source source =
      (case URust_Parser.parse_source \<^context> source of
         SOME expression => expression
       | NONE => error "position-independence source was empty")
    val left_tokens =
      URust_Printer.tokens_of_expr URust_Printer.serialized_options
        (parse_source left_source)
    val right_tokens =
      URust_Printer.tokens_of_expr URust_Printer.serialized_options
        (parse_source right_source)
    val _ =
      assert "serialized tokens retained source positions"
        (left_tokens = right_tokens)

    val wide =
      render_margin 120 URust_Printer.human_options
        "left + right + third + fourth"
    val narrow =
      render_margin 12 URust_Printer.human_options
        "left + right + third + fourth"
    val indented =
      render_margin 80 URust_Printer.human_options
        "{ let item = 1; item + 2 }"
    val conditional =
      render_margin 80 URust_Printer.human_options
        "if condition { let inner = value; inner } else { other }"
    val simple_conditional =
      render_margin 80 URust_Printer.human_options
        "if condition { left } else { right }"
    val looping =
      render_margin 80 URust_Printer.human_options
        "for item in values { item }"
    val matching =
      render_margin 80 URust_Printer.human_options
        "match value { Some(item) => { let inner = item; inner }, None => 0 }"
    val single_arm_match =
      render_margin 80 URust_Printer.human_options
        "match value { Some(item) => item }"
    val block_closure =
      render_margin 80 URust_Printer.human_options
        "|item| { item }"
    val _ = assert "wide rendering unexpectedly wrapped"
      (not (String.isSubstring "\n" wide))
    val _ = assert "narrow rendering did not wrap"
      (String.isSubstring "\n" narrow)
    val _ = assert "block rendering did not use two-space indentation"
      (String.isSubstring "\n  let item = 1;\n  item + 2\n}" indented)
    val _ =
      assert "conditional block indentation was measured from the opening brace"
        (conditional =
          "if condition {\n" ^
          "  let inner = value;\n" ^
          "  inner\n" ^
          "} else {\n" ^
          "  other\n" ^
          "}")
    val _ =
      assert "short if-else blocks were collapsed onto one line"
        (simple_conditional =
          "if condition {\n" ^
          "  left\n" ^
          "} else {\n" ^
          "  right\n" ^
          "}")
    val _ =
      assert "loop body was collapsed onto the construct line"
        (looping =
          "for item in values {\n" ^
          "  item\n" ^
          "}")
    val _ =
      assert "match and arm block indentation was measured from opening braces"
        (matching =
          "match value {\n" ^
          "  Some(item) => {\n" ^
          "    let inner = item;\n" ^
          "    inner\n" ^
          "  },\n" ^
          "  None => 0\n" ^
          "}")
    val _ =
      assert "single-arm match was collapsed onto one line"
        (single_arm_match =
          "match value {\n" ^
          "  Some(item) => item\n" ^
          "}")
    val _ =
      assert "closure block was collapsed onto the closure line"
        (block_closure =
          "|item| {\n" ^
          "  item\n" ^
          "}")
  in
    ()
  end
\<close>

subsection\<open> Verbose declaration output \<close>

ML_val\<open>
  let
    open Parser_Printer_Test

    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception true) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun parsed_body chunks =
      chunks
      |> implode
      |> YXML.parse_body

    fun plain_content chunks =
      parsed_body chunks
      |> XML.content_of
      |> Symbol.explode
      |> filter_out Symbol.is_control
      |> implode

    fun capture source_name command_text =
      let
        val ordinary =
          Synchronized.var
            ("urust_pretty_output_" ^ source_name)
            ([]: string list)
        val urgent =
          Synchronized.var
            ("urust_pretty_urgent_" ^ source_name)
            ([]: string list)
        val warnings =
          Synchronized.var
            ("urust_pretty_warnings_" ^ source_name)
            ([]: string list)
        fun collect target chunks =
          Synchronized.change target (append chunks)
        val _ =
          Unsynchronized.setmp Private_Output.warning_fn
            (collect warnings)
            (Unsynchronized.setmp Private_Output.writeln_fn
              (collect ordinary)
              (Unsynchronized.setmp Private_Output.writeln_urgent_fn
                (collect urgent)
                (run_command source_name command_text))) ()
        val ordinary_chunks = Synchronized.value ordinary
        val urgent_chunks = Synchronized.value urgent
        val warning_chunks = Synchronized.value warnings
      in
        {ordinary = plain_content ordinary_chunks,
         ordinary_body = parsed_body ordinary_chunks,
         urgent = plain_content urgent_chunks,
         warnings = plain_content warning_chunks}
      end

    fun assert_contains label expected output =
      assert
        (label ^ " is missing " ^ quote expected ^ ":\n" ^ output)
        (String.isSubstring expected output)

    fun assert_absent label unexpected output =
      assert
        (label ^ " unexpectedly contains " ^ quote unexpected ^ ":\n" ^ output)
        (not (String.isSubstring unexpected output))

    fun tree_has_marked_text expected_markup expected_text tree =
      (case XML.unwrap_elem tree of
         SOME (((actual_markup, _), _), body) =>
           (actual_markup = expected_markup andalso
             XML.content_of body = expected_text) orelse
           exists
             (tree_has_marked_text expected_markup expected_text)
             body
       | NONE =>
           (case tree of
              XML.Elem ((actual_markup, _), body) =>
                (actual_markup = expected_markup andalso
                  XML.content_of body = expected_text) orelse
                exists
                  (tree_has_marked_text expected_markup expected_text)
                  body
            | XML.Text _ => false))

    fun assert_marked_text label expected_markup expected_text body =
      assert
        (label ^ " is missing PIDE markup " ^ quote expected_markup ^
          " on " ^ quote expected_text)
        (exists
          (tree_has_marked_text expected_markup expected_text)
          body)

    fun assert_not_marked_text label unexpected_markup unexpected_text body =
      assert
        (label ^ " unexpectedly has PIDE markup " ^
          quote unexpected_markup ^ " on " ^ quote unexpected_text)
        (not
          (exists
            (tree_has_marked_text unexpected_markup unexpected_text)
            body))

    fun assert_symbolic_urust_wrapper label output body =
      let
        val opening = "\<mu>" ^ Symbol.open_
      in
        assert_contains label opening output;
        assert_contains label Symbol.close output;
        assert_marked_text label Markup.keyword1N "\<mu>" body;
        assert_marked_text label Markup.delimiterN Symbol.open_ body;
        assert_marked_text label Markup.delimiterN Symbol.close body
      end

    fun tree_has_wrapped_report
          expected_markup expected_header expected_text tree =
      (case XML.unwrap_elem tree of
         SOME (((actual_markup, _), header), body) =>
           (actual_markup = expected_markup andalso
             XML.content_of header = expected_header andalso
             XML.content_of body = expected_text) orelse
           exists
             (tree_has_wrapped_report
               expected_markup expected_header expected_text)
             body
       | NONE =>
           (case tree of
              XML.Elem (_, body) =>
                exists
                  (tree_has_wrapped_report
                    expected_markup expected_header expected_text)
                  body
            | XML.Text _ => false))

    fun assert_wrapped_report
          label expected_markup expected_header expected_text body =
      assert
        (label ^ " is missing wrapped PIDE report " ^
          quote expected_markup ^ " with payload " ^
          quote expected_header ^ " on " ^ quote expected_text)
        (exists
          (tree_has_wrapped_report
            expected_markup expected_header expected_text)
          body)

    fun wrapped_markup_properties expected_markup expected_text tree =
      (case XML.unwrap_elem tree of
         SOME (((actual_markup, properties), _), body) =>
           (if actual_markup = expected_markup andalso
                XML.content_of body = expected_text
            then [properties]
            else []) @
           maps
             (wrapped_markup_properties
               expected_markup expected_text)
             body
       | NONE =>
           (case tree of
              XML.Elem (_, body) =>
                maps
                  (wrapped_markup_properties
                    expected_markup expected_text)
                  body
            | XML.Text _ => []))

    val grouped_source =
      Symbol.open_ ^
      " (((let value = 1; value + 2))) " ^
      Symbol.close
    val function_type =
      Symbol.open_ ^
      "64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body" ^
      Symbol.close
    val function_source =
      Symbol.open_ ^
      " let value = (((item))); (value + 1u64) * 2u64 " ^
      Symbol.close
    val antiquotation_source =
      Symbol.open_ ^ " \<llangle>item :: nat\<rrangle> " ^ Symbol.close

    val pretty_expression =
      capture "pretty-expression"
        ("urust_expr " ^
          "[pretty, verbosity = 1, conformance = false] " ^
          "pretty_expression " ^ grouped_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty expression" expected
            (#ordinary pretty_expression))
        ["definition pretty_expression_def:",
         "pretty_expression \<equiv>",
         "let value = 1;",
         "value + 2"]
    val _ =
      assert_contains "pretty expression layout"
        ("pretty_expression \<equiv> \<mu>" ^ Symbol.open_ ^
          "\n  let value = 1;")
        (#ordinary pretty_expression)
    val _ =
      assert_absent "pretty expression groups"
        "(((let" (#ordinary pretty_expression)
    val _ =
      assert_absent "pretty expression urgent output"
        "definition pretty_expression_def:" (#urgent pretty_expression)
    val _ =
      assert_symbolic_urust_wrapper "pretty expression wrapper"
        (#ordinary pretty_expression) (#ordinary_body pretty_expression)
    val _ =
      assert_marked_text "pretty expression binder"
        Markup.boundN "value" (#ordinary_body pretty_expression)
    val _ =
      assert_not_marked_text "pretty expression binder"
        Markup.freeN "value" (#ordinary_body pretty_expression)
    val _ =
      List.app
        (fn (markup, text) =>
          assert_marked_text "pretty expression inherited parser markup"
            markup text (#ordinary_body pretty_expression))
        [(Markup.keyword1N, "let"),
         (Markup.delimiterN, "="),
         (Markup.numeralN, "1"),
         (Markup.operatorN, "+"),
         (Markup.typingN, "let"),
         (Markup.entityN, "value")]
    val _ =
      assert_wrapped_report
        "pretty expression inherited typing payload"
        Markup.typingN "TLET" "let"
        (#ordinary_body pretty_expression)
    val value_entities =
      maps
        (wrapped_markup_properties Markup.entityN "value")
        (#ordinary_body pretty_expression)
    val value_definitions =
      map_filter
        (fn properties => Properties.get properties Markup.defN)
        value_entities
    val value_references =
      map_filter
        (fn properties => Properties.get properties Markup.refN)
        value_entities
    val _ =
      assert
        "pretty expression did not preserve matching entity definition/reference identities"
        (exists
          (fn identity => member (op =) value_references identity)
          value_definitions)
    val _ =
      assert
        "pretty expression leaked synthetic report positions"
        (forall
          (fn properties =>
            not (exists Markup.position_property properties))
          value_entities)

    val pretty_function =
      capture "pretty-function"
        ("urust_fn " ^
          "[pretty = true, verbosity = 1, conformance = false] " ^
          "pretty_function :: " ^ function_type ^
          " (item) " ^ function_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty function" expected
            (#ordinary pretty_function))
        ["definition pretty_function_def:",
         "|item|",
         "let value = item;",
         "(value + 1u64) * 2u64"]
    val _ =
      assert_contains "pretty function layout"
        ("pretty_function \<equiv> \<mu>" ^ Symbol.open_ ^
          "\n  |item|\n    let value = item;")
        (#ordinary pretty_function)
    val _ =
      List.app
        (fn name =>
          (assert_marked_text "pretty function binder"
             Markup.boundN name (#ordinary_body pretty_function);
           assert_not_marked_text "pretty function binder"
             Markup.freeN name (#ordinary_body pretty_function)))
        ["item", "value"]
    val _ =
      assert_symbolic_urust_wrapper "pretty function wrapper"
        (#ordinary pretty_function) (#ordinary_body pretty_function)
    val _ =
      assert_marked_text "pretty function displayed formal"
        Markup.boundN "item" (#ordinary_body pretty_function)

    val pretty_abbreviation =
      capture "pretty-abbreviation"
        ("urust_expr " ^
          "[abbrev, pretty, verbosity = 1, conformance = false] " ^
          "pretty_abbreviation (item) " ^ antiquotation_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty abbreviation" expected
            (#ordinary pretty_abbreviation))
        ["abbreviation pretty_abbreviation:",
         "pretty_abbreviation \<equiv>",
         "\<llangle>item :: nat\<rrangle>"]
    val _ =
      assert_wrapped_report
        "pretty abbreviation inherited embedded HOL typing"
        Markup.typingN "nat" "item"
        (#ordinary_body pretty_abbreviation)
    val _ =
      assert_marked_text
        "pretty abbreviation inherited embedded HOL type entity"
        Markup.tconstN "nat"
        (#ordinary_body pretty_abbreviation)
    val _ =
      assert_symbolic_urust_wrapper "pretty abbreviation wrapper"
        (#ordinary pretty_abbreviation) (#ordinary_body pretty_abbreviation)

    val pretty_application =
      capture "pretty-application"
        ("urust_expr " ^
          "[application_def, pretty, verbosity = 1, conformance = false] " ^
          "pretty_application (item) " ^ antiquotation_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty application definition" expected
            (#ordinary pretty_application))
        ["definition pretty_application_def:",
         "pretty_application item \<equiv>",
         "\<llangle>item :: nat\<rrangle>"]
    val _ =
      assert_symbolic_urust_wrapper "pretty application definition wrapper"
        (#ordinary pretty_application) (#ordinary_body pretty_application)
    val _ =
      assert_absent "pretty application definition rhs abstraction"
        "|item|" (#ordinary pretty_application)

    val pretty_application_function =
      capture "pretty-application-function"
        ("urust_fn " ^
          "[application_def, pretty, verbosity = 1, conformance = false] " ^
          "pretty_application_function :: " ^ function_type ^
          " (item) " ^ function_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty application function" expected
            (#ordinary pretty_application_function))
        ["definition pretty_application_function_def:",
         "pretty_application_function item \<equiv>",
         "let value = item;",
         "(value + 1u64) * 2u64"]
    val _ =
      assert_contains "pretty application function layout"
        ("pretty_application_function item \<equiv> \<mu>" ^
          Symbol.open_ ^ "\n  let value = item;")
        (#ordinary pretty_application_function)
    val _ =
      assert_absent "pretty application function rhs abstraction"
        "|item|" (#ordinary pretty_application_function)
    val _ =
      assert_symbolic_urust_wrapper "pretty application function wrapper"
        (#ordinary pretty_application_function)
        (#ordinary_body pretty_application_function)

    val pretty_anonymous =
      capture "pretty-anonymous"
        ("urust_expr " ^
          "[pretty, verbosity = 1, conformance = false] _ " ^
          grouped_source)
    val _ =
      assert_contains "pretty anonymous result"
        "let value = 1;" (#ordinary pretty_anonymous)
    val _ =
      assert_absent "pretty anonymous definition heading"
        "definition " (#ordinary pretty_anonymous)
    val _ =
      assert_symbolic_urust_wrapper "pretty anonymous wrapper"
        (#ordinary pretty_anonymous) (#ordinary_body pretty_anonymous)

    val pretty_conformance =
      capture "pretty-conformance"
        ("urust_expr " ^
          "[pretty, verbosity = 2, conformance] " ^
          "pretty_conformance " ^
          (Symbol.open_ ^ " let item = 1; item + 2 " ^ Symbol.close))
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty conformance" expected
            (#ordinary pretty_conformance))
        ["definition pretty_conformance_def:",
         "let item = 1;",
         "theorem pretty_conformance_conformance:",
         "pretty_conformance = ",
         "+\<mu>"]
    val _ =
      assert_symbolic_urust_wrapper "pretty conformance declaration wrapper"
        (#ordinary pretty_conformance) (#ordinary_body pretty_conformance)

    val pretty_timing =
      capture "pretty-timing"
        ("urust_expr " ^
          "[pretty, verbosity = 1, timing_info, timing_verbosity = 2, " ^
          "conformance = false] " ^
          "pretty_timing " ^ grouped_source)
    val _ =
      assert_contains "pretty timing phase"
        "pretty output markup:"
        (#ordinary pretty_timing ^ #urgent pretty_timing)
    val _ =
      assert_symbolic_urust_wrapper "pretty timing wrapper"
        (#ordinary pretty_timing) (#ordinary_body pretty_timing)

    val scoped_pretty =
      capture "pretty-scoped"
        ("declare [[urust_pretty = true]]\n" ^
          "declare [[urust_verbosity = 1]]\n" ^
          "urust_expr [conformance = false] " ^
          "scoped_pretty " ^ grouped_source)
    val _ =
      assert_contains "scoped pretty"
        "let value = 1;" (#ordinary scoped_pretty)
    val _ =
      assert_symbolic_urust_wrapper "scoped pretty wrapper"
        (#ordinary scoped_pretty) (#ordinary_body scoped_pretty)

    val false_override =
      capture "pretty-false-override"
        ("declare [[urust_pretty = true]]\n" ^
          "declare [[urust_verbosity = 1]]\n" ^
          "urust_expr [pretty = false, conformance = false] " ^
          "pretty_false_override " ^ grouped_source)
    val _ =
      assert_contains "pretty false override"
        "definition pretty_false_override_def:"
        (#ordinary false_override)
    val _ =
      assert_absent "pretty false override source"
        "let value = 1;" (#ordinary false_override)
    val _ =
      assert_absent "pretty false override wrapper"
        ("\<mu>" ^ Symbol.open_) (#ordinary false_override)

    val ineffective =
      capture "pretty-ineffective"
        ("urust_expr " ^
          "[pretty, verbosity = 0, conformance = false] " ^
          "pretty_ineffective " ^ grouped_source)
    val _ =
      assert_absent "ineffective pretty output"
        "definition pretty_ineffective_def:"
        (#ordinary ineffective ^ #urgent ineffective)
    val _ =
      assert_contains "ineffective pretty warning"
        "uRust command option \"pretty\" has no effect when verbosity = 0"
        (#warnings ineffective)
  in
    ()
  end
\<close>

subsection\<open> Malformed hand-built ASTs \<close>

ML_val\<open>
  let
    open Parser_Printer_Test
    open URust_AST
    val pos = Position.none
    val unit = UE_Unit pos
    val one = UE_Literal (LP_Integer ("1", pos))
    val path = make_single_path ("value", pos)
    val matches_path = make_single_path ("matches", pos)
    val primitive_single =
      UR_Path
        (Primitive_Head (Primitive_Unsigned UT_U64),
         [Path_Segment ("u64", pos, NONE)], pos)
    fun print expression =
      URust_Printer.string_of_expr
        URust_Printer.serialized_options expression

    val _ = expect_error "empty path" "path requires at least one member"
      (fn () => print (UE_Path (UR_Path (Identifier_Head, [], pos))))
    val _ = expect_error "empty generic arguments"
      "generic argument list requires at least one member"
      (fn () =>
        print
          (UE_Path
            (UR_Path
              (Identifier_Head,
               [Path_Segment
                 ("value", pos, SOME (Generic_Args ([], pos)))],
               pos))))
    val _ = expect_error "one-element tuple expression"
      "tuple expression requires at least 2 members"
      (fn () => print (UE_Tuple ([unit], pos)))
    val _ = expect_error "one-element tuple pattern"
      "tuple pattern requires at least 2 members"
      (fn () =>
        print
          (UE_Match
            (MF_Auto, unit,
             [UR_Arm (P_Tuple ([P_Wild pos], pos), NONE, unit)], pos)))
    val _ = expect_error "empty constructor pattern"
      "constructor pattern requires at least one member"
      (fn () =>
        print
          (UE_Match
            (MF_Auto, unit,
             [UR_Arm (P_Constr (path, []), NONE, unit)], pos)))
    val _ = expect_error "empty struct pattern"
      "struct pattern requires at least one member"
      (fn () =>
        print
          (UE_Match
            (MF_Auto, unit,
             [UR_Arm (P_Struct (path, []), NONE, unit)], pos)))
    val _ = expect_error "singleton or-pattern"
      "or-pattern requires at least 2 members"
      (fn () =>
        print
          (UE_Match
            (MF_Auto, unit,
             [UR_Arm (P_Or ([P_Wild pos], pos), NONE, unit)], pos)))
    val _ = expect_error "invalid tuple projection"
      "tuple projection index 16"
      (fn () => print (UE_TupleProjection (unit, 16, pos)))
    val _ = expect_error "invalid function-literal arity"
      "outside the supported range 1 through 14"
      (fn () =>
        print
          (UE_Call
            (UC_FunLiteral
              (Parser_Lex_Util.text_source "callee", 0, pos, NONE),
             [], pos)))
    val _ = expect_error "primitive path without associated item"
      "primitive path requires an associated-item segment"
      (fn () => print (UE_Path primitive_single))
    val _ = expect_error "primitive named cast target"
      "named cast target cannot use a primitive path head"
      (fn () => print (UE_Cast (one, SCT_Named primitive_single, pos)))
    val _ = expect_error "matches arguments payload"
      "matches! requires the dedicated expression/pattern payload"
      (fn () =>
        print
          (UE_Macro
            (matches_path, pos, MP_Arguments [one], pos)))
    val _ = expect_error "wrong matches payload head"
      "MP_Matches requires the exact matches! macro head"
      (fn () =>
        print
          (UE_Macro
            (path, pos, MP_Matches (one, P_Wild pos), pos)))
    val _ = expect_error "inline const without block"
      "inline-const array repeat operand requires a block"
      (fn () =>
        print
          (UE_ArrayRepeat
            (AR_InlineConst, one, RL_Integer ("1", pos), pos)))
    val _ = expect_error "if without success block"
      "if success branch requires a block"
      (fn () => print (UE_If (one, one, NONE, pos)))
    val _ = expect_error "terminal return sequence"
      "terminal return cannot be represented"
      (fn () =>
        print (UE_Seq (UE_Return (NONE, pos), UE_Unit pos)))
  in
    ()
  end
\<close>

end
