theory Parser_Syntax_Tests
  imports Parser_Command_Tests Parser_Rejection_Tests
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open>AST source layouts\<close>

text\<open>
Composite AST nodes retain their complete diagnostic span separately from exact source-token
ranges. This syntax-only audit uses positioned inputs containing Isabelle symbols so byte offsets
cannot accidentally stand in for symbol offsets.
\<close>

ML_val\<open>
  let
    open URust_AST

    fun audit_assert label condition =
      if condition then ()
      else error ("source-layout regression audit: " ^ label)

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("source-layout regression audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun expected_position lex_layout raw spelling =
      Position.range_position
        (Parser_Lex_Util.text_range lex_layout (raw, spelling))

    fun expected_tokens source specifications =
      let
        val text = Input.text_of source
        val lex_layout = Parser_Lex_Util.make_source_layout source
        fun collect [] _ = []
          | collect ((role, spelling) :: rest) cursor =
              let
                val raw = find_from text spelling cursor
              in
                (role, expected_position lex_layout raw spelling) ::
                  collect rest (raw + size spelling)
              end
      in collect specifications 0 end

    fun assert_layout label source layout specifications =
      let
        val text = Input.text_of source
        val lex_layout = Parser_Lex_Util.make_source_layout source
        val expected_span = expected_position lex_layout 0 text
        val expected = expected_tokens source specifications
        val actual = source_tokens layout
        fun same_token
            ((left_role, left_pos), (right_role, right_pos)) =
          left_role = right_role andalso same_range left_pos right_pos
      in
        audit_assert (label ^ " complete span changed")
          (same_range (source_span layout) expected_span);
        audit_assert (label ^ " exact token list changed")
          (length actual = length expected andalso
           ListPair.allEq same_token (actual, expected))
      end

    fun assert_nested_layout label source layout span_text
        specifications =
      let
        val text = Input.text_of source
        val lex_layout = Parser_Lex_Util.make_source_layout source
        val span_raw = find_from text span_text 0
        val expected_span =
          expected_position lex_layout span_raw span_text
        val expected = expected_tokens source specifications
        val actual = source_tokens layout
        fun same_token
            ((left_role, left_pos), (right_role, right_pos)) =
          left_role = right_role andalso
          same_range left_pos right_pos
      in
        audit_assert (label ^ " complete span changed")
          (same_range (source_span layout) expected_span);
        audit_assert (label ^ " exact token list changed")
          (length actual = length expected andalso
           ListPair.allEq same_token (actual, expected))
      end

    fun assert_token_at label source layout role spelling cursor =
      let
        val text = Input.text_of source
        val lex_layout = Parser_Lex_Util.make_source_layout source
        val raw = find_from text spelling cursor
        val expected = expected_position lex_layout raw spelling
      in
        (case source_token_positions layout role of
           [actual] =>
             audit_assert (label ^ " exact range changed")
               (same_range actual expected)
         | _ =>
             error
               ("source-layout regression audit: " ^ label ^
                " token multiplicity changed"))
      end

    fun positioned label text =
      Parser_Lex_Util.positioned_content_source text
        (Position.make0 17 300 0 "" "" label)

    fun parse source =
      (case URust_Parser.parse_source \<^context> source of
         SOME expression => expression
       | NONE => error "source-layout regression audit: empty parse")

    val binding_source =
      positioned "source-layout-binding"
        "let mut slot = true; slot"
    val _ =
      (case parse binding_source of
         UE_LetMut
           (_, UE_Literal boolean, _, binding_layout) =>
           (assert_layout "mutable binding" binding_source binding_layout
              [(Keyword_Token "let", "let"),
               (Keyword_Token "mut", "mut"),
               (Delimiter_Token "=", "="),
               (Delimiter_Token ";", ";")];
            assert_token_at "boolean literal" binding_source
              (literal_source_layout boolean)
              (Keyword_Token "true") "true" 0)
       | _ =>
           error "source-layout regression audit: mutable binding AST changed")

    val sequence_source =
      positioned "source-layout-sequence" "left; return right"
    val return_source =
      positioned "source-layout-return" "return right"
    val _ =
      (case parse sequence_source of
         UE_Seq (_, UE_Return _, sequence_layout) =>
           assert_layout "sequence" sequence_source sequence_layout
             [(Delimiter_Token ";", ";")]
       | _ =>
           error "source-layout regression audit: sequence AST changed")
    val _ =
      (case parse return_source of
         UE_Return (_, return_layout) =>
           assert_layout "return" return_source return_layout
             [(Keyword_Token "return", "return")]
       | _ =>
           error "source-layout regression audit: return AST changed")

    val conditional_source =
      positioned "source-layout-conditional"
        "if \<llangle>condition\<rrangle> { true } else { false }"
    val _ =
      (case parse conditional_source of
         UE_If
           (_, UE_Block (UE_Literal true_payload, _),
            SOME (UE_Block (UE_Literal false_payload, _)),
            conditional_layout) =>
           (assert_layout "conditional" conditional_source
              conditional_layout
              [(Keyword_Token "if", "if"),
               (Keyword_Token "else", "else")];
            audit_assert "true literal token changed"
              (same_range
                (the_source_token_position
                  (literal_source_layout true_payload)
                  (Keyword_Token "true"))
                (#2
                  (hd
                    (expected_tokens conditional_source
                      [(Keyword_Token "true", "true")]))));
            assert_token_at "false literal" conditional_source
              (literal_source_layout false_payload)
              (Keyword_Token "false") "false" 0)
       | _ =>
           error "source-layout regression audit: conditional AST changed")

    fun audit_integer_literal label spelling numeric suffix =
      let
        val source =
          positioned ("source-layout-integer-" ^ label)
            ("true; " ^ spelling)
        val text = Input.text_of source
        val lex_layout = Parser_Lex_Util.make_source_layout source
        val literal_raw = find_from text spelling 0
        val numeric_raw = find_from text numeric literal_raw
        val expected_literal =
          expected_position lex_layout literal_raw spelling
        val expected_numeric =
          expected_position lex_layout numeric_raw numeric
        val expected_suffix =
          Option.map
            (fn suffix_text =>
              let
                val suffix_raw =
                  find_from text suffix_text
                    (numeric_raw + size numeric)
              in
                expected_position lex_layout suffix_raw suffix_text
              end)
            suffix
        val integer =
          (case parse source of
             UE_Seq (_, UE_Literal (LP_Integer integer), _) =>
               integer
           | _ =>
               error
                 ("source-layout regression audit: " ^
                   label ^ " integer AST changed"))
      in
        audit_assert (label ^ " complete literal range changed")
          (same_range
            (integer_literal_position integer)
            expected_literal);
        audit_assert (label ^ " numeric portion range changed")
          (same_range
            (integer_literal_numeric_position integer)
            expected_numeric);
        audit_assert (label ^ " suffix range changed")
          (case
              (integer_literal_suffix_position integer,
               expected_suffix) of
             (NONE, NONE) => true
           | (SOME actual, SOME expected) =>
               same_range actual expected
           | _ => false)
      end

    val _ =
      audit_integer_literal
        "decimal-unsuffixed" "42" "42" NONE
    val _ =
      audit_integer_literal
        "binary-suffixed" "0b10_01u8" "0b10_01" (SOME "u8")
    val _ =
      audit_integer_literal
        "octal-compatibility-suffix"
        "0o7_5_u16" "0o7_5" (SOME "_u16")
    val _ =
      audit_integer_literal
        "hexadecimal-suffixed"
        "0xff_00u32" "0xff_00" (SOME "u32")

    val value_antiquotation_input =
      positioned "source-layout-value-antiquotation"
        "true; \<llangle>value\<rrangle>"
    val value_antiquotation_text =
      Input.text_of value_antiquotation_input
    val value_antiquotation_lex_layout =
      Parser_Lex_Util.make_source_layout
        value_antiquotation_input
    val value_antiquotation_raw =
      find_from value_antiquotation_text
        "\<llangle>value\<rrangle>" 0
    val value_antiquotation_expected_span =
      expected_position value_antiquotation_lex_layout
        value_antiquotation_raw "\<llangle>value\<rrangle>"
    val value_antiquotation_expected_tokens =
      expected_tokens value_antiquotation_input
        [(Literal_Token, "\<llangle>"),
         (Literal_Token, "\<rrangle>")]
    val _ =
      (case parse value_antiquotation_input of
         UE_Seq
           (_, UE_Literal (LP_ValAntiq antiquotation), _) =>
           let
             val layout =
               value_antiquotation_source_layout antiquotation
             val actual_tokens = source_tokens layout
             fun same_token
                 ((left_role, left_pos),
                  (right_role, right_pos)) =
               left_role = right_role andalso
               same_range left_pos right_pos
           in
             audit_assert
               "value antiquotation complete span changed"
               (same_range
                 (source_span layout)
                 value_antiquotation_expected_span);
             audit_assert
               "value antiquotation delimiter ranges changed"
               (length actual_tokens =
                  length value_antiquotation_expected_tokens andalso
                ListPair.allEq same_token
                  (actual_tokens,
                   value_antiquotation_expected_tokens));
             audit_assert
               "value antiquotation body source changed"
               (Input.string_of
                  (value_antiquotation_source antiquotation) =
                "value")
           end
       | _ =>
           error
             "source-layout regression audit: value antiquotation AST changed")

    val while_source =
      positioned "source-layout-while"
        "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (true) { () }"
    val _ =
      (case parse while_source of
         UE_While (_, _, _, layout) =>
           assert_layout "fuelled while" while_source layout
             [(Delimiter_Token "#[", "#["),
              (Keyword_Token "fuel", "fuel"),
              (Delimiter_Token "]", "]"),
              (Keyword_Token "while", "while"),
              (Delimiter_Token "(", "("),
              (Delimiter_Token ")", ")")]
       | _ =>
           error "source-layout regression audit: while AST changed")

    val loop_source =
      positioned "source-layout-loop"
        "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () }"
    val _ =
      (case parse loop_source of
         UE_Loop (_, _, layout) =>
           assert_layout "fuelled loop" loop_source layout
             [(Delimiter_Token "#[", "#["),
              (Keyword_Token "fuel", "fuel"),
              (Delimiter_Token "]", "]"),
              (Keyword_Token "loop", "loop")]
       | _ =>
           error "source-layout regression audit: loop AST changed")

    val while_let_source =
      positioned "source-layout-while-let"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
         "Some(_) = value { () }")
    val _ =
      (case parse while_let_source of
         UE_WhileLet (_, _, _, _, layout) =>
           assert_layout "fuelled while let"
             while_let_source layout
             [(Delimiter_Token "#[", "#["),
              (Keyword_Token "fuel", "fuel"),
              (Delimiter_Token "]", "]"),
              (Keyword_Token "while", "while"),
              (Keyword_Token "let", "let"),
              (Delimiter_Token "=", "=")]
       | _ =>
           error
             "source-layout regression audit: while-let AST changed")

    val slice_source =
      positioned "source-layout-slice-pattern"
        "match values { [head, .., tail] => head, _ => 0 }"
    val _ =
      (case parse slice_source of
         UE_Match
           (_, _,
            UR_Arm (P_Slice (_, layout), _, _, _) :: _, _) =>
           assert_nested_layout "slice pattern" slice_source
             layout "[head, .., tail]"
             [(Delimiter_Token "[", "["),
              (Delimiter_Token "..", ".."),
              (Delimiter_Token "]", "]")]
       | _ =>
           error
             "source-layout regression audit: slice AST changed")

    val for_source =
      positioned "source-layout-for" "for item in items { item }"
    val _ =
      (case parse for_source of
         UE_For (_, _, _, layout) =>
           assert_layout "for loop" for_source layout
             [(Keyword_Token "for", "for"),
              (Keyword_Token "in", "in")]
       | _ =>
           error "source-layout regression audit: for AST changed")

    val postfix_source =
      positioned "source-layout-postfix" "target(value)[0].field"
    val _ =
      (case parse postfix_source of
         UE_Field
           (UE_Index
             (UE_Call (_, _, call_layout), _, index_layout),
            "field", field_layout) =>
           (assert_layout "call"
              (positioned "source-layout-call" "target(value)")
              call_layout
              [(Delimiter_Token "(", "("),
               (Delimiter_Token ")", ")")];
            audit_assert "index delimiters changed"
              (map #1 (source_tokens index_layout) =
                [Delimiter_Token "[", Delimiter_Token "]"]);
            assert_token_at "index opener" postfix_source index_layout
              (Delimiter_Token "[") "[" 0;
            assert_token_at "index closer" postfix_source index_layout
              (Delimiter_Token "]") "]" 0;
            audit_assert "field selector tokens changed"
              (map #1 (source_tokens field_layout) =
                [Delimiter_Token ".", Name_Token]);
            assert_token_at "field dot" postfix_source field_layout
              (Delimiter_Token ".") "." 0;
            assert_token_at "field name" postfix_source field_layout
              Name_Token "field" 0)
       | _ =>
           error "source-layout regression audit: postfix AST changed")

    val operator_source =
      positioned "source-layout-operators"
        "slot += lower + upper..=limit as usize"
    val _ =
      (case parse operator_source of
         UE_Assign
           (AssignAdd, _, UE_Range
             (RK_Inclusive, UE_Bin (_, _, _, binary_layout),
              UE_Cast (_, _, cast_layout), range_layout),
            assign_layout) =>
           (audit_assert "assignment operator token changed"
              (map #1 (source_tokens assign_layout) = [Operator_Token]);
            assert_token_at "assignment operator" operator_source
              assign_layout Operator_Token "+=" 0;
            assert_token_at "binary operator" operator_source
              binary_layout Operator_Token "+" 7;
            assert_token_at "range operator" operator_source
              range_layout Operator_Token "..=" 0;
            assert_token_at "cast keyword" operator_source
              cast_layout (Keyword_Token "as") "as" 0)
       | _ =>
           error "source-layout regression audit: operator AST changed")

    val match_source =
      positioned "source-layout-match"
        ("match_switch value { " ^
         "whole @ & mut Some(1..=2) if guard => true, _ => false }")
    val _ =
      (case parse match_source of
         UE_Match
           (MF_Switch, _,
            UR_Arm
              (P_Alias
                (_, _, P_Borrow
                  (BM_Mut,
                   P_Constr
                     (_, [P_Range (_, _, _, range_layout)],
                      constructor_layout),
                   borrow_layout),
                 alias_layout),
               SOME (_, _), UE_Literal _, arm_layout) :: _,
            match_layout) =>
           (assert_layout "match" match_source match_layout
              [(Keyword_Token "match_switch", "match_switch"),
               (Delimiter_Token "{", "{"),
               (Delimiter_Token "}", "}")];
            audit_assert "guarded arm controls changed"
              (map #1 (source_tokens arm_layout) =
                [Keyword_Token "if", Delimiter_Token "=>"]);
            assert_token_at "arm guard" match_source arm_layout
              (Keyword_Token "if") "if" 0;
            assert_token_at "arm arrow" match_source arm_layout
              (Delimiter_Token "=>") "=>" 0;
            audit_assert "alias control changed"
              (map #1 (source_tokens alias_layout) = [Operator_Token]);
            assert_token_at "pattern alias" match_source alias_layout
              Operator_Token "@" 0;
            audit_assert "borrow controls changed"
              (map #1 (source_tokens borrow_layout) =
                [Operator_Token, Keyword_Token "mut"]);
            assert_token_at "pattern borrow" match_source borrow_layout
              Operator_Token "&" 0;
            assert_token_at "pattern mut" match_source borrow_layout
              (Keyword_Token "mut") "mut" 0;
            audit_assert "constructor delimiters changed"
              (map #1 (source_tokens constructor_layout) =
                [Delimiter_Token "(", Delimiter_Token ")"]);
            assert_token_at "constructor opener" match_source
              constructor_layout (Delimiter_Token "(") "(" 0;
            assert_token_at "constructor closer" match_source
              constructor_layout (Delimiter_Token ")") ")" 0;
            audit_assert "pattern range control changed"
              (map #1 (source_tokens range_layout) = [Operator_Token]);
            assert_token_at "pattern range" match_source range_layout
              Operator_Token "..=" 0)
       | _ =>
           error "source-layout regression audit: match AST changed")

    val macro_source =
      positioned "source-layout-macros"
        "Module::invoke!(matches!(true, _))"
    val _ =
      (case parse macro_source of
         UE_Macro
           (_, MP_Arguments
             [UE_Macro (_, MP_Matches _, matches_layout)],
            macro_layout) =>
           (audit_assert "registered macro controls changed"
              (map #1 (source_tokens macro_layout) =
                [Bang_Token,
                 Delimiter_Token "(", Delimiter_Token ")"]);
            assert_token_at "registered macro bang" macro_source
              macro_layout Bang_Token "!" 0;
            audit_assert "matches macro controls changed"
              (map #1 (source_tokens matches_layout) =
                [Keyword_Token "matches", Bang_Token,
                 Delimiter_Token "(", Delimiter_Token ",",
                 Delimiter_Token ")"]);
            assert_token_at "matches macro bang" macro_source
              matches_layout Bang_Token "!" 16)
       | _ =>
           error "source-layout regression audit: macro AST changed")
  in
    writeln "AST source-layout regressions passed"
  end
\<close>

section\<open>Expression precedence\<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context
  fixes prefix_ref :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  fixes prefix_bool_ref :: \<open>(unit, unit, bool) Global_Store.ref\<close>
begin

urust_expr grammar_deref_before_cast
  \<open> *prefix_ref as u8 \<close>

urust_expr grammar_not_deref
  \<open> !*prefix_bool_ref \<close>

end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

urust_expr grammar_if_left_operand
  \<open>
    if true { \<llangle>1 :: 32 word\<rrangle> }
    else { \<llangle>2 :: 32 word\<rrangle> }
    + \<llangle>3 :: 32 word\<rrangle>
  \<close>

urust_expr grammar_match_left_operand
  \<open>
    match true {
      true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
      false \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>
    } + \<llangle>3 :: 32 word\<rrangle>
  \<close>

urust_expr grammar_semicolon_free_if_statement
  \<open> if true { () } else { () } () \<close>

urust_expr_rejects
  \<open>
    if true { \<llangle>1 :: 32 word\<rrangle> }
    else { \<llangle>2 :: 32 word\<rrangle> }
    + \<llangle>3 :: 32 word\<rrangle>
    ()
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    (if true { \<llangle>1 :: 32 word\<rrangle> }
     else { \<llangle>2 :: 32 word\<rrangle> })
    + \<llangle>3 :: 32 word\<rrangle>
    ()
  \<close>
  \<open> syntax error \<close>

section\<open>Match-arm separators\<close>

text\<open>
A direct with-block arm may omit its comma when the following pattern has an unambiguous first
token. Top-level borrow and slice patterns still require a comma because \<open>&\<close> and \<open>[\<close>
can continue the preceding body as binary-and or indexing. The AST audit below checks the complete
restricted-start pattern family, both explicit-comma cases, rejection without the comma, and parser
recovery.
\<close>

urust_expr  grammar_direct_with_block_arm
  \<open>
    match true {
      true \<Rightarrow> if true { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }
      false \<Rightarrow> \<llangle>3 :: nat\<rrangle>
    }
  \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> (if true { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> })
      false \<Rightarrow> \<llangle>3 :: nat\<rrangle>
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> return \<llangle>1 :: nat\<rrangle>;,
      false \<Rightarrow> return \<llangle>2 :: nat\<rrangle>;
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> return;,
      false \<Rightarrow> return;
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> if true { () } else { () }
      false \<Rightarrow> return;
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> The restricted arm family after a comma-free direct block rejects the same semicolon. \<close>

urust_expr grammar_valued_return_arm_commas
  \<open>
    match true {
      true \<Rightarrow> return \<llangle>1 :: nat\<rrangle>,
      false \<Rightarrow> return \<llangle>2 :: nat\<rrangle>,
    }
  \<close>

urust_expr grammar_operandless_return_arm_commas
  \<open>
    match true {
      true \<Rightarrow> return,
      false \<Rightarrow> return,
    }
  \<close>

urust_expr grammar_valued_return_arm_blocks
  \<open>
    match true {
      true \<Rightarrow> { return \<llangle>1 :: nat\<rrangle>; },
      false \<Rightarrow> { return \<llangle>2 :: nat\<rrangle>; }
    }
  \<close>

urust_expr grammar_operandless_return_arm_blocks
  \<open>
    match true {
      true \<Rightarrow> { return; },
      false \<Rightarrow> { return; }
    }
  \<close>

urust_expr grammar_return_arm_recovery
  \<open> match true { true \<Rightarrow> return (), false \<Rightarrow> return (), } \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> \<llangle>1 :: nat\<rrangle>;,
      false \<Rightarrow> \<llangle>2 :: nat\<rrangle>
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> Direct arm bodies require a comma or braces; arbitrary semicolon arms remain invalid. \<close>

section\<open>Closures and binding RHSs\<close>

urust_expr  grammar_direct_closure_initializer
  \<open>
    let f = |x| x + \<llangle>1 :: 32 word\<rrangle>;
    ()
  \<close>

urust_expr grammar_closure_full_body
  \<open>
    |x| if true { x } else { x + \<llangle>1 :: 32 word\<rrangle> }
  \<close>

urust_expr  grammar_closure_if_let_body
  \<open>
    || if let Some(x) = Some(\<llangle>1 :: nat\<rrangle>) { x } else { 0 }
  \<close>

urust_expr  grammar_closure_mixed_if_body
  \<open>
    || if true { 0 } else if let Some(x) = Some(\<llangle>1 :: nat\<rrangle>) { x } else { 0 }
  \<close>

urust_expr  grammar_closure_return_body
  \<open> || return \<llangle>1 :: nat\<rrangle> \<close>

urust_expr  grammar_nested_closure_body
  \<open> || || \<llangle>1 :: nat\<rrangle> \<close>

urust_expr  grammar_if_let_operand
  \<open>
    if let Some(value) = Some(\<llangle>1 :: 32 word\<rrangle>) {
      value
    } else {
      \<llangle>0 :: 32 word\<rrangle>
    } + \<llangle>1 :: 32 word\<rrangle>
  \<close>

urust_expr  grammar_closure_match_scrutinee
  \<open> match || true { _ \<Rightarrow> () } \<close>

urust_expr  grammar_closure_match_arms
  \<open>
    match true {
      true \<Rightarrow> || true,
      false \<Rightarrow> || false
    }
  \<close>

section\<open>Integer literal bases and separators\<close>

urust_expr grammar_binary \<open> 0b1010 \<close>
urust_expr grammar_binary_suffix
  \<open> 0b1111u8 \<close>
urust_expr grammar_binary_trailing_separator
  \<open> 0b1010_ \<close>
urust_expr grammar_octal
  \<open> 0o755 \<close>
urust_expr grammar_octal_suffix
  \<open> 0o17_u16 \<close>
urust_expr grammar_octal_trailing_separator
  \<open> 0o17_ \<close>
urust_expr grammar_decimal_separators
  \<open> 1_000_000u32 \<close>
urust_expr grammar_hex_separators
  \<open> 0xff_00u32 \<close>
urust_expr grammar_decimal_trailing_separator
  \<open> 1_ \<close>
urust_expr grammar_hex_trailing_separator
  \<open> 0xff_ \<close>


section\<open>Struct expressions\<close>

datatype grammar_empty_struct = GrammarEmptyStruct

definition grammar_empty_struct_call ::
    \<open>(unit, grammar_empty_struct, unit, unit, unit) function_body\<close>
  where
    \<open>grammar_empty_struct_call \<equiv> FunctionBody (literal GrammarEmptyStruct)\<close>

micro_rust_notation (call) grammar_empty_struct_call ("GrammarEmptyStruct")

urust_expr grammar_empty_struct_expression
  \<open> GrammarEmptyStruct {} \<close>

definition grammar_empty_bool_value :: bool
  where \<open>grammar_empty_bool_value \<equiv> True\<close>

definition grammar_empty_bool_call ::
    \<open>(unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_bool_call \<equiv>
        FunctionBody (literal grammar_empty_bool_value)
    \<close>

definition grammar_empty_option_value :: \<open>unit option\<close>
  where \<open>grammar_empty_option_value \<equiv> Some ()\<close>

definition grammar_empty_option_call ::
    \<open>(unit, unit option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_option_call \<equiv>
        FunctionBody (literal grammar_empty_option_value)
    \<close>

definition grammar_empty_list_value :: \<open>unit list\<close>
  where \<open>grammar_empty_list_value \<equiv> [()]\<close>

definition grammar_empty_list_call ::
    \<open>(unit, unit list, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_list_call \<equiv>
        FunctionBody (literal grammar_empty_list_value)
    \<close>

definition grammar_empty_nat_value :: nat
  where \<open>grammar_empty_nat_value \<equiv> 1\<close>

definition grammar_empty_nat_call ::
    \<open>(unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_nat_call \<equiv>
        FunctionBody (literal grammar_empty_nat_value)
    \<close>

micro_rust_notation (call)
  grammar_empty_bool_call ("grammar_empty_bool_value")
micro_rust_notation (call)
  grammar_empty_option_call ("grammar_empty_option_value")
micro_rust_notation (call)
  grammar_empty_list_call ("grammar_empty_list_value")
micro_rust_notation (call)
  grammar_empty_nat_call ("grammar_empty_nat_value")

definition grammar_propagate_bool_value :: \<open>bool option\<close>
  where \<open>grammar_propagate_bool_value \<equiv> Some True\<close>

definition grammar_propagate_bool_call ::
    \<open>(unit, bool option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_bool_call \<equiv>
        FunctionBody (literal grammar_propagate_bool_value)
    \<close>

definition grammar_propagate_option_value :: \<open>unit option option\<close>
  where \<open>grammar_propagate_option_value \<equiv> Some (Some ())\<close>

definition grammar_propagate_option_call ::
    \<open>(unit, unit option option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_option_call \<equiv>
        FunctionBody (literal grammar_propagate_option_value)
    \<close>

definition grammar_propagate_list_value :: \<open>unit list option\<close>
  where \<open>grammar_propagate_list_value \<equiv> Some [()]\<close>

definition grammar_propagate_list_call ::
    \<open>(unit, unit list option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_list_call \<equiv>
        FunctionBody (literal grammar_propagate_list_value)
    \<close>

definition grammar_propagate_nat_value :: \<open>nat option\<close>
  where \<open>grammar_propagate_nat_value \<equiv> Some 1\<close>

definition grammar_propagate_nat_call ::
    \<open>(unit, nat option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_nat_call \<equiv>
        FunctionBody (literal grammar_propagate_nat_value)
    \<close>

micro_rust_notation (call)
  grammar_propagate_bool_call ("grammar_propagate_bool_value")
micro_rust_notation (call)
  grammar_propagate_option_call ("grammar_propagate_option_value")
micro_rust_notation (call)
  grammar_propagate_list_call ("grammar_propagate_list_value")
micro_rust_notation (call)
  grammar_propagate_nat_call ("grammar_propagate_nat_value")

subsection\<open>Empty struct expressions in control heads\<close>

text\<open>
Each surface name below is both a genuine bare HOL value and a registered nullary call. In a
no-struct control head, its first empty braces must not be silently consumed as the control body.
Explicit grouping restores unrestricted expression parsing.
\<close>

urust_expr_rejects
  \<open> if grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    if let Some(_) = grammar_empty_option_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open> if let _ = GrammarEmptyStruct {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open> for _ in grammar_empty_list_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      grammar_empty_option_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    match grammar_empty_bool_value {} {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match_case grammar_empty_option_value {} {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match_switch grammar_empty_nat_value {} {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> if !grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open> if true && grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    if false || true && !grammar_empty_bool_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    if true == grammar_empty_bool_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

text\<open>
Postfix propagation closes its operand before the control body begins. It therefore disambiguates
the following empty braces even when the operand path also names a registered nullary call.
True prefix operators surrounding the propagated expression retain that postfix boundary.
\<close>

urust_expr  grammar_propagate_empty_body_if
  \<open> if grammar_propagate_bool_value? {} else {} \<close>

urust_expr  grammar_propagate_empty_body_if_let
  \<open>
    if let Some(_) = grammar_propagate_option_value? {} else {}
  \<close>

urust_expr  grammar_propagate_empty_body_for
  \<open> for _ in grammar_propagate_list_value? {} \<close>

urust_expr  grammar_propagate_empty_body_while_let
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      grammar_propagate_option_value? {}
  \<close>

urust_expr  grammar_propagate_empty_body_match
  \<open>
    match grammar_propagate_bool_value? {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_propagate_empty_body_match_case
  \<open>
    match_case grammar_propagate_option_value? {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_propagate_empty_body_match_switch
  \<open>
    match_switch grammar_propagate_nat_value? {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_propagate_nested_prefix_empty_body
  \<open> if !grammar_propagate_bool_value? {} else {} \<close>

urust_expr  grammar_propagate_nested_binary_empty_body
  \<open>
    if false || grammar_propagate_bool_value? {} else {}
  \<close>

urust_expr  grammar_propagate_nested_comparison_empty_body
  \<open>
    if true == grammar_propagate_bool_value? {} else {}
  \<close>

urust_expr  grammar_grouped_empty_struct_if
  \<open>
    if (grammar_empty_bool_value {}) {} else {}
  \<close>

urust_expr  grammar_grouped_empty_struct_if_let
  \<open>
    if let Some(_) = (grammar_empty_option_value {}) {} else {}
  \<close>

urust_expr  grammar_grouped_empty_struct_for
  \<open> for _ in (grammar_empty_list_value {}) {} \<close>

urust_expr  grammar_grouped_empty_struct_while_let
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      (grammar_empty_option_value {}) {}
  \<close>

urust_expr  grammar_grouped_empty_struct_match
  \<open>
    match (grammar_empty_bool_value {}) {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_grouped_empty_struct_match_case
  \<open>
    match_case (grammar_empty_option_value {}) {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_grouped_empty_struct_match_switch
  \<open>
    match_switch (grammar_empty_nat_value {}) {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>

definition grammar_bare_flag :: bool
  where \<open>grammar_bare_flag \<equiv> True\<close>

urust_expr  grammar_bare_path_empty_body
  \<open> if grammar_bare_flag {} \<close>

urust_expr  grammar_bare_path_empty_body_sequence
  \<open> if grammar_bare_flag {} {} \<close>

urust_expr  grammar_nested_bare_path_empty_body_sequence
  \<open> if true && grammar_bare_flag {} {} \<close>

context fixes flag :: bool
begin

urust_expr  grammar_fixed_path_empty_body_sequence
  \<open> if flag {} {} \<close>

end

urust_expr  grammar_struct_trailing_comma
  \<open>
    D21Pair {
      second: 2_u64,
      first: 1_u64,
    }
  \<close>

section\<open>AST and grammar-shape audit\<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>
    fun parse source =
      (case URust_Parser.parse_source ctxt (Parser_Lex_Util.text_source source) of
         SOME expression => expression
       | NONE => error "expected a nonempty uRust expression")
    fun assert message true = ()
      | assert message false = error message
    fun following_pattern separator pattern =
      (case parse
          ("match scrutinee { _ => if flag { left } else { right }" ^
           separator ^ pattern ^ " => body }") of
         UE_Match
           (_, _,
            [UR_Arm (_, _, UE_If _, _),
             UR_Arm (following, _, _, _)],
            _) => following
       | _ =>
           error
             ("match-arm separator AST shape changed for pattern " ^
              quote pattern))
    fun assert_comma_free_follow (label, pattern) =
      (case Exn.result (following_pattern " ") pattern of
         Exn.Res _ => ()
       | Exn.Exn exn =>
           Exn.reraise
             (ERROR
               ("comma-free direct with-block arm rejected " ^ label ^
                " pattern " ^ quote pattern ^ ":\n" ^
                Runtime.exn_message exn)))
    fun assert_comma_required (label, pattern) =
      (case Exn.result (following_pattern " ") pattern of
         Exn.Exn exn =>
           assert
             ("comma-free " ^ label ^
              " pattern changed its syntax diagnostic")
             (String.isSubstring "syntax error"
               (Runtime.exn_message exn))
       | Exn.Res _ =>
           error
             ("comma-free direct with-block arm accepted top-level " ^
              label ^ " pattern " ^ quote pattern))
    val _ =
      List.app assert_comma_free_follow
        [("wildcard", "_"),
         ("path", "Module::Next"),
         ("unsigned primitive path", "u8::MAX"),
         ("signed primitive path", "i32::MIN"),
         ("numeral", "1"),
         ("Boolean", "true"),
         ("string", "\"key\""),
         ("value antiquotation", "\<llangle>value\<rrangle>"),
         ("constructor", "Some(item)"),
         ("group", "(Next)"),
         ("tuple", "(left, right)"),
         ("struct", "Shape { field: item }"),
         ("alias with borrowed inner pattern", "binding @ &item"),
         ("range", "1..=2"),
         ("or-pattern with borrowed tail", "Next | &item"),
         ("grouped slice", "([item])")]
    val _ =
      (case following_pattern " " "u8::MAX" of
         P_Path
           (UR_Path
             (Primitive_Head (Primitive_Unsigned UT_U8), _, _)) => ()
       | _ =>
           error
             "comma-free unsigned primitive path pattern changed shape")
    val _ =
      (case following_pattern " " "i32::MIN" of
         P_Path
           (UR_Path
             (Primitive_Head (Primitive_Signed ST_I32), _, _)) => ()
       | _ =>
           error
             "comma-free signed primitive path pattern changed shape")
    val _ =
      (case following_pattern ", " "&item" of
         P_Borrow (BM_Imm, P_Ident ("item", _), _) => ()
       | _ => error "explicit-comma borrowed arm pattern shape changed")
    val _ =
      (case following_pattern ", " "[item]" of
         P_Slice ([SI_Pat (P_Ident ("item", _))], _) => ()
       | _ => error "explicit-comma slice arm pattern shape changed")
    val _ = assert_comma_required ("borrow", "&item")
    val _ = assert_comma_required ("slice", "[item]")
    val _ = following_pattern " " "Recovery"
    val _ =
      (case parse
          "match value { First => if flag { left } else { right } Second if guard => body }" of
         UE_Match
           (_, _,
            [UR_Arm (_, _, UE_If _, _),
             UR_Arm
               (P_Ident ("Second", _),
                SOME (UE_Path _, _), UE_Path _, _)],
            _) => ()
       | _ => error "guarded arm after comma-free block changed shape")
    val _ =
      (case parse
          ("match value { First => if flag { left } else { right } " ^
           "Second => if guard { middle } else { other } Third => tail }") of
         UE_Match
           (_, _,
            [UR_Arm (_, _, UE_If _, _),
             UR_Arm (_, _, UE_If _, _),
             UR_Arm (P_Ident ("Third", _), _, UE_Path _, _)],
            _) => ()
       | _ => error "chained comma-free block arms changed shape")
    val _ =
      (case parse
          "match value { First => if flag { left } else { right } Second => return result, }" of
         UE_Match
           (_, _,
            [UR_Arm (_, _, UE_If _, _),
             UR_Arm
               (P_Ident ("Second", _), _, UE_Return _, _)],
            _) => ()
       | _ => error "comma-delimited return arm after comma-free block changed shape")
    val _ =
      (case parse
          "match value { First => if flag { left } else { right } Second => middle, &third => tail }" of
         UE_Match
           (_, _,
            [UR_Arm (_, _, UE_If _, _),
             UR_Arm (P_Ident ("Second", _), _, UE_Path _, _),
             UR_Arm (P_Borrow _, _, UE_Path _, _)],
            _) => ()
       | _ => error "comma did not restore unrestricted following arms")
    val _ =
      (case parse
          "match value { First => if flag { left } else { right } Second => tail, }" of
         UE_Match
           (_, _,
            [UR_Arm (_, _, UE_If _, _),
             UR_Arm (P_Ident ("Second", _), _, UE_Path _, _)],
            _) => ()
       | _ => error "trailing comma after restricted following arm changed")
  in
    val _ =
      (case parse "*x as usize" of
         UE_Cast
           (UE_Unary (U_Deref, UE_Path _, _),
            SCT_Primitive (CT_Unsigned UT_Usize, _), _) => ()
       | _ => error "unary-before-cast AST shape changed")
    val _ =
      (case parse "*base[index]" of
         UE_Unary
           (U_Deref, UE_Index (UE_Path _, UE_Path _, _), _) => ()
       | _ => error "postfix-before-dereference index AST shape changed")
    val _ =
      (case parse "*(base[index])" of
         UE_Unary
           (U_Deref, UE_Group (UE_Index (UE_Path _, UE_Path _, _), _), _) => ()
       | _ => error "explicit Rust-grouped dereference/index AST shape changed")
    val _ =
      (case parse "(*base)[index]" of
         UE_Index
           (UE_Group (UE_Unary (U_Deref, UE_Path _, _), _),
            UE_Path _, _) => ()
       | _ => error "explicit grouped-dereference/index AST shape changed")
    val _ =
      (case parse "*base.field" of
         UE_Unary (U_Deref, UE_Field (UE_Path _, "field", _), _) => ()
       | _ => error "ordinary path-field dereference AST shape changed")
    val _ =
      (case parse "*(base).field" of
         UE_Unary
           (U_Deref,
            UE_Field (UE_Group (UE_Path _, _), "field", _), _) => ()
       | _ => error "grouped field operand dereference AST shape changed")
    val _ =
      (case parse "*make().field" of
         UE_Unary
           (U_Deref, UE_Field (UE_Call _, "field", _), _) => ()
       | _ => error "call field operand dereference AST shape changed")
    val _ =
      (case parse "*base[index].field.0.method()?" of
         UE_Unary
           (U_Deref,
            UE_Unary
              (U_Propagate,
               UE_Call
                 (UC_Method
                   (UE_TupleProjection
                     (UE_Field
                       (UE_Index (UE_Path _, UE_Path _, _),
                        "field", _),
                      0, _),
                    Path_Segment ("method", _, _)),
                  [], _),
               _),
            _) => ()
       | _ => error "long postfix operand dereference AST shape changed")
    val _ =
      (case parse "*base.field as u64" of
         UE_Cast
           (UE_Unary (U_Deref, UE_Field (UE_Path _, "field", _), _),
            SCT_Primitive (CT_Unsigned UT_U64, _), _) => ()
       | _ => error "dereference operand crossed the cast boundary")
    val _ =
      (case parse "!*p" of
         UE_Unary (U_Not, UE_Unary (U_Deref, UE_Path _, _), _) => ()
       | _ => error "mixed not/dereference prefix shape changed")
    val _ =
      (case parse "*& mut r" of
         UE_Unary
           (U_Deref, UE_Unary (U_Borrow BM_Mut, UE_Path _, _), _) => ()
       | _ => error "mixed dereference/mutable-borrow prefix shape changed")
    val _ =
      (case parse "&!x" of
         UE_Unary (U_Borrow BM_Imm, UE_Unary (U_Not, UE_Path _, _), _) => ()
       | _ => error "mixed borrow/not prefix shape changed")
    val _ =
      (case parse "**p" of
         UE_Unary (U_Deref, UE_Unary (U_Deref, UE_Path _, _), _) => ()
       | _ => error "repeated dereference prefix shape changed")
    val _ =
      (case parse "if true { 1 } else { 2 } + 3" of
         UE_Bin (Add, UE_If _, UE_Literal _, _) => ()
       | _ => error "direct with-block operand AST shape changed")
    val _ =
      (case parse "if true { () } else { () } ()" of
         UE_Seq (UE_If _, UE_Unit _, _) => ()
       | _ => error "semicolon-free direct with-block statement shape changed")
    val _ =
      (case parse "0b10_01u8" of
         UE_Literal
           (LP_Integer
             (Integer_Literal ("0b10_01u8", _, _))) => ()
       | _ => error "integer literal raw spelling was not retained")
    val _ =
      (case parse "GrammarEmptyStruct {}" of
         UE_Struct (_, [], _) => ()
       | _ => error "empty struct expression AST shape changed")
    val _ =
      (case parse "AdvStruct { adv_right: 2, adv_left: 1, }" of
         UE_Struct
           (_, [SE_Field ("adv_right", _, _), SE_Field ("adv_left", _, _)], _) => ()
       | _ => error "struct field source order or trailing-comma shape changed")
    val _ =
      (case parse "r = match flag { true => lhs, false => rhs }" of
         UE_Assign (Assign, _, UE_Match _, _) => ()
       | _ => error "direct match assignment RHS shape changed")
    val _ =
      (case parse "r += if flag { lhs } else { rhs }" of
         UE_Assign (AssignAdd, _, UE_If _, _) => ()
       | _ => error "direct conditional compound-assignment RHS shape changed")
    val _ =
      (case parse "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } == ()" of
         UE_Bin (Eq, UE_Loop _, UE_Unit _, _) => ()
       | _ => error "direct loop binary-operand shape changed")
    val _ =
      (case parse "for value in \<llangle>[1 :: nat]\<rrangle> { () } == ()" of
         UE_Bin (Eq, UE_For _, UE_Unit _, _) => ()
       | _ => error "direct for-loop binary-operand shape changed")
    val _ =
      (case parse
          "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) = \<llangle>Some (1 :: nat)\<rrangle> { () } == ()" of
         UE_Bin (Eq, UE_WhileLet _, UE_Unit _, _) => ()
       | _ => error "direct while-let binary-operand shape changed")
    val _ =
      (case parse "target = || 1" of
         UE_Assign (Assign, _, UE_Closure _, _) => ()
       | _ => error "closure assignment RHS shape changed")
    val _ =
      (case parse "|| target = 1" of
         UE_Closure (_, UE_Assign (Assign, _, _, _), _) => ()
       | _ => error "assignment closure-body shape changed")
    val _ =
      (case parse "|| #[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () }" of
         UE_Closure (_, UE_Loop _, _) => ()
       | _ => error "loop closure-body shape changed")
    val _ =
      (case parse "|| (); ()" of
         UE_Seq
           (UE_Closure (_, UE_Unit _, _), UE_Unit _, _) => ()
       | _ => error "closure statement sequencing shape changed")
    val _ =
      (case parse "|| \<llangle>1 :: nat\<rrangle>; ()" of
         UE_Seq
           (UE_Closure (_, UE_Literal _, _), UE_Unit _, _) => ()
       | _ => error "closure left-sequencing shape changed")
    val _ =
      (case parse
          "match true { true => return 1, false => { return 2; } }" of
         UE_Match
           (_, _,
            [UR_Arm (_, _, UE_Return _, _),
             UR_Arm (_, _, UE_Block (UE_Return _, _), _)],
            _) => ()
       | _ => error "comma and braced return-arm AST shapes changed")
    val literal_text = "0b10_01u8"
    val literal_start =
      Position.make0 23 400 0 "" "" "grammar-literal-markup-audit"
    val literal_stop =
      Position.symbol_explode literal_text literal_start
    val captured_reports =
      Synchronized.var "grammar_literal_reports" ([] : string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                (case URust_Parser.parse_source ctxt
                    (Parser_Lex_Util.positioned_content_source
                      literal_text literal_start) of
                   SOME _ => ()
                 | NONE => error "integer markup audit parsed empty input")) ())
          ())
    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val literal_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun property_matches name value properties =
      Properties.get properties name = Option.map Value.print_int value
    val _ =
      assert "integer candidate lost whole-token numeral markup"
        (exists
          (fn (name, properties) =>
            name = Markup.numeralN andalso
              property_matches Markup.offsetN
                (Position.offset_of literal_start) properties andalso
              property_matches Markup.end_offsetN
                (Position.offset_of literal_stop) properties)
          literal_markup)
    val _ =
      (case Exn.result
          (Parser_Test_Elaboration.expression ctxt)
          (Parser_Lex_Util.text_source "0b102u32") of
         Exn.Exn exn =>
           assert "malformed integer candidate changed diagnostic"
             (String.isSubstring
               "cannot read integer literal \"0b102u32\""
               (Runtime.exn_message exn))
       | Exn.Res _ => error "malformed integer candidate was accepted")
    val _ =
      (case parse "0x2a" of
         UE_Literal
           (LP_Integer (Integer_Literal ("0x2a", _, _))) => ()
       | _ => error "integer parser did not recover after malformed input")
    val _ = assert "ordinary/no-struct audit fixture did not run" true
  end
\<close>



section\<open> Full guard-body grammar audit \<close>

text\<open>
Match guards reuse the complete non-nullable body grammar. This audit checks the AST before
elaboration, including branches whose final type is intentionally not boolean.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>
    val arm_prefix = "match_case Some(()) { Some(_) if "
    val arm_suffix = " => (), None => (), }"

    fun audit_assert message condition =
      if condition then ()
      else error ("full guard-body grammar audit: " ^ message)

    fun source_text guard = arm_prefix ^ guard ^ arm_suffix

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "full guard-body grammar audit: empty parse")

    fun guard_of source =
      (case parse source of
         UE_Match
           (MF_Case, _,
            UR_Arm (_, SOME (guard, if_pos), UE_Unit _, _) ::
              UR_Arm (_, NONE, UE_Unit _, _) :: [],
            _) =>
           (guard, if_pos)
       | _ =>
           error
             "full guard-body grammar audit: wrapper AST changed")

    fun parse_guard guard =
      guard_of
        (Parser_Lex_Util.text_source (source_text guard))

    fun check_guard label guard expected =
      let val (expression, _) = parse_guard guard
      in
        audit_assert (label ^ " AST changed") (expected expression)
      end

    fun is_true (UE_Literal (LP_Bool (true, _))) = true
      | is_true _ = false

    fun is_unit (UE_Unit _) = true
      | is_unit _ = false

    fun is_path name (UE_Path path) = render_path path = name
      | is_path _ _ = false

    val _ = check_guard "terminal value" "true" is_true
    val _ =
      check_guard "semicolon value sequence" "(); true"
        (fn UE_Seq (left, right, _) =>
              is_unit left andalso is_true right
          | _ => false)
    val _ =
      check_guard "terminal statement" "();"
        (fn UE_Seq (left, right, _) =>
              is_unit left andalso is_unit right
          | _ => false)
    val _ =
      check_guard "block prefix" "{ () } true"
        (fn UE_Seq (UE_Block (body, _), right, _) =>
              is_unit body andalso is_true right
          | _ => false)
    val _ =
      check_guard "unsafe-block prefix" "unsafe { () } true"
        (fn UE_Seq (UE_Block (body, _), right, _) =>
              is_unit body andalso is_true right
          | _ => false)
    val _ =
      check_guard "conditional prefix"
        "if false { () } else { () } true"
        (fn UE_Seq (UE_If _, right, _) => is_true right
          | _ => false)
    val _ =
      check_guard "while prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) { () } true")
        (fn UE_Seq (UE_While _, right, _) => is_true right
          | _ => false)
    val _ =
      check_guard "loop prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } true")
        (fn UE_Seq (UE_Loop _, right, _) => is_true right
          | _ => false)
    val _ =
      check_guard "for prefix"
        "for item in values { () } true"
        (fn UE_Seq
              (UE_For (P_Ident ("item", _), _, _, _),
               right, _) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "while-let prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
         "Some(item) = Some(()) { () } true")
        (fn UE_Seq
              (UE_WhileLet
                (_, P_Constr (path, [P_Ident ("item", _)], _),
                 _, _, _),
               right, _) =>
              render_path path = "Some" andalso is_true right
          | _ => false)
    val _ =
      check_guard "bare-match prefix"
        "match true { true => (), false => () } true"
        (fn UE_Seq (UE_Match (MF_Auto, _, _, _), right, _) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "explicit case-match prefix"
        "match_case Some(()) { Some(value) => value, None => () } true"
        (fn UE_Seq (UE_Match (MF_Case, _, _, _), right, _) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "explicit switch-match prefix"
        "match_switch 0 { 0 => (), _ => () } true"
        (fn UE_Seq (UE_Match (MF_Switch, _, _, _), right, _) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "let binding"
        "let flag = true; flag"
        (fn UE_Let (P_Ident ("flag", _), value, body, _) =>
              is_true value andalso is_path "flag" body
          | _ => false)
    val _ =
      check_guard "mutable binding"
        "let mut flag = true; true"
        (fn UE_LetMut (P_Ident ("flag", _), value, body, _) =>
              is_true value andalso is_true body
          | _ => false)
    val _ =
      check_guard "const binding"
        "const FLAG = true; FLAG"
        (fn UE_Const (P_Ident ("FLAG", _), value, body, _) =>
              is_true value andalso is_path "FLAG" body
          | _ => false)
    val _ =
      check_guard "let-else binding"
        "let Some(flag) = Some(true) else { false }; flag"
        (fn UE_LetElse
              (P_Constr (path, [P_Ident ("flag", _)], _),
               _, UE_Block (fallback, _), body, _) =>
              render_path path = "Some" andalso is_path "flag" body andalso
                (case fallback of
                   UE_Literal (LP_Bool (false, _)) => true
                 | _ => false)
          | _ => false)
    val _ =
      check_guard "right-associated bindings"
        "let first = true; const SECOND = first; SECOND"
        (fn UE_Let
              (P_Ident ("first", _), _,
               UE_Const
                 (P_Ident ("SECOND", _), first, second, _),
               _) =>
              is_path "first" first andalso is_path "SECOND" second
          | _ => false)
    val _ =
      check_guard "if-let value"
        "if let Some(flag) = Some(true) { flag } else { false }"
        (fn UE_IfLet
              (P_Constr (path, [P_Ident ("flag", _)], _),
               _, UE_Block (body, _),
               SOME (UE_Block (UE_Literal (LP_Bool (false, _)), _)), _) =>
              render_path path = "Some" andalso is_path "flag" body
          | _ => false)
    val _ =
      check_guard "legacy return with operand" "return true;"
        (fn UE_Return (SOME value, _) => is_true value
          | _ => false)
    val _ =
      check_guard "legacy operandless return" "return;"
        (fn UE_Return (NONE, _) => true
          | _ => false)
    val _ =
      check_guard "tail return" "return true"
        (fn UE_Return (SOME value, _) => is_true value
          | _ => false)

    val positioned_guard =
      "if let Some(flag) = Some(true) { flag } else { false }"
    val positioned_text = source_text positioned_guard
    val positioned_start =
      Position.make0 17 80 200 "" "" "full-guard-body-ast-audit"
    val (positioned_ast, arm_if_pos) =
      guard_of
        (Parser_Lex_Util.positioned_content_source
          positioned_text positioned_start)
    val arm_if_raw = size arm_prefix - size "if "
    val guard_stop_raw = size arm_prefix + size positioned_guard
    fun position_at raw =
      Position.symbol_explode
        (String.substring (positioned_text, 0, raw))
        positioned_start
    val _ =
      audit_assert "guard keyword position moved"
        (Position.offset_of arm_if_pos =
          Position.offset_of (position_at arm_if_raw))
    val _ =
      (case positioned_ast of
         UE_IfLet (_, _, _, _, layout) =>
           (audit_assert "if-let guard span start moved"
              (Position.offset_of (source_span layout) =
                Position.offset_of (position_at (size arm_prefix)));
            audit_assert "if-let guard span stopped before the arrow"
              (Position.end_offset_of (source_span layout) =
                Position.offset_of (position_at guard_stop_raw)))
       | _ =>
           error
             "full guard-body grammar audit: positioned if-let AST changed")

    val positioned_let_else =
      "let Some(flag) = Some(true) else { false }; flag"
    val positioned_let_else_text = source_text positioned_let_else
    val (positioned_let_else_ast, _) =
      guard_of
        (Parser_Lex_Util.positioned_content_source
          positioned_let_else_text positioned_start)
    val positioned_let_else_stop =
      Position.symbol_explode
        (String.substring
          (positioned_let_else_text, 0,
           size arm_prefix + size positioned_let_else))
        positioned_start
    val _ =
      (case positioned_let_else_ast of
         UE_LetElse (_, _, _, _, layout) =>
           (audit_assert "let-else guard span start moved"
              (Position.offset_of (source_span layout) =
                Position.offset_of (position_at (size arm_prefix)));
            audit_assert "let-else guard span stopped before the arrow"
              (Position.end_offset_of (source_span layout) =
                Position.offset_of positioned_let_else_stop))
       | _ =>
           error
             "full guard-body grammar audit: positioned let-else AST changed")

    val non_boolean_source = source_text "();"
    val (non_boolean_ast, _) =
      guard_of (Parser_Lex_Util.text_source non_boolean_source)
    val _ =
      audit_assert "non-boolean terminal statement did not parse"
        (case non_boolean_ast of
           UE_Seq (left, right, _) =>
             is_unit left andalso is_unit right
         | _ => false)
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source non_boolean_source)) () of
         Exn.Res _ =>
           error
             "full guard-body grammar audit: non-boolean guard type-checked"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "non-boolean guard failed outside boolean checking"
               (String.isSubstring "bool" (Runtime.exn_message exn)))
  in
    val _ = writeln "Full guard-body grammar audit passed"
  end
\<close>

section\<open> Range, array, and indexing structure \<close>

text\<open>
The public AST keeps each source form explicit, while the term layer emits only
the shallow semantic vocabulary before the command's single final
\<open>Syntax.check_term\<close>.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("range/array/index regression audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE =>
           error "range/array/index regression audit: empty parse")

    fun integer text (UE_Literal (LP_Integer integer)) =
          integer_literal_lexeme integer = text
      | integer _ _ = false

    fun identifier text (UE_Path path) = render_path path = text
      | identifier _ _ = false

    val _ =
      (case parse "1..2" of
         UE_Range (RK_Exclusive, lower, upper, _) =>
           audit_assert "exclusive range AST changed"
             (integer "1" lower andalso integer "2" upper)
       | _ => error "range/array/index regression audit: exclusive range AST changed")

    val _ =
      (case parse "1..=2" of
         UE_Range (RK_Inclusive, lower, upper, _) =>
           audit_assert "inclusive range AST changed"
             (integer "1" lower andalso integer "2" upper)
       | _ => error "range/array/index regression audit: inclusive range AST changed")

    val _ =
      (case parse "[]" of
         UE_Array ([], _) => ()
       | _ => error "range/array/index regression audit: empty array AST changed")

    val _ =
      (case parse "[1, 2]" of
         UE_Array ([first, second], _) =>
           audit_assert "array element order changed"
             (integer "1" first andalso integer "2" second)
       | _ => error "range/array/index regression audit: array AST changed")

    val _ =
      (case parse "xs[0].field[1]" of
         UE_Index
           (UE_Field
             (UE_Index (base, first_index, _), "field", _),
            second_index, _) =>
           audit_assert "postfix index/field nesting changed"
             (identifier "xs" base andalso
              integer "0" first_index andalso
              integer "1" second_index)
       | _ =>
           error
             "range/array/index regression audit: postfix nesting AST changed")

    val _ =
      (case parse "xs[0] += 1" of
         UE_Assign
           (AssignAdd,
            UP_Index (UP_Path path, index, _),
            rhs, _) =>
           audit_assert "indexed place conversion changed"
             (render_path path = "xs" andalso
              integer "0" index andalso integer "1" rhs)
       | _ =>
           error
             "range/array/index regression audit: indexed place AST changed")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    fun has_head name arity term =
      (case Term.strip_comb term of
         (Const (actual, _), arguments) =>
           actual = name andalso length arguments = arity
       | _ => false)

    fun function_call2 target term =
      (case Term.strip_comb term of
         (Const (call, _), Const (actual, _) :: arguments) =>
           call = \<^const_name>\<open>funcall2\<close> andalso
           actual = target andalso length arguments = 2
       | _ => false)

    fun dest_read_adjustment
        (Const (\<^const_name>\<open>urust_internal_read_adjustment\<close>, _) $
          _ $ place) =
          SOME place
      | dest_read_adjustment _ = NONE

    val _ =
      audit_assert "exclusive range term shape changed"
        (function_call2 \<^const_name>\<open>range_new\<close>
          (unchecked "1..2"))

    val _ =
      audit_assert "inclusive range term shape changed"
        (function_call2 \<^const_name>\<open>range_eq_new\<close>
          (unchecked "1..=2"))

    fun array_shape [] term =
          (case Term.strip_comb term of
             (Const (literal_name, _), [Const (nil_name, _)]) =>
               literal_name = \<^const_name>\<open>literal\<close> andalso
               nil_name = \<^const_name>\<open>List.Nil\<close>
           | _ => false)
      | array_shape (_ :: rest) term =
          (case Term.strip_comb term of
             (Const (bindlift_name, _),
              [Const (cons_name, _), _, tail]) =>
               bindlift_name = \<^const_name>\<open>bindlift2\<close> andalso
               cons_name = \<^const_name>\<open>List.Cons\<close> andalso
               array_shape rest tail
           | _ => false)

    val _ =
      audit_assert "empty array term shape changed"
        (array_shape [] (unchecked "[]"))

    val _ =
      audit_assert "nonempty array term shape changed"
        (array_shape [(), (), ()] (unchecked "[1, 2, 3]"))

    val unchecked_index = unchecked "[1][0]"
    val _ =
      audit_assert "index term lost its internal value adjustment"
        (is_some (dest_read_adjustment unchecked_index))
    val _ =
      audit_assert "index term lost its private projection recipe"
        (has_head
          \<^const_name>\<open>urust_internal_index_projection\<close> 3
          (the (dest_read_adjustment unchecked_index)))

    val _ =
      audit_assert "direct array borrow stopped erasing"
        (Term.aconv (unchecked "&[1, 2]", unchecked "[1, 2]"))

    val indexed_assignment = unchecked "xs[0] = 1"
    val _ =
      audit_assert "indexed assignment lost store-update lowering"
        (has_head \<^const_name>\<open>bind2\<close> 3 indexed_assignment)
    val index_count =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = \<^const_name>\<open>index_const\<close>
              then Integer.add 1
              else I
          | _ => I)
        indexed_assignment 0
    val _ =
      audit_assert "indexed assignment did not lower its place exactly once"
        (index_count = 1)
  in
    val _ = writeln "Range, array, and indexing regressions passed"
  end
\<close>

section\<open> Numeric tuple projection structure, ranges, and markup \<close>

consts
  tuple_projection_audit_marker ::
    \<open>
      (unit,
       nat \<times> nat \<times> nat \<times>
         (bool \<times> bool \<times> Tuple.tnil) \<times> Tuple.tnil,
       unit, unit, unit, unit) expression
    \<close>

text\<open>
These checks keep numeric projections distinct from fields and bracket indexing.
They pin the canonical index payload, left-associated AST, numeric-token ranges,
lexer markup, direct expanded \<open>tuple_index_N\<close> shape, recovery, value-only
assignment policy, and exactly-once receiver lowering.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("tuple-projection regression audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "tuple-projection regression audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)
      |> Term_Position.strip_positions

    fun path_named name (UE_Path path) = render_path path = name
      | path_named _ _ = false

    fun projection index receiver (UE_TupleProjection (actual, stored, _)) =
          stored = index andalso receiver actual
      | projection _ _ _ = false

    val _ =
      List.app
        (fn index =>
          audit_assert
            ("AST index " ^ string_of_int index ^ " changed")
            (projection index (path_named "source")
              (parse ("source." ^ string_of_int index))))
        [0, 1, 10, 15]

    val _ =
      (case parse "source.2.0" of
         UE_TupleProjection
           (UE_TupleProjection (base, 2, _), 0, _) =>
           audit_assert "projection chain base changed"
             (path_named "source" base)
       | _ => error "tuple-projection regression audit: chain AST changed")

    val _ =
      (case parse "source.field[0].1" of
         UE_TupleProjection
           (UE_Index
             (UE_Field (base, "field", _),
              UE_Literal
                (LP_Integer (Integer_Literal ("0", _, _))), _),
            1, _) =>
           audit_assert "field/index/projection source order changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: mixed postfix AST changed")

    val _ =
      (case parse "!source.0" of
         UE_Unary
           (U_Not, UE_TupleProjection (base, 0, _), _) =>
           audit_assert "projection/prefix precedence changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: prefix AST changed")

    val _ =
      (case parse "source.0 + other" of
         UE_Bin
           (Add, UE_TupleProjection (base, 0, _), other, _) =>
           audit_assert "projection/binary precedence changed"
             (path_named "source" base andalso
              path_named "other" other)
       | _ =>
           error
             "tuple-projection regression audit: binary AST changed")

    val _ =
      (case parse "if source.0 { () } else { () }" of
         UE_If
           (UE_TupleProjection (base, 0, _),
            UE_Block (UE_Unit _, _),
            SOME (UE_Block (UE_Unit _, _)), _) =>
           audit_assert "restricted control-head projection changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: control-head AST changed")

    fun find_from text needle offset =
      if offset + size needle > size text
      then
        error
          ("tuple-projection regression audit: missing " ^ quote needle)
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

    fun same_range actual expected =
      Position.offset_of actual = Position.offset_of expected andalso
      Position.end_offset_of actual = Position.end_offset_of expected

    val ranged_text =
      "\<llangle>tuple_projection_audit_marker\<rrangle>.10.15"
    val ranged_start =
      Position.make0 13 70 700 "" ""
        "tuple-projection-range-audit"
    val ranged_stop =
      Position.symbol_explode ranged_text ranged_start
    val ranged_span =
      Position.range_position (ranged_start, ranged_stop)
    val (ten_offset, ten_position) =
      token_position ranged_text ranged_start "10" 0
    val (_, fifteen_position) =
      token_position ranged_text ranged_start "15"
        (ten_offset + size "10")
    val ranged_ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          ranged_text ranged_start)
    val _ =
      (case ranged_ast of
         UE_TupleProjection
           (UE_TupleProjection
             (UE_Literal (LP_ValAntiq _), 10, inner_layout),
            15, outer_layout) =>
           (audit_assert "inner two-digit token range changed"
              (same_range
                (the_source_token_position
                  inner_layout Name_Token)
                ten_position);
            audit_assert "outer two-digit token range changed"
              (same_range
                (the_source_token_position
                  outer_layout Name_Token)
                fifteen_position);
            audit_assert "expression_position lost the projection span"
              (same_range
                (expression_position ranged_ast) ranged_span))
       | _ =>
           error
             "tuple-projection regression audit: ranged AST changed")

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun decoded_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))

    fun expect_positioned_failure label text start expected position =
      (case Exn.result
          (fn () =>
            parse_source
              (Parser_Lex_Util.positioned_content_source text start)) () of
         Exn.Res _ =>
           error
             ("tuple-projection regression audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
               val markup = fold collect_markup body []
             in
               audit_assert (label ^ " diagnostic changed")
                 (String.isSubstring expected message);
               audit_assert (label ^ " diagnostic position changed")
                 (exists
                   (fn (name, properties) =>
                     name = Markup.positionN andalso
                       has_position properties position)
                   markup)
             end)

    val assignment_text = "source.0 = rhs"
    val assignment_start =
      Position.make0 19 90 900 "" ""
        "tuple-projection-assignment-audit"
    val (_, assignment_index_position) =
      token_position assignment_text assignment_start "0" 0
    val _ =
      expect_positioned_failure
        "value-only assignment"
        assignment_text assignment_start
        "invalid assignment target"
        assignment_index_position

    val invalid_start =
      Position.make0 23 110 1100 "" ""
        "tuple-projection-invalid-index-audit"
    fun expect_invalid_projection (text, token) =
      let
        val (_, token_position) =
          token_position text invalid_start token 0
      in
        expect_positioned_failure
          ("invalid index " ^ quote token)
          text invalid_start
          ("invalid tuple projection index " ^ quote token ^
            " (expected an unsuffixed decimal integer from 0 through 15)")
          token_position
      end
    val _ =
      List.app expect_invalid_projection
        [("source.16", "16"),
         ("source.00", "00"),
         ("source.01", "01"),
         ("source.0x1", "0x1"),
         ("source.1u8", "1u8"),
         ("source.1_u8", "1_u8")]

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun projection_parts expected_index term =
      (case Term.strip_comb term of
         (Const (bindlift, _), [selector, receiver]) =>
           (audit_assert
              ("projection " ^ string_of_int expected_index ^
                " did not use bindlift1")
              (bindlift = \<^const_name>\<open>bindlift1\<close>);
            audit_assert
              ("projection " ^ string_of_int expected_index ^
                " selector lost fst")
              (count_constant \<^const_name>\<open>fst\<close> selector = 1);
            audit_assert
              ("projection " ^ string_of_int expected_index ^
                " selector has the wrong snd depth")
              (count_constant \<^const_name>\<open>snd\<close> selector =
                expected_index);
            receiver)
       | _ =>
           error
             ("tuple-projection regression audit: projection " ^
               string_of_int expected_index ^ " term shape changed"))

    fun marker_projection index =
      unchecked
        ("\<epsilon>\<open>tuple_projection_audit_marker\<close>." ^
          string_of_int index)

    val _ =
      List.app
        (fn index =>
          let
            val term = marker_projection index
            val receiver = projection_parts index term
          in
            audit_assert
              ("projection " ^ string_of_int index ^
                " receiver changed or was duplicated")
              (count_constant
                 \<^const_name>\<open>tuple_projection_audit_marker\<close>
                 receiver = 1);
            audit_assert
              ("projection " ^ string_of_int index ^
                " introduced field/index/literal lowering")
              (count_constant
                 \<^const_name>\<open>focus_lens_const\<close> term = 0 andalso
               count_constant \<^const_name>\<open>index_const\<close> term = 0 andalso
               count_constant \<^const_name>\<open>literal\<close> term = 0)
          end)
        [0, 1, 10, 15]

    val chain =
      unchecked
        "\<epsilon>\<open>tuple_projection_audit_marker\<close>.3.0"
    val inner = projection_parts 0 chain
    val receiver = projection_parts 3 inner
    val _ =
      audit_assert "chained receiver was not lowered exactly once"
        (count_constant
           \<^const_name>\<open>tuple_projection_audit_marker\<close>
           chain = 1)
    val _ =
      audit_assert "chained projections lost one selected operation"
        (count_constant \<^const_name>\<open>bindlift1\<close> chain = 2)
    val _ =
      audit_assert "chained projection receiver changed"
        (count_constant
           \<^const_name>\<open>tuple_projection_audit_marker\<close>
           receiver = 1)

    fun expect_failure text expected =
      (case Exn.result (fn () => parse text) () of
         Exn.Res _ =>
           error
             ("tuple-projection regression audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (decoded_message exn)))

    val _ =
      (expect_failure "source.16"
         "invalid tuple projection index \"16\"";
       audit_assert "parser did not recover after invalid index"
         (projection 15 (path_named "source") (parse "source.15"));
       expect_failure "source."
         "syntax error found at end of input";
       audit_assert "parser did not recover after trailing dot"
         (projection 15 (path_named "source") (parse "source.15")))

    val captured_reports =
      Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (parse_source
                    (Parser_Lex_Util.positioned_content_source
                      ranged_text ranged_start))) ())
          ())

    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun has_any_entity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            has_position properties position)
        markup
    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size ranged_text
          then rev positions
          else
            (case try (find_from ranged_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position ranged_text ranged_start needle raw
                 in
                   collect (raw + size needle)
                     (position :: positions)
                 end
             | NONE => rev positions)
      in collect 0 [] end

    val _ =
      List.app
        (fn position =>
          audit_assert "projection dot lost delimiter markup"
            (has_markup Markup.delimiterN position))
        (all_token_positions ".")
    val _ =
      List.app
        (fn position =>
          (audit_assert "projection index lost numeral markup"
             (has_markup Markup.numeralN position);
           audit_assert "projection index lost typing markup"
             (has_markup Markup.typingN position);
           audit_assert "projection index received field/free markup"
             (not (has_markup Markup.freeN position));
           audit_assert "projection index received entity markup"
             (not (has_any_entity position))))
        [ten_position, fifteen_position]
  in
    val _ =
      writeln
        "Numeric tuple projection AST, range, markup, lowering, and recovery regressions passed"
  end
\<close>

section\<open> Legacy macro structure, spans, and markup \<close>

consts
  macro_audit_scrutinee :: \<open>nat option\<close>
  macro_audit_ref :: \<open>('a, 'b, 'v) Global_Store.ref\<close>
  macro_audit_marker :: bool
  macro_audit_ignored_marker :: bool
  macro_audit_vec_first :: nat
  macro_audit_vec_second :: nat

text\<open>
These checks pin complete-body macro payload boundaries, source spans, markup, recovery,
and the exact shallow term vocabulary. They also prove that retained bindings evaluate
once, discarded arguments never enter semantic lowering, \<open>vec!\<close> preserves
complete-body element order through the array builder, address macros retain the exact
legacy \<open>ref_address\<close> target, registered bang-names win only when adjacent, and
\<open>matches!\<close> uses the ordinary case compiler with one scrutinee evaluation and
false fallback.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("legacy macro regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "legacy macro regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse_text text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("legacy macro regression audit: missing " ^ quote needle)
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

    val full_body_text =
      "debug_assert!(let flag = true; " ^
      "if let Some(_) = Some(flag) { flag } else { false })"
    val full_body_start =
      Position.make0 7 30 0 "" "" "macro-full-body-span-audit"
    val full_body_stop =
      Position.symbol_explode full_body_text full_body_start
    val full_body =
      parse
        (Parser_Lex_Util.positioned_content_source
          full_body_text full_body_start)
    val (full_body_name_pos, full_body_bang_pos,
         full_body_invocation_pos, full_body_binder_pos,
         full_body_literal_pos, full_body_if_pos) =
      (case full_body of
         UE_Macro
           (path,
            MP_Arguments
              [UE_Let
                (P_Ident ("flag", binder_pos),
                 UE_Literal (LP_Bool (true, literal_pos)),
                 UE_IfLet
                   (P_Constr (pattern_path, [P_Wild _], _),
                    UE_Call
                      (UC_Path call_path, [UE_Path scrutinee_path], _),
                    UE_Block (UE_Path then_path, _),
                    SOME
                      (UE_Block
                        (UE_Literal (LP_Bool (false, _)), _)),
                    if_layout),
                 _)],
            macro_layout) =>
           (audit_assert "full-body macro path changed"
              (render_path path = "debug_assert");
            audit_assert "full-body condition escaped its binding continuation"
              (render_path pattern_path = "Some" andalso
               render_path call_path = "Some" andalso
               render_path scrutinee_path = "flag" andalso
               render_path then_path = "flag");
            (path_position path,
             the_source_token_position macro_layout Bang_Token,
             source_span macro_layout,
             binder_pos, literal_pos, source_span if_layout))
       | _ =>
           error "legacy macro regression audit: full-body macro AST changed")
    val _ =
      audit_assert "full-body invocation start moved"
        (Position.offset_of full_body_invocation_pos =
          Position.offset_of full_body_start)
    val _ =
      audit_assert "full-body invocation end moved"
        (Position.end_offset_of full_body_invocation_pos =
          Position.offset_of full_body_stop)
    val (_, full_body_binder_token) =
      token_position full_body_text full_body_start "flag" 0
    val (_, full_body_literal_token) =
      token_position full_body_text full_body_start "true" 0
    val (_, full_body_if_token) =
      token_position full_body_text full_body_start "if" 0
    val (full_body_name_raw, full_body_name_token) =
      token_position full_body_text full_body_start "debug_assert" 0
    val (_, full_body_bang_token) =
      token_position full_body_text full_body_start "!"
        (full_body_name_raw + size "debug_assert")
    val (first_brace_raw, _) =
      token_position full_body_text full_body_start "}" 0
    val (_, full_body_final_brace) =
      token_position full_body_text full_body_start "}"
        (first_brace_raw + 1)
    val _ =
      audit_assert "full-body binder position moved"
        (Position.offset_of full_body_binder_pos =
           Position.offset_of full_body_binder_token andalso
         Position.end_offset_of full_body_binder_pos =
           Position.end_offset_of full_body_binder_token)
    val _ =
      audit_assert "full-body literal position moved"
        (Position.offset_of full_body_literal_pos =
           Position.offset_of full_body_literal_token andalso
         Position.end_offset_of full_body_literal_pos =
           Position.end_offset_of full_body_literal_token)
    val _ =
      audit_assert "nested conditional span moved"
        (Position.offset_of full_body_if_pos =
           Position.offset_of full_body_if_token andalso
         Position.end_offset_of full_body_if_pos =
           Position.end_offset_of full_body_final_brace)
    val _ =
      audit_assert "full-body macro name span moved"
        (Position.offset_of full_body_name_pos =
           Position.offset_of full_body_name_token andalso
         Position.end_offset_of full_body_name_pos =
           Position.end_offset_of full_body_name_token)
    val full_body_bang_markup_pos = full_body_bang_pos
    val _ =
      audit_assert "full-body macro bang span moved"
        (Position.offset_of full_body_bang_markup_pos =
           Position.offset_of full_body_bang_token andalso
         Position.end_offset_of full_body_bang_markup_pos =
           Position.end_offset_of full_body_bang_token)
    val _ =
      audit_assert "full-body macro name and bang stopped being adjacent"
        (Position.end_offset_of full_body_name_pos =
           Position.offset_of full_body_bang_pos)

    val bracket_body_text =
      "assert_eq![let left = true; left, " ^
      "const right = false; if right { false } else { true }]"
    val bracket_body_start =
      Position.make0 9 60 0 "" "" "macro-bracket-body-span-audit"
    val bracket_body_stop =
      Position.symbol_explode bracket_body_text bracket_body_start
    val bracket_body =
      parse
        (Parser_Lex_Util.positioned_content_source
          bracket_body_text bracket_body_start)
    val (bracket_body_name_pos, bracket_body_invocation_pos) =
      (case bracket_body of
         UE_Macro
           (path,
            MP_Arguments
              [UE_Let
                (P_Ident ("left", _),
                 UE_Literal (LP_Bool (true, _)),
                 UE_Path left_path, _),
               UE_Const
                (P_Ident ("right", _),
                 UE_Literal (LP_Bool (false, _)),
                 UE_If
                   (UE_Path right_path, UE_Block _,
                    SOME (UE_Block _), _),
                 _)],
            macro_layout) =>
           (audit_assert "bracket full-body macro path changed"
              (render_path path = "assert_eq");
            audit_assert "bracket full-body argument order changed"
              (render_path left_path = "left" andalso
               render_path right_path = "right");
            (path_position path, source_span macro_layout))
       | _ =>
           error "legacy macro regression audit: bracket full-body AST changed")
    val _ =
      audit_assert "bracket full-body invocation start moved"
        (Position.offset_of bracket_body_invocation_pos =
          Position.offset_of bracket_body_start)
    val _ =
      audit_assert "bracket full-body invocation end moved"
        (Position.end_offset_of bracket_body_invocation_pos =
          Position.offset_of bracket_body_stop)

    val spaced_text = "assert\n  ! [\<llangle>True\<rrangle>]"
    val spaced_start =
      Position.make0 11 40 0 "" "" "macro-span-audit"
    val spaced_stop =
      Position.symbol_explode spaced_text spaced_start
    val spaced =
      parse
        (Parser_Lex_Util.positioned_content_source
          spaced_text spaced_start)
    val (spaced_name_pos, spaced_bang_pos, spaced_invocation_pos) =
      (case spaced of
         UE_Macro
           (path, MP_Arguments [UE_Literal (LP_ValAntiq _)],
            macro_layout) =>
           let
             val name_pos = path_position path
             val bang_pos =
               the_source_token_position macro_layout Bang_Token
             val invocation_pos = source_span macro_layout
           in
           (audit_assert "generic macro path changed"
              (render_path path = "assert");
            audit_assert "generic macro name span moved"
              (Position.offset_of name_pos =
                Position.offset_of spaced_start);
            audit_assert "generic whitespace before bang was lost"
              (Position.end_offset_of name_pos <>
                Position.offset_of bang_pos);
            audit_assert "generic invocation start moved"
              (Position.offset_of invocation_pos =
                Position.offset_of spaced_start);
            audit_assert "generic invocation end moved"
              (Position.end_offset_of invocation_pos =
                Position.offset_of spaced_stop);
            (name_pos, bang_pos, invocation_pos))
           end
       | _ =>
           error "legacy macro regression audit: generic macro AST changed")

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) ())
          ())
    val _ = capture_elaboration spaced_text spaced_start
    val _ = capture_elaboration full_body_text full_body_start
    val _ = capture_elaboration bracket_body_text bracket_body_start

    val ignored_markup_text =
      "debug_assert!(true, let ignored = unknown_macro_markup; ignored)"
    val ignored_markup_start =
      Position.make0 13 90 0 "" "" "macro-ignored-body-markup-audit"
    val _ =
      capture_elaboration ignored_markup_text ignored_markup_start

    val matches_text =
      "matches!(Some(\<llangle>1 :: nat\<rrangle>), Some(_))"
    val matches_start =
      Position.make0 17 80 0 "" "" "macro-markup-audit"
    val matches_stop =
      Position.symbol_explode matches_text matches_start
    val matches =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    matches_text matches_start)) ())
          ())
    val (matches_name_pos, matches_bang_pos, matches_invocation_pos) =
      (case matches of
         UE_Macro
           (path,
            MP_Matches
              (UE_Call (UC_Path call_path, [_], _),
               P_Constr (pattern_path, [P_Wild _], _)),
            macro_layout) =>
           if render_path path = "matches" andalso
               render_path call_path = "Some" andalso
               render_path pattern_path = "Some"
           then
             (path_position path,
              the_source_token_position macro_layout Bang_Token,
              source_span macro_layout)
           else error "legacy macro regression audit: matches paths changed"
       | _ =>
           error "legacy macro regression audit: matches macro AST changed")
    val _ =
      audit_assert "matches name and bang stopped being adjacent"
        (Position.end_offset_of matches_name_pos =
          Position.offset_of matches_bang_pos)
    val _ =
      audit_assert "matches invocation start moved"
        (Position.offset_of matches_invocation_pos =
          Position.offset_of matches_start)
    val _ =
      audit_assert "matches invocation end moved across Isabelle symbols"
        (Position.end_offset_of matches_invocation_pos =
          Position.offset_of matches_stop)

    val registered_text = "shout!(true)"
    val registered_start =
      Position.make0 23 120 0 "" "" "macro-registered-markup-audit"
    val registered =
      parse
        (Parser_Lex_Util.positioned_content_source
          registered_text registered_start)
    val (registered_name_pos, registered_bang_pos) =
      (case registered of
         UE_Macro
           (path,
            MP_Arguments [UE_Literal (LP_Bool (true, _))],
            macro_layout) =>
           if render_path path = "shout"
           then
             (path_position path,
              the_source_token_position macro_layout Bang_Token)
           else error "legacy macro regression audit: registered macro path changed"
       | _ =>
           error "legacy macro regression audit: registered macro AST changed")
    val _ =
      audit_assert "registered macro name and bang stopped being adjacent"
        (Position.end_offset_of registered_name_pos =
          Position.offset_of registered_bang_pos)
    val _ = capture_elaboration registered_text registered_start

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
    fun has_markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun has_urust_entity pos =
      has_entity_markup "urust_var" pos
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
         | _ =>
             error
               "legacy macro regression audit: binder entity markup changed")
      end
    val _ =
      audit_assert "generic built-in macro keyword markup moved"
        (has_markup Markup.keyword1N spaced_name_pos)
    val _ =
      audit_assert "generic built-in macro hover range moved"
        (has_markup Markup.typingN spaced_name_pos)
    val spaced_bang_markup_pos = spaced_bang_pos
    val _ =
      audit_assert "generic built-in macro bang markup moved"
        (has_markup Markup.operatorN spaced_bang_markup_pos)
    val _ =
      audit_assert "generic macro invocation lost its symbol-counted end"
        (Position.end_offset_of spaced_invocation_pos =
          Position.offset_of spaced_stop)
    val _ =
      audit_assert "matches keyword markup moved"
        (has_markup Markup.keyword1N matches_name_pos)
    val matches_bang_markup_pos = matches_bang_pos
    val _ =
      audit_assert "matches bang operator markup moved"
        (has_markup Markup.operatorN matches_bang_markup_pos)
    val _ =
      audit_assert "registered identifier notation markup moved"
        (has_entity_markup
          Micro_Rust_Names.notationN registered_name_pos)
    val _ =
      audit_assert "registered identifier dispatch styling moved"
        (has_markup Markup.keyword3N registered_name_pos)

    val (_, full_body_let_keyword) =
      token_position full_body_text full_body_start "let" 0
    val (_, full_body_else_keyword) =
      token_position full_body_text full_body_start "else" 0
    val (_, full_body_semicolon) =
      token_position full_body_text full_body_start ";" 0
    val (_, full_body_left_paren) =
      token_position full_body_text full_body_start "(" 0
    val (_, full_body_right_paren) =
      token_position full_body_text full_body_start ")"
        (size full_body_text - 1)
    val (full_body_definition_raw, full_body_definition) =
      token_position full_body_text full_body_start "flag" 0
    val (_, full_body_reference) =
      token_position full_body_text full_body_start "flag"
        (full_body_definition_raw + size "flag")
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " keyword markup moved")
            (has_markup Markup.keyword1N position))
        [(full_body_let_keyword, "full-body let"),
         (full_body_if_token, "full-body if"),
         (full_body_else_keyword, "full-body else")]
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " delimiter markup moved")
            (has_markup Markup.delimiterN position))
        [(full_body_semicolon, "full-body semicolon"),
         (full_body_left_paren, "full-body opening parenthesis"),
         (full_body_right_paren, "full-body closing parenthesis")]
    val _ =
      audit_assert "full-body built-in macro keyword markup moved"
        (has_markup Markup.keyword1N full_body_name_pos)
    val _ =
      audit_assert "full-body built-in macro hover range moved"
        (has_markup Markup.typingN full_body_name_pos)
    val _ =
      audit_assert "full-body macro bang operator markup moved"
        (has_markup Markup.operatorN full_body_bang_markup_pos)
    val _ =
      audit_assert "bracket built-in macro hover range moved"
        (has_markup Markup.typingN bracket_body_name_pos)
    val _ =
      audit_assert "retained full-body binder navigation changed"
        (has_markup Markup.boundN full_body_definition andalso
         has_markup Markup.boundN full_body_reference andalso
         entity_id Markup.defN full_body_definition =
           entity_id Markup.refN full_body_reference)

    val (_, bracket_const_keyword) =
      token_position bracket_body_text bracket_body_start "const" 0
    val (_, bracket_comma) =
      token_position bracket_body_text bracket_body_start "," 0
    val (_, bracket_semicolon) =
      token_position bracket_body_text bracket_body_start ";" 0
    val (_, bracket_left) =
      token_position bracket_body_text bracket_body_start "[" 0
    val (_, bracket_right) =
      token_position bracket_body_text bracket_body_start "]" 0
    val _ =
      audit_assert "full-body const keyword markup moved"
        (has_markup Markup.keyword1N bracket_const_keyword)
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " delimiter markup moved")
            (has_markup Markup.delimiterN position))
        [(bracket_comma, "full-body top-level comma"),
         (bracket_semicolon, "bracket full-body semicolon"),
         (bracket_left, "full-body opening bracket"),
         (bracket_right, "full-body closing bracket")]

    val (_, ignored_let_keyword) =
      token_position ignored_markup_text ignored_markup_start "let" 0
    val (_, ignored_semicolon) =
      token_position ignored_markup_text ignored_markup_start ";" 0
    val (ignored_definition_raw, ignored_definition) =
      token_position ignored_markup_text ignored_markup_start "ignored" 0
    val (_, ignored_reference) =
      token_position ignored_markup_text ignored_markup_start "ignored"
        (ignored_definition_raw + size "ignored")
    val _ =
      audit_assert "ignored full-body let lost syntactic keyword markup"
        (has_markup Markup.keyword1N ignored_let_keyword)
    val _ =
      audit_assert "ignored full-body semicolon lost delimiter markup"
        (has_markup Markup.delimiterN ignored_semicolon)
    val _ =
      audit_assert "ignored full-body binder entered semantic markup"
        (not (has_markup Markup.boundN ignored_definition) andalso
         not (has_markup Markup.boundN ignored_reference) andalso
         not (has_urust_entity ignored_definition) andalso
         not (has_urust_entity ignored_reference))

    val full_body_parent_term =
      checked
        ("debug_assert!(let observed = macro_audit_marker; " ^
         "if observed { observed } else { false })")
    val full_body_bracket_term =
      checked
        ("debug_assert![let observed = macro_audit_marker; " ^
         "if observed { observed } else { false }]")
    val _ =
      audit_assert "full-body delimiters changed lowering"
        (Term.aconv (full_body_parent_term, full_body_bracket_term))
    val _ =
      audit_assert "retained full-body initializer evaluated more than once"
        (count_constant
          \<^const_name>\<open>macro_audit_marker\<close>
          full_body_parent_term = 1)

    val ignored_full_body_term =
      checked
        ("debug_assert!(true, " ^
         "let ignored = macro_audit_ignored_marker; ignored)")
    val _ =
      audit_assert "ignored full-body assertion argument entered the term"
        (Term.aconv
          (ignored_full_body_term, checked "debug_assert!(true)"))
    val _ =
      audit_assert "ignored full-body initializer entered the term"
        (count_constant
          \<^const_name>\<open>macro_audit_ignored_marker\<close>
          ignored_full_body_term = 0)
    val _ =
      audit_assert "ignored full-body message argument entered the term"
        (Term.aconv
          (checked
            ("panic!(\"kept\", " ^
             "let ignored = macro_audit_ignored_marker; ignored)"),
           checked "panic!(\"kept\")"))

    val vec_full_body_term =
      checked
        ("vec![" ^
         "let first = macro_audit_vec_first; first, " ^
         "let second = macro_audit_vec_second; second]")
    val vec_grouped_array_term =
      checked
        ("[(let first = macro_audit_vec_first; first), " ^
         "(let second = macro_audit_vec_second; second)]")
    val _ =
      audit_assert "vec! complete-body element order changed"
        (Term.aconv (vec_full_body_term, vec_grouped_array_term))
    val _ =
      audit_assert "vec! complete-body elements were not evaluated once each"
        (count_constant
           \<^const_name>\<open>macro_audit_vec_first\<close>
           vec_full_body_term = 1 andalso
         count_constant
           \<^const_name>\<open>macro_audit_vec_second\<close>
           vec_full_body_term = 1)

    val _ =
      audit_assert "ignored assertion arguments entered the term"
        (Term.aconv
          (unchecked "assert!(true, unknown_ignored, 1 + false)",
           unchecked "assert!(true)"))
    val _ =
      audit_assert "ignored panic arguments entered the term"
        (Term.aconv
          (unchecked "panic!(\"kept\", unknown_ignored, { return missing; })",
           unchecked "panic!(\"kept\")"))
    val _ =
      audit_assert "debug_assert! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert!(true)",
           unchecked "assert!(true)"))
    val _ =
      audit_assert "debug_assert_eq! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert_eq!(1, 1)",
           unchecked "assert_eq!(1, 1)"))
    val _ =
      audit_assert "debug_assert_ne! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert_ne!(1, 2)",
           unchecked "assert_ne!(1, 2)"))
    val _ =
      audit_assert "todo! stopped aliasing unimplemented!"
        (Term.aconv
          (unchecked "todo!(\"later\")",
           unchecked "unimplemented!(\"later\")"))
    val _ =
      audit_assert "unreachable! stopped aliasing panic!"
        (Term.aconv
          (unchecked "unreachable!(\"never\")",
           unchecked "panic!(\"never\")"))
    val _ =
      audit_assert "vec! stopped reusing the array builder"
        (Term.aconv
          (unchecked "vec![1, 2, 3]",
           unchecked "[1, 2, 3]"))
    val legacy_ref_address =
      Term.map_types (K dummyT) \<^term>\<open>ref_address\<close>
    fun address_target source =
      (case unchecked source of
         Const (name, _) $ target $ _
           => if name = \<^const_name>\<open>bindlift1\<close> then target
              else error "legacy macro regression audit: address macro stopped using bindlift1"
       | _ =>
           error "legacy macro regression audit: address macro term shape changed")
    val _ =
      audit_assert "addr_of! stopped using the exact legacy ref_address target"
        (Term.aconv
          (address_target "addr_of!(macro_audit_ref)",
           legacy_ref_address))
    val _ =
      audit_assert "addr_of_mut! stopped using the exact legacy ref_address target"
        (Term.aconv
          (address_target "addr_of_mut!(macro_audit_ref)",
           legacy_ref_address))

    fun is_recovered_full_body expression =
      (case expression of
         UE_Macro
           (path,
            MP_Arguments
              [UE_Let
                (P_Ident ("recovered", _),
                 UE_Literal (LP_Bool (true, _)),
                 UE_If
                   (UE_Path condition_path,
                    UE_Block (UE_Path then_path, _),
                    SOME (UE_Block _), _),
                 _)],
            _) =>
           render_path path = "debug_assert" andalso
           render_path condition_path = "recovered" andalso
           render_path then_path = "recovered"
       | _ => false)
    fun reject_then_recover bad =
      let
        val _ =
          (case Exn.result parse_text bad of
             Exn.Res _ =>
               error
                 ("legacy macro regression audit: malformed full body " ^
                  quote bad ^ " unexpectedly parsed")
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else ())
        val recovered =
          parse_text
            ("debug_assert!(let recovered = true; " ^
             "if recovered { recovered } else { false })")
      in
        audit_assert
          ("malformed full body leaked parser state after " ^ quote bad)
          (is_recovered_full_body recovered)
      end
    val _ =
      List.app reject_then_recover
        ["debug_assert!(let flag = true;)",
         "assert_eq!(let left = true; left,, false)",
         "debug_assert!(let flag = true; if flag { true } else { false)",
         "debug_assert![let flag = true; flag)"]

    val matches_term =
      checked "matches!(macro_audit_scrutinee, Some(_))"
    val explicit_case =
      checked
        "match_case macro_audit_scrutinee { Some(_) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }"
    val _ =
      audit_assert "matches! stopped using ordinary case compilation"
        (Term.aconv (matches_term, explicit_case))
    val _ =
      audit_assert "matches! evaluated its scrutinee more than once"
        (count_constant
          \<^const_name>\<open>macro_audit_scrutinee\<close>
          matches_term = 1)
    val _ =
      audit_assert "matches! lost its requested-pattern true branch"
        (count_constant \<^const_name>\<open>True\<close> matches_term = 1)
    val _ =
      audit_assert "matches! lost its wildcard false fallback"
        (count_constant \<^const_name>\<open>False\<close> matches_term = 1)
  in
    val _ = writeln "Legacy macro structure, span, and markup regressions passed"
  end
\<close>

section\<open> Closure AST, lowering, and binder-navigation audit \<close>

consts
  closure_audit_marker ::
    \<open>(unit, nat, nat, unit, unit, unit) expression\<close>

text\<open>
These checks pin the second-class closure boundary below the source-level examples. They retain
ordered pattern-shaped formals and the complete closure span, prove that grouping alone re-enters
ordinary expression positions, and inspect the checked shallow term for the exact frontend shape.
The markup checks lock definition/reference navigation across ordinary, duplicate, nested, and
shadowed formals.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("closure regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "closure regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_abstractions (Abs (_, _, body)) =
          1 + count_abstractions body
      | count_abstractions (left $ right) =
          count_abstractions left + count_abstractions right
      | count_abstractions _ = 0

    fun is_grouped_closure (UE_Group (UE_Closure _, _)) = true
      | is_grouped_closure _ = false

    val ast_text = "|first, second| second"
    val ast_start =
      Position.make0 5 20 100 "" "" "closure-ast-audit"
    val ast_stop =
      Position.symbol_explode ast_text ast_start
    val ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          ast_text ast_start)
    val _ =
      (case ast of
         UE_Closure
           ([P_Ident ("first", _), P_Ident ("second", _)],
            UE_Path body_path, closure_layout) =>
           (audit_assert "closure body path changed"
              (render_path body_path = "second");
            audit_assert "full closure span start moved"
              (Position.offset_of (source_span closure_layout) =
                Position.offset_of ast_start);
            audit_assert "full closure span end moved"
              (Position.end_offset_of
                (source_span closure_layout) =
                Position.offset_of ast_stop);
            audit_assert "expression_position lost the closure span"
              (Position.offset_of (expression_position ast) =
                 Position.offset_of
                   (source_span closure_layout) andalso
               Position.end_offset_of (expression_position ast) =
                 Position.end_offset_of
                   (source_span closure_layout)))
       | _ =>
           error "closure regression audit: closure AST changed")

    val _ =
      (case parse_text "let f = (|| 1); ()" of
         UE_Let (_, initializer, _, _) =>
           audit_assert "grouped closure initializer stopped parsing"
             (is_grouped_closure initializer)
       | _ =>
           error "closure regression audit: grouped initializer AST changed")
    val _ =
      (case parse_text "target = (|| 1)" of
         UE_Assign (_, _, rhs, _) =>
           audit_assert "grouped closure assignment RHS stopped parsing"
             (is_grouped_closure rhs)
       | _ =>
           error "closure regression audit: grouped assignment AST changed")
    val _ =
      (case parse_text "1 + (|| 2)" of
         UE_Bin (_, _, rhs, _) =>
           audit_assert "grouped closure binary operand stopped parsing"
             (is_grouped_closure rhs)
       | _ =>
           error "closure regression audit: grouped binary AST changed")
    val _ =
      (case parse_text "if (|| true) { () }" of
         UE_If (condition, _, _, _) =>
           audit_assert "grouped closure condition stopped parsing"
             (is_grouped_closure condition)
       | _ =>
           error "closure regression audit: grouped condition AST changed")
    val _ =
      (case parse_text "match (|| true) { _ \<Rightarrow> () }" of
         UE_Match (_, scrutinee, _, _) =>
           audit_assert "grouped closure scrutinee stopped parsing"
             (is_grouped_closure scrutinee)
       | _ =>
           error "closure regression audit: grouped scrutinee AST changed")
    val _ =
      (case parse_text "for item in (|| []) { () }" of
         UE_For (_, iterable, _, _) =>
           audit_assert "grouped closure iterable stopped parsing"
             (is_grouped_closure iterable)
       | _ =>
           error "closure regression audit: grouped iterable AST changed")
    val _ =
      (case
          parse_text
            "match true { true \<Rightarrow> (|| true), false \<Rightarrow> (|| false) }" of
         UE_Match
           (_, _,
            [UR_Arm (_, _, first, _),
             UR_Arm (_, _, second, _)], _) =>
           (audit_assert "first grouped closure arm stopped parsing"
              (is_grouped_closure first);
            audit_assert "second grouped closure arm stopped parsing"
              (is_grouped_closure second))
       | _ =>
           error "closure regression audit: grouped arm AST changed")
    val _ =
      (case parse_text "(|| 1); ()" of
         UE_Seq (left, _, _) =>
           audit_assert "grouped closure sequencing-left stopped parsing"
             (is_grouped_closure left)
       | _ =>
           error "closure regression audit: grouped sequence AST changed")
    val _ =
      (case parse_text "|| (|| 1)" of
         UE_Closure (_, body, _) =>
           audit_assert "grouped nested closure body stopped parsing"
             (is_grouped_closure body)
       | _ =>
           error "closure regression audit: grouped nested closure AST changed")

    val guard =
      parse_text
        "match_case Some(()) { Some(_) if || true \<Rightarrow> (), None \<Rightarrow> () }"
    val _ =
      (case guard of
         UE_Match
           (_, _,
            UR_Arm
              (_, SOME
                (UE_Closure
                  ([], UE_Literal (LP_Bool (true, _)), _), _),
               _, _) :: _,
            _) =>
           ()
       | _ =>
           error
             "closure regression audit: a closure stopped parsing as a complete guard body")

    val shape =
      checked
        "|first, second| \<epsilon>\<open>closure_audit_marker\<close>"
    val _ =
      audit_assert "closure did not lower to exactly one literal"
        (count_constant \<^const_name>\<open>literal\<close> shape = 1)
    val _ =
      audit_assert "closure did not lower to exactly one FunctionBody"
        (count_constant \<^const_name>\<open>FunctionBody\<close> shape = 1)
    val _ =
      audit_assert "closure did not lower to one abstraction per formal"
        (count_abstractions shape = 2)
    val _ =
      audit_assert "closure body was lowered more than once"
        (count_constant
          \<^const_name>\<open>closure_audit_marker\<close> shape = 1)

    fun closure_payload
        (Const (name, _) $ payload) =
          if name = \<^const_name>\<open>literal\<close>
          then payload
          else error
            "closure regression audit: closure wrapper stopped using literal"
      | closure_payload _ =
          error "closure regression audit: closure wrapper shape changed"

    val ordered =
      checked
        "|first, second| \<llangle>(first :: nat, second :: bool)\<rrangle>"
    val (ordered_formals, _) =
      Term.strip_abs (closure_payload ordered)
    val _ =
      audit_assert "closure abstraction order changed"
        (map #2 ordered_formals = [HOLogic.natT, HOLogic.boolT])

    val duplicate =
      checked "|same, same, same| same"
    val (duplicate_formals, duplicate_body) =
      Term.strip_abs (closure_payload duplicate)
    val _ =
      audit_assert "duplicate closure formals stopped producing abstractions"
        (length duplicate_formals = 3)
    val _ =
      (case duplicate_body of
         Const (function_body_name, _) $
           (Const (literal_name, _) $ Bound 0) =>
           (audit_assert "duplicate closure body lost FunctionBody"
              (function_body_name =
                \<^const_name>\<open>FunctionBody\<close>);
            audit_assert "duplicate closure body lost literal lowering"
              (literal_name = \<^const_name>\<open>literal\<close>))
       | _ =>
           error
             "closure regression audit: innermost duplicate no longer shadows earlier formals")

    val allocator_start =
      Position.make0 9 30 300 "" "" "closure-allocator-audit"
    val allocator_positions =
      [allocator_start,
       Position.symbol_explode "first " allocator_start,
       Position.symbol_explode "first second " allocator_start]
    val (allocated, allocated_environment) =
      URust_Resolution.allocate_closure_formals ctxt
        URust_Resolution.empty_environment
        (map2 pair ["first", "second", "first"] allocator_positions)
    val allocated_names =
      map
        (fn Free (name, _) => name
          | _ =>
              error
                "closure regression audit: allocator returned a non-Free formal")
        allocated
    val _ =
      audit_assert "closure allocator reused a formal identity"
        (length (distinct (op =) allocated_names) = 3)
    val _ =
      audit_assert "closure allocator did not preserve source order"
        (length allocated = 3)
    val _ =
      audit_assert "later duplicate did not win in the final environment"
        (case URust_Resolution.lookup_local
            allocated_environment "first" of
           SOME selected => Term.aconv (selected, List.last allocated)
         | NONE => false)

    val resolved_dispatch =
      checked "|closureRole| closureRole(closureRole)"
    val _ =
      audit_assert "checked closure retained an unresolved dispatch marker"
        (count_constant
          \<^const_name>\<open>urust_dispatch\<close>
          resolved_dispatch = 0)

    fun find_from text needle offset =
      if offset + size needle > size text
      then error
        ("closure regression audit: missing " ^ quote needle)
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

    val ordinary_text = "|alpha| alpha"
    val ordinary_start =
      Position.make0 11 40 400 "" "" "closure-markup-ordinary"
    val duplicate_text = "|dup, dup| dup"
    val duplicate_start =
      Position.make0 13 50 500 "" "" "closure-markup-duplicate"
    val nested_text =
      "|outer| (|inner| if true { outer } else { inner })"
    val nested_start =
      Position.make0 17 60 600 "" "" "closure-markup-nested"
    val shadow_text =
      "|shadow| { let shadow = shadow; shadow }"
    val shadow_start =
      Position.make0 19 70 700 "" "" "closure-markup-shadow"

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) ())
          ())
    val _ = capture_elaboration ordinary_text ordinary_start
    val _ = capture_elaboration duplicate_text duplicate_start
    val _ = capture_elaboration nested_text nested_start
    val _ = capture_elaboration shadow_text shadow_start

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_bound position =
      exists
        (fn (name, properties) =>
          name = Markup.boundN andalso
            has_position properties position)
        markup
    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "closure regression audit: binder entity markup changed")
      end
    fun audit_navigation label definition reference =
      (audit_assert (label ^ " definition lost bound markup")
         (has_bound definition);
       audit_assert (label ^ " reference lost bound markup")
         (has_bound reference);
       audit_assert (label ^ " reference stopped targeting its formal")
         (entity_id Markup.defN definition =
          entity_id Markup.refN reference))

    val (ordinary_def_offset, ordinary_definition) =
      token_position ordinary_text ordinary_start "alpha" 0
    val (_, ordinary_reference) =
      token_position ordinary_text ordinary_start "alpha"
        (ordinary_def_offset + size "alpha")
    val _ =
      audit_navigation
        "ordinary closure formal"
        ordinary_definition ordinary_reference

    val (duplicate_first_offset, duplicate_first_definition) =
      token_position duplicate_text duplicate_start "dup" 0
    val (duplicate_second_offset, duplicate_second_definition) =
      token_position duplicate_text duplicate_start "dup"
        (duplicate_first_offset + size "dup")
    val (_, duplicate_reference) =
      token_position duplicate_text duplicate_start "dup"
        (duplicate_second_offset + size "dup")
    val duplicate_first_id =
      entity_id Markup.defN duplicate_first_definition
    val duplicate_second_id =
      entity_id Markup.defN duplicate_second_definition
    val _ =
      audit_assert "duplicate formal definitions reused an entity ID"
        (duplicate_first_id <> duplicate_second_id)
    val _ =
      audit_navigation
        "duplicate closure formal"
        duplicate_second_definition duplicate_reference
    val _ =
      audit_assert "duplicate body reference targeted the first formal"
        (entity_id Markup.refN duplicate_reference <>
          duplicate_first_id)

    val (nested_outer_offset, nested_outer_definition) =
      token_position nested_text nested_start "outer" 0
    val (nested_inner_offset, nested_inner_definition) =
      token_position nested_text nested_start "inner" 0
    val (_, nested_outer_reference) =
      token_position nested_text nested_start "outer"
        (nested_outer_offset + size "outer")
    val (_, nested_inner_reference) =
      token_position nested_text nested_start "inner"
        (nested_inner_offset + size "inner")
    val _ =
      audit_navigation
        "nested outer closure formal"
        nested_outer_definition nested_outer_reference
    val _ =
      audit_navigation
        "nested inner closure formal"
        nested_inner_definition nested_inner_reference
    val _ =
      audit_assert "nested closure formals reused an entity ID"
        (entity_id Markup.defN nested_outer_definition <>
          entity_id Markup.defN nested_inner_definition)

    val (shadow_outer_offset, shadow_outer_definition) =
      token_position shadow_text shadow_start "shadow" 0
    val (shadow_inner_offset, shadow_inner_definition) =
      token_position shadow_text shadow_start "shadow"
        (shadow_outer_offset + size "shadow")
    val (shadow_outer_reference_offset, shadow_outer_reference) =
      token_position shadow_text shadow_start "shadow"
        (shadow_inner_offset + size "shadow")
    val (_, shadow_inner_reference) =
      token_position shadow_text shadow_start "shadow"
        (shadow_outer_reference_offset + size "shadow")
    val _ =
      audit_navigation
        "shadowed closure formal"
        shadow_outer_definition shadow_outer_reference
    val _ =
      audit_navigation
        "shadowing let binder"
        shadow_inner_definition shadow_inner_reference
    val _ =
      audit_assert "shadowing let binder reused the closure formal entity ID"
        (entity_id Markup.defN shadow_outer_definition <>
          entity_id Markup.defN shadow_inner_definition)
  in
    val _ =
      writeln
        "Closure AST, lowering, allocator, dispatch, and markup regressions passed"
end
\<close>


section\<open> Cast AST, lowering, markup, and recovery \<close>

text\<open>
The cast audit pins the closed target representation, left association,
prefix-before-cast precedence, source position, exact lowering table, semantic
collapses, reserved-word markup, and parser-state recovery after malformed
targets.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("cast regression audit: " ^ message)

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left =
        Position.end_offset_of right

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "cast regression audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun exact_source_position source spelling cursor =
      let
        val text = Input.text_of source
        fun seek offset =
          if offset + size spelling > size text then
            error
              ("cast regression audit: missing " ^
                quote spelling)
          else if
            String.substring
              (text, offset, size spelling) = spelling
          then offset
          else seek (offset + 1)
        val raw =
          let
            fun from offset =
              if offset < cursor then from (offset + 1)
              else seek offset
          in from 0 end
        val layout =
          Parser_Lex_Util.make_source_layout source
      in
        Position.range_position
          (Parser_Lex_Util.text_range
            layout (raw, spelling))
      end

    fun path_named expected (UE_Path path) =
          render_path path = expected
      | path_named _ _ = false

    fun target_is expected (SCT_Primitive (actual, _)) =
          expected = actual
      | target_is _ _ = false

    val positioned_text = "operand as *mut usize"
    val positioned_start =
      Position.make0 9 14 0 "" "" ""
    val positioned_ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          positioned_text positioned_start)
    val as_offset = size "operand "
    val expected_as =
      Position.symbol_explode
        (String.substring (positioned_text, 0, as_offset))
        positioned_start
    val _ =
      (case positioned_ast of
         UE_Cast
           (operand,
            SCT_Primitive
              (CT_RawPointer (RPM_Mut, UT_Usize),
               target_type_pos),
            cast_layout) =>
           (audit_assert "cast operand changed"
              (path_named "operand" operand);
            audit_assert "as position moved"
              (Position.offset_of
                (the_source_token_position
                  cast_layout (Keyword_Token "as")) =
                Position.offset_of expected_as);
            audit_assert "cast target type-token range moved"
              (let
                 val source =
                   Parser_Lex_Util.positioned_content_source
                     positioned_text positioned_start
               in
                 same_range target_type_pos
                   (exact_source_position source
                     "usize" 0)
               end))
       | _ => error "cast regression audit: positioned cast AST changed")

    val cast_type_cases =
      [("u8", "u8"),
       ("u16", "u16"),
       ("u32", "u32"),
       ("u64", "u64"),
       ("usize", "usize"),
       ("i32", "i32"),
       ("i64", "i64"),
       ("*const u8", "u8"),
       ("*const u16", "u16"),
       ("*const u32", "u32"),
       ("*const u64", "u64"),
       ("*const usize", "usize"),
       ("*mut u8", "u8"),
       ("*mut u16", "u16"),
       ("*mut u32", "u32"),
       ("*mut u64", "u64"),
       ("*mut usize", "usize")]

    val _ =
      cast_type_cases
      |> map_index
          (fn (index, (target_text, type_text)) =>
            let
              val text =
                "\<llangle>0 :: 64 word\<rrangle> as " ^
                  target_text
              val source =
                Parser_Lex_Util.positioned_content_source text
                  (Position.make0 (40 + index)
                    (2000 + index * 100) 0 "" ""
                    ("cast-type-range-" ^
                      string_of_int index))
              val expected =
                exact_source_position source type_text
                  0
            in
              (case parse_source source of
                 UE_Cast
                   (_, primitive_target as SCT_Primitive _, _) =>
                   (case
                       source_cast_target_type_position
                         primitive_target of
                      SOME actual =>
                        audit_assert
                          ("cast target range changed for " ^
                            quote target_text)
                          (same_range actual expected)
                    | NONE =>
                        error
                          "cast regression audit: primitive target lost its type range")
               | _ =>
                   error
                     ("cast regression audit: target AST changed for " ^
                       quote target_text))
            end)
      |> List.app I

    val _ =
      (case parse "source.field.method()[0]? as i64" of
         UE_Cast
           (UE_Unary
             (U_Propagate,
              UE_Index
                (UE_Call
                  (UC_Method
                    (UE_Field (source, "field", _),
                     Path_Segment ("method", _, NONE)),
                   [], _),
                 UE_Literal
                   (LP_Integer
                     (Integer_Literal ("0", _, _))), _),
              _),
            SCT_Primitive (CT_Signed ST_I64, _), _) =>
           audit_assert "cast lost its complete postfix operand"
             (path_named "source" source)
       | _ =>
           error
             "cast regression audit: postfix operand AST changed")

    val _ =
      (case parse "value as u8 as u16 as i32" of
         UE_Cast
           (UE_Cast
             (UE_Cast
               (value, first, _),
              second, _),
            third, _) =>
           (audit_assert "cast chain lost its operand"
              (path_named "value" value);
            audit_assert "first cast target changed"
              (target_is (CT_Unsigned UT_U8) first);
            audit_assert "second cast target changed"
              (target_is (CT_Unsigned UT_U16) second);
            audit_assert "third cast target changed"
              (target_is (CT_Signed ST_I32) third))
       | _ =>
           error "cast regression audit: cast chain is not left-associated")

    val _ =
      (case parse "!value as u8" of
         UE_Cast
           (UE_Unary (U_Not, value, _),
            SCT_Primitive (CT_Unsigned UT_U8, _), _) =>
           audit_assert "not/cast operand changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: not-before-cast precedence changed")

    val _ =
      (case parse "*raw as *const u8" of
         UE_Cast
           (UE_Unary (U_Deref, raw, _),
            SCT_Primitive
              (CT_RawPointer (RPM_Const, UT_U8), _), _) =>
           audit_assert "deref/cast operand changed"
             (path_named "raw" raw)
       | _ =>
           error "cast regression audit: deref-before-cast precedence changed")

    val _ =
      (case parse "(!value) as u8" of
         UE_Cast
           (UE_Group
             (UE_Unary (U_Not, value, _), _),
            SCT_Primitive (CT_Unsigned UT_U8, _), _) =>
           audit_assert "grouped opposite interpretation changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: grouped prefix/cast AST changed")

    val _ =
      (case parse "(value as u32).field.method()[0]?" of
         UE_Unary
           (U_Propagate,
            UE_Index
              (UE_Call
                (UC_Method
                  (UE_Field
                    (UE_Group
                      (UE_Cast
                        (value,
                         SCT_Primitive
                           (CT_Unsigned UT_U32, _), _), _),
                     "field", _),
                   Path_Segment ("method", _, NONE)),
                 [], _),
               UE_Literal
                 (LP_Integer
                   (Integer_Literal ("0", _, _))), _),
            _) =>
           audit_assert "grouped cast postfix chain changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: grouped cast postfix AST changed")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    datatype lowering_kind =
        Unsigned_Lowering
      | Signed_Lowering
      | Pointer_Lowering

    val lowering_cases =
      [("value as u8", Unsigned_Lowering,
        \<^term>\<open>ucastu8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as u16", Unsigned_Lowering,
        \<^term>\<open>ucastu16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as u32", Unsigned_Lowering,
        \<^term>\<open>ucastu32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as u64", Unsigned_Lowering,
        \<^term>\<open>ucastu64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as usize", Unsigned_Lowering,
        \<^term>\<open>ucastu64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as i32", Signed_Lowering,
        \<^term>\<open>ucasti32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as i64", Signed_Lowering,
        \<^term>\<open>ucasti64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *const u8", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as *const u16", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as *const u32", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as *const u64", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *const usize", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *mut u8", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as *mut u16", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as *mut u32", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as *mut u64", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *mut usize", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>)]

    fun count_constant expected term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)
        term 0

    fun cast_count term =
      count_constant \<^const_name>\<open>bind1\<close> term +
      count_constant \<^const_name>\<open>raw_ptr_cast\<close> term

    fun cast_result_type typ =
      Term.map_atyps
        (fn TFree _ => dummyT
          | TVar _ => dummyT
          | atomic => atomic)
        typ

    fun expected_lowering target_function =
      Type.constraint
        (cast_result_type
          (Term.range_type (fastype_of target_function)))
        (Term.list_comb
          (Term.map_types (K dummyT) target_function,
           [unchecked "value"]))

    fun checked text =
      Syntax.check_term ctxt (unchecked text)

    val reference_type_name =
      (case \<^typ>\<open>('address, 'global, 'value) Global_Store.ref\<close> of
         Type (name, _) => name
       | _ => error "cast regression audit: reference type abbreviation changed")

    fun result_width Pointer_Lowering term =
          (case fastype_of term of
             Type (expression_name, [_, value_type, _, _, _, _]) =>
               if expression_name = \<^type_name>\<open>expression\<close>
               then
                 (case value_type of
                    Type (reference_name, [_, _, width]) =>
                      if reference_name = reference_type_name
                      then width
                      else error "cast regression audit: pointer cast result is not a reference"
                  | _ =>
                      error "cast regression audit: pointer cast result is not a reference")
               else error "cast regression audit: cast result is not an expression"
           | _ => error "cast regression audit: cast result type changed")
      | result_width _ term =
          (case fastype_of term of
             Type (expression_name, [_, value_type, _, _, _, _]) =>
               if expression_name = \<^type_name>\<open>expression\<close>
               then value_type
               else error "cast regression audit: cast result is not an expression"
           | _ => error "cast regression audit: cast result type changed")

    fun check_lowering
      (source, kind, target_function, expected_width) =
      let
        val term = unchecked source
        val checked_term = checked source
      in
        audit_assert
          ("wrong lowering for " ^ quote source)
          (Term.aconv (term, expected_lowering target_function));
        audit_assert
          ("source cast did not lower exactly once for " ^ quote source)
          (cast_count term = 1);
        audit_assert
          ("wrong result width for " ^ quote source)
          (result_width kind checked_term = expected_width)
      end

    val _ = List.app check_lowering lowering_cases

    val _ =
      audit_assert "usize stopped collapsing to u64"
        (Term.aconv
          (unchecked "value as usize",
           unchecked "value as u64"))

    val _ =
      audit_assert "pointer usize stopped collapsing to pointer u64"
        (Term.aconv
          (unchecked "value as *const usize",
           unchecked "value as *const u64"))

    val _ =
      List.app
        (fn target =>
          audit_assert
            ("pointer mutability changed lowering for " ^ target)
            (Term.aconv
              (unchecked ("value as *const " ^ target),
               unchecked ("value as *mut " ^ target))))
        ["u8", "u16", "u32", "u64", "usize"]

    val chain = unchecked "value as u8 as u32 as i64"
    val _ =
      audit_assert "three-stage chain did not lower three casts"
        (cast_count chain = 3)
    val _ =
      audit_assert "three-stage lowering lost left nesting"
        (count_constant \<^const_name>\<open>bind1\<close> chain = 3 andalso
         result_width Signed_Lowering
           (checked "value as u8 as u32 as i64") =
             \<^typ>\<open>64 word\<close>)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("cast regression audit: missing " ^ quote needle)
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

    val markup_text =
      "value as u8; value as u16; value as u32; " ^
      "value as u64; value as usize; value as i32; " ^
      "value as i64; raw as *const u8; raw as *mut usize"
    val markup_start =
      Position.make0 11 3 0 "" "" "cast-markup-audit"
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse_source
                  (Parser_Lex_Util.positioned_content_source
                    markup_text markup_start)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun has_entity_markup position =
      has_markup Markup.defN position orelse
      has_markup Markup.refN position

    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size markup_text then rev positions
          else
            (case try (find_from markup_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position markup_text markup_start needle raw
                 in collect (raw + size needle) (position :: positions) end
             | NONE => rev positions)
      in collect 0 [] end

    val keyword_spellings =
      ["as", "u8", "u16", "u32", "u64", "usize", "i32", "i64",
       "const", "mut"]
    val type_spellings =
      ["u8", "u16", "u32", "u64", "usize", "i32", "i64"]
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              (audit_assert
                 (spelling ^ " lost keyword markup")
                 (has_markup Markup.keyword1N position);
               audit_assert
                 (spelling ^ " lost typing markup")
                 (has_markup Markup.typingN position)))
            (all_token_positions spelling))
        keyword_spellings
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                (spelling ^ " received identifier entity markup")
                (not (has_entity_markup position)))
            (all_token_positions spelling))
        type_spellings
    val _ =
      List.app
        (fn position =>
          audit_assert "* stopped being operator markup in cast targets"
            (has_markup Markup.operatorN position))
        (all_token_positions "*")

    val malformed =
      ["as u8",
       "value as",
       "value as *",
       "value as *const",
       "value as *mut",
       "value as *const i32",
       "value as *mut i64",
       "value as *const bool",
       "value as *mut Target",
       "value as *mut u128",
       "value as **const u8",
       "value as *const *const u8",
       "value as *const const u8",
       "value as *mut mut u8",
       "value as &u8",
       "value as as u8",
       "value as u8 as",
       "value as u8 as *const",
       "value as ()",
       "value as [u8]",
       "value as u8,",
       "value as u8 trailing",
       "value asu8",
       "value as u32.field",
       "value as u32.method()",
       "value as u32[0]",
       "value as u32?",
       "value as u32()",
       "value as u8 as u32.field"]

    fun reject_then_recover bad =
      let
        val _ =
          (case Exn.result parse bad of
             Exn.Res _ =>
               error
                 ("cast regression audit: malformed cast accepted: " ^
                   quote bad)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else ())
        val _ =
          (case parse "value as u8" of
             UE_Cast
               (_, SCT_Primitive (CT_Unsigned UT_U8, _), _) => ()
           | _ =>
               error
                 ("cast regression audit: parser did not recover after " ^
                   quote bad))
      in () end

    val _ = List.app reject_then_recover malformed
  in
    val _ =
      writeln "Cast AST, lowering, markup, and recovery regressions passed"
  end
\<close>


section\<open> Struct-expression AST, lowering, markup, and recovery \<close>

definition d21_audit_identity1 ::
    \<open>'a \<Rightarrow> (unit, 'a, unit, unit, unit) function_body\<close>
  where \<open> d21_audit_identity1 \<equiv> lift_fun1 (\<lambda>value. value) \<close>

definition d21_audit_first2 ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> d21_audit_first2 \<equiv> lift_fun2 (\<lambda>first second. first) \<close>

definition d21_audit_truth :: bool
  where \<open> d21_audit_truth \<equiv> True \<close>

consts
  d21_audit_marker_a :: nat
  d21_audit_marker_b :: nat
  d21_audit_marker_c :: nat

micro_rust_notation (call) d21_audit_identity1 ("D21AuditOne")
micro_rust_notation (call) d21_audit_first2 ("D21AuditPair")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("struct-expression regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "struct-expression regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_named_atom name term =
      Term.fold_aterms
        (fn Free (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | Const (candidate, _) =>
              if Long_Name.base_name candidate = name
              then Integer.add 1
              else I
          | _ => I)
        term 0

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("struct-expression regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
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

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val structural_text =
      "D21AuditPair {\n" ^
      "  alpha: \<llangle>d21_audit_marker_a\<rrangle>, // retained comment\n" ^
      "  beta: D21AuditPair { gamma: \<llangle>d21_audit_marker_b\<rrangle>, " ^
        "delta: \<llangle>d21_audit_marker_c\<rrangle> }\n" ^
      "}"
    val structural_start =
      Position.make0 31 700 0 "" "" "struct-expression-audit"
    val structural_stop =
      Position.symbol_explode structural_text structural_start
    val structural_source =
      Parser_Lex_Util.positioned_content_source
        structural_text structural_start
    val structural_ast = parse structural_source

    val control_text =
      "match (D21AuditOne { value: Some(()) }) {\n" ^
      "  Some(_) \<Rightarrow> (),\n" ^
      "  None \<Rightarrow> ()\n" ^
      "}"
    val control_start =
      Position.make0 41 900 0 "" "" "struct-control-head-audit"
    val control_stop =
      Position.symbol_explode control_text control_start
    val control_source =
      Parser_Lex_Util.positioned_content_source
        control_text control_start
    val control_ast = parse control_source

    val (outer_head_raw, outer_head_pos) =
      token_position structural_text structural_start "D21AuditPair" 0
    val (alpha_raw, alpha_pos) =
      token_position structural_text structural_start "alpha" 0
    val (_, marker_a_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_a" alpha_raw
    val (beta_raw, beta_pos) =
      token_position structural_text structural_start "beta" 0
    val (nested_head_raw, nested_head_pos) =
      token_position structural_text structural_start "D21AuditPair"
        (outer_head_raw + size "D21AuditPair")
    val (gamma_raw, gamma_pos) =
      token_position structural_text structural_start "gamma" nested_head_raw
    val (_, marker_b_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_b" gamma_raw
    val (delta_raw, delta_pos) =
      token_position structural_text structural_start "delta" gamma_raw
    val (_, marker_c_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_c" delta_raw
    val (nested_close_raw, nested_close_pos) =
      token_position structural_text structural_start "}" delta_raw
    val (_, outer_close_pos) =
      token_position structural_text structural_start "}"
        (nested_close_raw + 1)
    val nested_span =
      Position.range_position
        (nested_head_pos,
         Position.symbol_explode "}" nested_close_pos)

    val (_, control_match_pos) =
      token_position control_text control_start "match" 0
    val (control_group_raw, control_group_left_pos) =
      token_position control_text control_start "(" 0
    val (control_head_raw, control_head_pos) =
      token_position control_text control_start "D21AuditOne"
        control_group_raw
    val (control_label_raw, control_label_pos) =
      token_position control_text control_start "value" control_head_raw
    val (control_struct_close_raw, control_struct_close_pos) =
      token_position control_text control_start "}" control_label_raw
    val (_, control_group_right_pos) =
      token_position control_text control_start ")"
        (control_struct_close_raw + 1)
    val control_struct_span =
      Position.range_position
        (control_head_pos,
         Position.symbol_explode "}" control_struct_close_pos)
    val control_group_span =
      Position.range_position
        (control_group_left_pos,
         Position.symbol_explode ")" control_group_right_pos)

    val _ =
      (case structural_ast of
         UE_Struct
           (head,
            [SE_Field
               ("alpha", first_label_pos,
                UE_Literal (LP_ValAntiq _)),
             SE_Field
               ("beta", second_label_pos,
                nested as
                  UE_Struct
                    (nested_head,
                     [SE_Field
                        ("gamma", third_label_pos,
                         UE_Literal (LP_ValAntiq _)),
                      SE_Field
                        ("delta", fourth_label_pos,
                         UE_Literal (LP_ValAntiq _))],
                     nested_layout))],
            outer_layout) =>
           (audit_assert "outer head changed"
              (render_path head = "D21AuditPair");
            audit_assert "nested head changed"
              (render_path nested_head = "D21AuditPair");
            audit_assert "outer label order or positions changed"
              (same_range first_label_pos alpha_pos andalso
               same_range second_label_pos beta_pos);
            audit_assert "nested label order or positions changed"
              (same_range third_label_pos gamma_pos andalso
               same_range fourth_label_pos delta_pos);
            audit_assert "outer span no longer covers head through closing brace"
              (Position.offset_of (source_span outer_layout) =
                 Position.offset_of outer_head_pos andalso
               Position.end_offset_of (source_span outer_layout) =
                 Position.offset_of structural_stop);
            audit_assert "nested struct span changed"
              (same_range
                (source_span nested_layout) nested_span);
            audit_assert "expression_position lost the nested struct boundary"
              (same_range (expression_position nested) nested_span))
       | _ =>
           error "struct-expression regression audit: structural AST changed")

    val _ =
      (case control_ast of
         UE_Match
           (MF_Auto,
            UE_Group
              (nested as
                 UE_Struct
                   (head,
                    [SE_Field ("value", label_pos, _)],
                    struct_layout),
               group_layout),
            _, match_layout) =>
           (audit_assert "grouped control-head struct changed"
              (render_path head = "D21AuditOne");
            audit_assert "grouped control-head label position changed"
              (same_range label_pos control_label_pos);
            audit_assert "grouped control-head struct span changed"
              (same_range
                 (source_span struct_layout)
                 control_struct_span andalso
               same_range
                 (expression_position nested) control_struct_span);
            audit_assert "grouped control-head span changed"
              (same_range
                (source_span group_layout) control_group_span);
            audit_assert "grouped control-head match span changed"
              (Position.offset_of (source_span match_layout) =
                 Position.offset_of control_match_pos andalso
               Position.end_offset_of (source_span match_layout) =
                 Position.offset_of control_stop))
       | _ =>
           error
             "struct-expression regression audit: grouped control-head AST changed")

    fun dest_funcall2 term =
      (case Term_Position.strip_positions term of
         Const (name, _) $ function $ first $ second =>
           if name = \<^const_name>\<open>funcall2\<close>
           then (function, first, second)
           else
             error
               ("struct-expression regression audit: expected funcall2, found " ^
                 quote name)
       | _ =>
           error "struct-expression regression audit: funcall2 shape changed")

    val structural_term =
      Parser_Test_Elaboration.expression ctxt structural_source
    val (outer_function, outer_first, outer_second) =
      dest_funcall2 structural_term
    val (nested_function, nested_first, nested_second) =
      dest_funcall2 outer_second
    val _ =
      audit_assert "registered wrapper head was not retained"
        (count_constant
          \<^const_name>\<open>d21_audit_first2\<close>
          outer_function = 1 andalso
         count_constant
          \<^const_name>\<open>d21_audit_first2\<close>
          nested_function = 1)
    val _ =
      audit_assert "first initializer left the first call argument"
        (count_constant
           \<^const_name>\<open>d21_audit_marker_a\<close>
           outer_first = 1 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_b\<close>
           outer_first = 0)
    val _ =
      audit_assert "nested initializer order changed"
        (count_constant
           \<^const_name>\<open>d21_audit_marker_b\<close>
           nested_first = 1 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_c\<close>
           nested_first = 0 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_c\<close>
           nested_second = 1)
    val _ =
      List.app
        (fn marker =>
          audit_assert
            ("initializer marker " ^ quote marker ^
              " was duplicated or dropped")
            (count_constant marker structural_term = 1))
        [\<^const_name>\<open>d21_audit_marker_a\<close>,
         \<^const_name>\<open>d21_audit_marker_b\<close>,
         \<^const_name>\<open>d21_audit_marker_c\<close>]
    val _ =
      List.app
        (fn label =>
          audit_assert
            ("label " ^ quote label ^ " leaked into the HOL term")
            (count_named_atom label structural_term = 0))
        ["alpha", "beta", "gamma", "delta"]

    val canonical =
      checked
        ("D21AuditPair { first: \<llangle>d21_audit_marker_a\<rrangle>, " ^
         "second: \<llangle>d21_audit_marker_b\<rrangle> }")
    val renamed =
      checked
        ("D21AuditPair { unknown: \<llangle>d21_audit_marker_a\<rrangle>, " ^
         "unknown: \<llangle>d21_audit_marker_b\<rrangle> }")
    val _ =
      audit_assert "labels stopped erasing completely"
        (Term.aconv (canonical, renamed))

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                (ignore
                   (Parser_Test_Elaboration.expression ctxt structural_source);
                 ignore
                   (Parser_Test_Elaboration.expression ctxt control_source))) ())
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
    fun has_markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun has_any_entity pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso has_position properties pos)
        markup
    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size structural_text then rev positions
          else
            (case try (find_from structural_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position structural_text structural_start
                       needle raw
                 in collect (raw + size needle) (position :: positions) end
             | NONE => rev positions)
      in collect 0 [] end

    val _ =
      List.app
        (fn head_pos =>
          (audit_assert "struct head lost function-role notation markup"
             (has_entity_markup
               Micro_Rust_Names.notationN head_pos);
           audit_assert "struct head lost registered-call styling"
             (has_markup Markup.keyword3N head_pos)))
        [outer_head_pos, nested_head_pos]
    val _ =
      (audit_assert
         "grouped control-head struct lost function-role notation markup"
         (has_entity_markup
           Micro_Rust_Names.notationN control_head_pos);
       audit_assert
         "grouped control-head struct lost registered-call styling"
         (has_markup Markup.keyword3N control_head_pos);
       audit_assert "grouped control-head label retained free-variable markup"
         (not (has_markup Markup.freeN control_label_pos));
       audit_assert "grouped control-head label lost typing markup"
         (has_markup Markup.typingN control_label_pos);
       audit_assert "grouped control-head label received entity markup"
         (not (has_any_entity control_label_pos));
       audit_assert "grouped control-head opening parenthesis lost markup"
         (has_markup Markup.delimiterN control_group_left_pos);
       audit_assert "grouped control-head closing parenthesis lost markup"
         (has_markup Markup.delimiterN control_group_right_pos))
    val _ =
      List.app
        (fn (label, pos) =>
          (audit_assert
             ("label " ^ quote label ^
               " retained free-variable markup")
             (not (has_markup Markup.freeN pos));
           audit_assert
             ("label " ^ quote label ^ " lost typing markup")
             (has_markup Markup.typingN pos);
           audit_assert
             ("label " ^ quote label ^ " received entity/selector markup")
             (not (has_any_entity pos));
           audit_assert
             ("label " ^ quote label ^ " received call styling")
             (not (has_markup Markup.keyword3N pos))))
        [("alpha", alpha_pos), ("beta", beta_pos),
         ("gamma", gamma_pos), ("delta", delta_pos)]
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                ("delimiter " ^ quote spelling ^ " lost markup")
                (has_markup Markup.delimiterN position))
            (all_token_positions spelling))
        ["{", "}", ":", ","]
    val (_, comment_pos) =
      token_position structural_text structural_start
        "// retained comment" 0
    val _ =
      audit_assert "line comment lost comment markup"
        (has_markup Markup.comment1N comment_pos)
    val _ =
      List.app
        (fn position =>
          audit_assert "value-antiquotation opener lost delimiter markup"
            (has_markup Markup.delimiterN position))
        (all_token_positions "\<llangle>")
    val _ =
      List.app
        (fn (marker, position) =>
          audit_assert
            ("value-antiquotation body " ^ quote marker ^
              " lost constant entity markup")
            (has_entity_markup Markup.constantN position))
        [("d21_audit_marker_a", marker_a_pos),
         ("d21_audit_marker_b", marker_b_pos),
         ("d21_audit_marker_c", marker_c_pos)]

    val valid_struct =
      "D21AuditPair { first: \<llangle>d21_audit_marker_a\<rrangle>, " ^
      "second: \<llangle>d21_audit_marker_b\<rrangle> }"
    val ordinary_follower = "if d21_audit_truth { () }"
    val ordinary_arm_follower =
      "match d21_audit_truth { _ \<Rightarrow> () }"

    fun expect_failure operation source =
      (case Exn.result operation source of
         Exn.Res _ =>
           error
             ("struct-expression regression audit: expected rejection of " ^
               quote source)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())

    fun assert_recovered () =
      let
        val _ = ignore (checked valid_struct)
        val _ =
          (case parse_text ordinary_follower of
             UE_If
               (UE_Path path, UE_Block (UE_Unit _, _), NONE, _) =>
               audit_assert "ordinary block-followed path changed after failure"
                 (render_path path = "d21_audit_truth")
           | _ =>
               error
                 "struct-expression regression audit: ordinary block follower did not recover")
        val _ =
          (case parse_text ordinary_arm_follower of
             UE_Match (MF_Auto, UE_Path path, _, _) =>
               audit_assert "ordinary match-followed path changed after failure"
                 (render_path path = "d21_audit_truth")
           | _ =>
               error
                 "struct-expression regression audit: ordinary arm follower did not recover")
      in () end

    val _ =
      (expect_failure parse_text
         "if D21AuditOne { value: true } { () }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: $, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: 1, second: }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: \<llangle>1, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure checked
         "D21AuditPair { first: 0 = rhs, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure checked
         ("D21AuditPair { " ^
          "f00: 0, f01: 1, f02: 2, f03: 3, f04: 4, " ^
          "f05: 5, f06: 6, f07: 7, f08: 8, f09: 9, " ^
          "f10: 10, f11: 11, f12: 12, f13: 13, f14: 14 }");
       assert_recovered ())
  in
    val _ =
      writeln
        "Struct-expression AST, lowering, parity, markup, and recovery regressions passed"
  end
\<close>


section\<open> Structural call-arity preflight audit \<close>

consts
  arity_audit_marker_00 :: nat
  arity_audit_marker_01 :: nat
  arity_audit_marker_02 :: nat
  arity_audit_marker_03 :: nat
  arity_audit_marker_04 :: nat
  arity_audit_marker_05 :: nat
  arity_audit_marker_06 :: nat
  arity_audit_marker_07 :: nat
  arity_audit_marker_08 :: nat
  arity_audit_marker_09 :: nat
  arity_audit_marker_10 :: nat
  arity_audit_marker_11 :: nat
  arity_audit_marker_12 :: nat
  arity_audit_marker_13 :: nat

definition arity_audit_backend14 ::
  \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body
  \<close>
  where
    \<open>
      arity_audit_backend14 \<equiv>
        lift_fun14 (\<lambda>a b c d e f g h i j k l m n. a)
    \<close>

definition arity_audit_registered_value :: nat
  where \<open> arity_audit_registered_value = 0 \<close>

micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Call14")
micro_rust_notation (call) arity_audit_backend14 ("arity_audit_method14")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Struct14")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Over")
micro_rust_notation (call) arity_audit_backend14 ("arity_audit_over_method")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::StructOver")
micro_rust_notation (literal) arity_audit_registered_value ("ArityAudit::Value")

text\<open>
The shallow-term layer owns the single \<open>funcall0\<close>-through-\<open>funcall14\<close> table. Translation
preflights the AST's total runtime arity before resolving a callee, applying generic arguments,
parsing embedded HOL, reporting struct labels, or lowering a receiver, argument, or initializer.
The ordinary call constructor still checks the same private table defensively.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("structural call-arity preflight audit: " ^ message)

    fun comma arguments = space_implode ", " arguments
    fun integers first count =
      map string_of_int (first upto (first + count - 1))
    fun call head arguments =
      head ^ "(" ^ comma arguments ^ ")"
    fun method receiver head arguments =
      receiver ^ "." ^ head ^ "(" ^ comma arguments ^ ")"

    val marker_sources =
      ["arity_audit_marker_00", "arity_audit_marker_01",
       "arity_audit_marker_02", "arity_audit_marker_03",
       "arity_audit_marker_04", "arity_audit_marker_05",
       "arity_audit_marker_06", "arity_audit_marker_07",
       "arity_audit_marker_08", "arity_audit_marker_09",
       "arity_audit_marker_10", "arity_audit_marker_11",
       "arity_audit_marker_12", "arity_audit_marker_13"]
    val marker_constants =
      [\<^const_name>\<open>arity_audit_marker_00\<close>,
       \<^const_name>\<open>arity_audit_marker_01\<close>,
       \<^const_name>\<open>arity_audit_marker_02\<close>,
       \<^const_name>\<open>arity_audit_marker_03\<close>,
       \<^const_name>\<open>arity_audit_marker_04\<close>,
       \<^const_name>\<open>arity_audit_marker_05\<close>,
       \<^const_name>\<open>arity_audit_marker_06\<close>,
       \<^const_name>\<open>arity_audit_marker_07\<close>,
       \<^const_name>\<open>arity_audit_marker_08\<close>,
       \<^const_name>\<open>arity_audit_marker_09\<close>,
       \<^const_name>\<open>arity_audit_marker_10\<close>,
       \<^const_name>\<open>arity_audit_marker_11\<close>,
       \<^const_name>\<open>arity_audit_marker_12\<close>,
       \<^const_name>\<open>arity_audit_marker_13\<close>]

    fun checked elaboration_ctxt text =
      Parser_Test_Elaboration.expression elaboration_ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun marker_sequence term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if member (op =) marker_constants name
              then fn names => names @ [name]
              else I
          | _ => I)
        term []

    val valid_direct =
      call "ArityAudit::Call14" marker_sources
    val valid_method =
      method (hd marker_sources) "arity_audit_method14"
        (tl marker_sources)
    val valid_struct =
      "ArityAudit::Struct14 { " ^
      comma
        (map_index
          (fn (index, marker) =>
            "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
            ": " ^ marker)
          marker_sources) ^
      " }"

    fun check_supported_boundary label text =
      let
        val term = checked ctxt text
      in
        audit_assert (label ^ " selected the backend more than once")
          (count_constant
            \<^const_name>\<open>arity_audit_backend14\<close> term = 1);
        audit_assert (label ^ " changed source order or single evaluation")
          (marker_sequence term = marker_constants)
      end

    fun recovery () =
      (check_supported_boundary "direct arity-14 recovery" valid_direct;
       check_supported_boundary "method total-14 recovery" valid_method;
       check_supported_boundary "struct arity-14 recovery" valid_struct;
       ignore (checked ctxt "()"))

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("structural call-arity preflight audit: missing " ^ quote needle)
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
           (token_start, Position.symbol_explode needle token_start))
      end

    fun complete_position text start =
      Position.range_position
        (start, Position.symbol_explode text start)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

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

    fun has_entity markup kind identity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            Properties.get properties Markup.nameN = SOME identity andalso
            has_position properties position)
        markup

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun arity_message arity position =
      "urust_expr: unsupported call arity " ^ string_of_int arity ^
      " (max 14; the frontend's surface lowering caps here)" ^
      Position.here position

    fun capture_expression elaboration_ctxt source =
      let
        val captured =
          Synchronized.var "structural_call_arity_reports" ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        Parser_Test_Elaboration.expression
                          elaboration_ctxt source) ()) ())
              ())
      in
        (result,
         fold collect_markup
           (maps YXML.parse_body (Synchronized.value captured)) [])
      end

    fun expect_rejection elaboration_ctxt serial label text arity inspect =
      let
        val start =
          Position.make0 (130 + serial) (9000 + serial * 500) 0 "" ""
            ("structural-call-arity-" ^ label ^ "-audit")
        val position = complete_position text start
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (result, markup) =
          capture_expression elaboration_ctxt source
        val body =
          (case result of
             Exn.Res term =>
               error
                 (label ^ " unexpectedly elaborated to " ^
                   Syntax.string_of_term elaboration_ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = arity_message arity position);
                   YXML.parse_body actual
                 end)
        val expected_range =
          [(Value.print_int (the (Position.offset_of position)),
            Value.print_int (the (Position.end_offset_of position)))]
        val _ =
          audit_assert (label ^ " diagnostic range changed")
            (diagnostic_ranges body = expected_range)
        val _ = inspect text start markup
        val _ = recovery ()
      in () end

    fun no_inspection _ _ _ = ()

    fun assert_no_notation label key position markup =
      (audit_assert (label ^ " resolved notation before arity rejection")
         (not
           (has_entity markup Micro_Rust_Names.notationN key position));
       audit_assert (label ^ " emitted registered-call styling before rejection")
         (not (has_markup markup Markup.keyword3N position)))

    fun inspect_direct text start markup =
      let
        val (head_offset, _) =
          token_position text start "ArityAudit::Over" 0
        val (_, head_position) =
          token_position text start "Over"
            (head_offset + size "ArityAudit::")
        val (value_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, value_position) =
          token_position text start "Value"
            (value_offset + size "ArityAudit::")
      in
        assert_no_notation "direct head" "ArityAudit::Over"
          head_position markup;
        assert_no_notation "direct argument" "ArityAudit::Value"
          value_position markup
      end

    fun inspect_method text start markup =
      let
        val (receiver_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, receiver_position) =
          token_position text start "Value"
            (receiver_offset + size "ArityAudit::")
        val (_, method_position) =
          token_position text start "arity_audit_over_method" 0
      in
        assert_no_notation "method receiver" "ArityAudit::Value"
          receiver_position markup;
        assert_no_notation "method head" "arity_audit_over_method"
          method_position markup
      end

    fun inspect_struct text start markup =
      let
        val (head_offset, _) =
          token_position text start "ArityAudit::StructOver" 0
        val (_, head_position) =
          token_position text start "StructOver"
            (head_offset + size "ArityAudit::")
        val (_, label_position) =
          token_position text start "f00" 0
        val (value_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, value_position) =
          token_position text start "Value"
            (value_offset + size "ArityAudit::")
      in
        assert_no_notation "struct head" "ArityAudit::StructOver"
          head_position markup;
        assert_no_notation "struct initializer" "ArityAudit::Value"
          value_position markup;
        audit_assert "struct label was semantically reported before arity rejection"
          (not (has_markup markup Markup.freeN label_position))
      end

    val fifteen = integers 0 15
    val method_fifteen = integers 1 14
    val method_sixteen = integers 1 15
    val (fixed_names, fixed_ctxt) =
      Variable.add_fixes
        ["arity_audit_fixed", "arity_audit_fixed_method"] ctxt
    val (fixed_head, fixed_method) =
      (case fixed_names of
         [head, method_name] => (head, method_name)
       | _ => error "structural call-arity preflight audit: fixed-name allocation changed")

    val direct_report_text =
      call "ArityAudit::Over"
        ("ArityAudit::Value" :: integers 1 14)
    val method_report_text =
      method "ArityAudit::Value" "arity_audit_over_method"
        method_fifteen
    val struct_report_text =
      "ArityAudit::StructOver { " ^
      comma
        ("f00: ArityAudit::Value" ::
          map
            (fn index =>
              "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
              ": " ^ string_of_int index)
            (1 upto 14)) ^
      " }"

    val _ =
      expect_rejection ctxt 0 "direct-registered-reports"
        direct_report_text 15 inspect_direct
    val _ =
      expect_rejection ctxt 1 "direct-unregistered"
        (call "arity_audit_missing_direct" fifteen) 15 no_inspection
    val _ =
      expect_rejection fixed_ctxt 2 "direct-fixed"
        (call fixed_head fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 3 "direct-shallow"
        (call "cf1" fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 4 "direct-pure"
        (call "Suc" fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 5 "direct-antiquotation"
        (call "\<epsilon>\<open>arity_audit_missing_antiquotation\<close>" fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 6 "direct-function-literal"
        (call
          "\<llangle>arity_audit_missing_function_literal\<rrangle>\<^sub>1::<arity_audit_missing_generic>"
          fifteen)
        15 no_inspection

    val _ =
      expect_rejection ctxt 7 "method-registered-reports"
        method_report_text 15 inspect_method
    val _ =
      expect_rejection ctxt 8 "method-registered-16"
        (method "0" "arity_audit_over_method" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 9 "method-unregistered-15"
        (method "0" "arity_audit_missing_method" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 10 "method-unregistered-16"
        (method "0" "arity_audit_missing_method" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection fixed_ctxt 11 "method-fixed-15"
        (method "0" fixed_method method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection fixed_ctxt 12 "method-fixed-16"
        (method "0" fixed_method method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 13 "method-shallow-15"
        (method "0" "cf1" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 14 "method-shallow-16"
        (method "0" "cf1" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 15 "method-pure-15"
        (method "0" "Suc" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 16 "method-pure-16"
        (method "0" "Suc" method_sixteen)
        16 no_inspection

    val _ =
      expect_rejection ctxt 17 "struct-reports"
        struct_report_text 15 inspect_struct
    val _ =
      expect_rejection ctxt 18 "callee-and-argument-precedence"
        (call "Suc"
          ("unknown_arity_argument!()" :: integers 1 14))
        15 no_inspection
    val _ =
      expect_rejection ctxt 19 "receiver-and-method-precedence"
        (method "unknown_arity_receiver!()" "arity_audit_missing_method"
          ("unknown_arity_argument!()" :: integers 2 13))
        15 no_inspection
    val _ =
      expect_rejection ctxt 20 "struct-head-and-initializer-precedence"
        ("UnknownArityStruct { " ^
         comma
           ("f00: unknown_arity_initializer!()" ::
             map
               (fn index =>
                 "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
                 ": " ^ string_of_int index)
               (1 upto 14)) ^
         " }")
        15 no_inspection

    val _ =
      URust_Shallow_Terms.check_function_call_arity Position.none 14
    val _ =
      (case Exn.result
          (fn () =>
            URust_Shallow_Terms.function_call Position.none HOLogic.unit
              (replicate 15 HOLogic.unit)) () of
         Exn.Res _ =>
           error "structural call-arity preflight audit: defensive function_call accepted arity 15"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "defensive function_call diagnostic changed"
               (Runtime.exn_message exn =
                 arity_message 15 Position.none))
  in
    val _ =
      writeln
        "Structural call-arity preflight, precedence, reports, ranges, recovery, order, and single-evaluation regressions passed"
  end
\<close>


chapter\<open>Logging\<close>

declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]


text\<open>
This suite is evaluated after \<open>Parser_Expression_Tests\<close>, so the logging import does not affect that theory's built-in macro coverage.
The parser-test logging fixture imports \<open>StdLib_Logging\<close>, which registers
the syntax used by \<open>l\<llangle>...\<rrangle>\<close> together with
\<open>fatal!\<close>, \<open>info!\<close>, and the other logger calls. In particular, registered
\<open>fatal!\<close> takes precedence over the built-in macro in this context.
Keeping the import isolated preserves the main suite's built-in \<open>fatal!\<close>
coverage.
\<close>

section\<open> Logging-data expressions \<close>

urust_expr log_data_one_string
  \<open> l\<llangle>"one"\<rrangle> \<close>

context
  fixes context_value :: nat
begin

urust_expr log_data_one_identifier
  \<open> l\<llangle>context_value\<rrangle> \<close>

urust_expr log_data_mixed
  \<open> l\<llangle>"value = ", context_value, "."\<rrangle> \<close>

urust_expr log_data_repeated_identifier
  \<open> l\<llangle>context_value, context_value, context_value\<rrangle> \<close>

end

urust_expr log_data_long
  \<open>
    l\<llangle>
      "a", True, "b", False, "c", True,
      "d", False, "e", True, "f", False
    \<rrangle>
  \<close>

urust_expr log_data_empty_string
  \<open> l\<llangle>""\<rrangle> \<close>

urust_expr log_data_multiline
  \<open>
    l\<llangle>
      "first",
      True,
      "second",
      False
    \<rrangle>
  \<close>

subsection\<open> String-token boundaries \<close>

urust_expr log_data_escaped_quote
  \<open> l\<llangle>"say: \"hello\""\<rrangle> \<close>

urust_expr log_data_escaped_backslash
  \<open> l\<llangle>"left\\right"\<rrangle> \<close>

urust_expr log_data_comma_in_string
  \<open> l\<llangle>"left, right"\<rrangle> \<close>

urust_expr log_data_comment_text
  \<open> l\<llangle>"https://example.invalid//path"\<rrangle> \<close>

urust_expr log_data_keyword_text
  \<open> l\<llangle>"true false let const return log yield l"\<rrangle> \<close>

subsection\<open> Identifier resolution and lexical scope \<close>

definition logging_collision :: nat
  where \<open> logging_collision = 17 \<close>

definition logging_notation_target :: nat
  where \<open> logging_notation_target = 99 \<close>

micro_rust_notation (literal) logging_notation_target ("logging_collision")

urust_expr log_data_hol_constant
  \<open> l\<llangle>logging_collision\<rrangle> \<close>

urust_expr log_data_boolean_constant
  \<open> l\<llangle>True, False\<rrangle> \<close>

urust_expr log_data_local
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    l\<llangle>"value = ", value\<rrangle>
  \<close>

urust_expr log_data_nested_shadowing
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    let outer = l\<llangle>value\<rrangle>;
    let value = \<llangle>7 :: nat\<rrangle>;
    (outer, l\<llangle>value\<rrangle>)
  \<close>

urust_expr log_data_constant_named_binder
  \<open>
    let Some = \<llangle>11 :: nat\<rrangle>;
    l\<llangle>Some, Some\<rrangle>
  \<close>

subsection\<open> Registered logging calls \<close>

urust_expr registered_fatal_logger
  \<open> fatal!(l\<llangle>"fatal", True\<rrangle>) \<close>

urust_expr registered_info_logger
  \<open> info!(l\<llangle>"info", True\<rrangle>) \<close>

urust_expr registered_error_logger
  \<open> error!(l\<llangle>"error", True\<rrangle>) \<close>

urust_expr registered_debug_logger
  \<open> debug!(l\<llangle>"debug", False\<rrangle>) \<close>

urust_expr registered_trace_logger
  \<open> trace!(l\<llangle>"trace", True\<rrangle>) \<close>

text\<open>
The first row specifically checks that the adjacent registered \<open>fatal!\<close> call wins over the
built-in message macro in this import context. The expression suite does not import
\<open>StdLib_Logging\<close>, so its built-in \<open>fatal!\<close> coverage remains unchanged.
\<close>


chapter\<open>Yield and logging audits\<close>

declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]

section\<open> Yield and logging structural audit \<close>

text\<open>
This theory audits the yield, primitive-log, and log-data ASTs and source spans;
exact lowering shape; local-first identifier resolution; editor markup;
positioned diagnostics; and lexer/parser recovery after malformed input.
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
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "yield/logging regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
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
         UE_Yield layout =>
           audit_assert "yield AST span changed"
             (same_range (source_span layout) yield_span)
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
         UE_Log (priority, data, layout) =>
           (audit_assert "primitive-log priority source changed"
              (Symbol.trim_blanks
                (Input.string_of
                  (value_antiquotation_source priority)) =
                "Error");
            audit_assert "primitive-log data source changed"
              (Symbol.trim_blanks
                (Input.string_of
                  (value_antiquotation_source data)) =
                "[LogNat 1]");
            audit_assert "primitive-log span changed"
              (Position.offset_of (source_span layout) =
                 Position.offset_of primitive_start andalso
               Position.end_offset_of (source_span layout) =
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
    val (string_raw, string_pos, identifier_pos, data_layout) =
      (case parse data_source of
         UE_LogData
           ([LDE_String (raw, first_pos),
             LDE_Identifier ("True", second_pos)],
            layout) =>
           (raw, first_pos, second_pos, layout)
       | _ => error "yield/logging regression audit: log-data AST changed")
    val data_pos = source_span data_layout
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
    val (identifier_raw, expected_identifier_pos) =
      token_position data_text data_start "True" 0
    val (name_raw, expected_name_pos) =
      token_position data_text data_start "l" 0
    val (open_raw, expected_open_pos) =
      token_position data_text data_start "\<llangle>" (name_raw + 1)
    val (_, expected_close_pos) =
      token_position data_text data_start "\<rrangle>"
        (identifier_raw + size "True")
    val _ =
      audit_assert "log-data entry spans changed"
        (same_range string_pos expected_string_pos andalso
         same_range identifier_pos expected_identifier_pos)
    val _ =
      audit_assert "log-data control-token spans changed"
        (same_range
           (the_source_token_position
             data_layout (Keyword_Token "l"))
           expected_name_pos andalso
         same_range
           (the_source_token_position
             data_layout (Delimiter_Token "log-data-open"))
           expected_open_pos andalso
         same_range
           (the_source_token_position
             data_layout (Delimiter_Token "log-data-close"))
           expected_close_pos)

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
                  (Parser_Test_Elaboration.expression ctxt markup_source)) ())
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
           audit_assert (label ^ " received a binding entity")
             (not (has_entity_markup "urust_var" pos))))
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


chapter\<open>Comments\<close>

declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]

section\<open> Nested Rust block comments \<close>

text\<open>
The ordinary lexer owns nested \<open>/* ... */\<close> layout and reports exactly the complete outer span.
The audit uses positioned escaped symbols and physical Unicode to pin symbol-aware ranges, while also
checking AST and checked-term transparency, literal-state boundaries, EOF behavior, diagnostics, and
state recovery.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("block-comment regression audit: " ^ message)

    fun parse_option source =
      URust_Parser.parse_source ctxt source

    fun parse_source source =
      (case parse_option source of
         SOME expression => expression
       | NONE => error "block-comment regression audit: empty parse")

    fun parse_text text =
      parse_source (Parser_Lex_Util.text_source text)

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked text =
      checked_source (Parser_Lex_Util.text_source text)

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("block-comment regression audit: missing " ^ quote needle)
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
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body
            ((markup, XML.content_of body) :: result)

    fun capture_reports action =
      let
        val captured =
          Synchronized.var
            "block_comment_parser_test_reports" ([] : string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
      in (result, markup) end

    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)

    fun has_markup markup markup_name pos =
      exists
        (fn ((name, properties), _) =>
          name = markup_name andalso has_position properties pos)
        markup

    fun count_markup markup markup_name pos =
      length
        (filter
          (fn ((name, properties), _) =>
            name = markup_name andalso has_position properties pos)
          markup)

    fun has_typing markup label pos =
      exists
        (fn ((name, properties), body) =>
          name = Markup.typingN andalso
            has_position properties pos andalso body = label)
        markup

    val physical_lambda =
      Byte.bytesToString
        (Word8Vector.fromList [0wxCE, 0wxBB])
    val block_comment =
      "/* outer physical " ^ physical_lambda ^
      "; escaped \<alpha> \<Rightarrow>; operators + - * / //; " ^
      "keyword let; numeral 7; delimiters { [ ( , ; ; " ^
      "quote \"paired /* marker */ text\"; " ^
      Symbol.comment ^ " " ^ Symbol.open_ ^
      "formal-shaped /* marker */ text" ^ Symbol.close ^
      "; /* nested /* deeply nested */ + */ end */"
    val structural_text =
      "1_u64" ^ block_comment ^ "+2_u64"
    val structural_start =
      Position.make0 41 400 0 "" "" "block-comment-structure"
    val structural_source =
      Parser_Lex_Util.positioned_content_source
        structural_text structural_start

    val (left_raw, left_pos) =
      token_position structural_text structural_start "1_u64" 0
    val (comment_raw, comment_pos) =
      token_position structural_text structural_start block_comment left_raw
    val (inner_plus_raw, inner_plus_pos) =
      token_position structural_text structural_start "+" comment_raw
    val (_, inner_keyword_pos) =
      token_position structural_text structural_start "let" comment_raw
    val (_, inner_numeral_pos) =
      token_position structural_text structural_start "7" comment_raw
    val (_, inner_delimiter_pos) =
      token_position structural_text structural_start "{" comment_raw
    val (outer_plus_raw, outer_plus_pos) =
      token_position structural_text structural_start "+"
        (comment_raw + size block_comment)
    val (_, right_pos) =
      token_position structural_text structural_start "2_u64"
        outer_plus_raw

    val _ =
      (case parse_source structural_source of
         UE_Bin
           (Add,
            UE_Literal (LP_Integer first_integer),
            UE_Literal (LP_Integer second_integer),
            operator_layout) =>
           (audit_assert "comment changed a neighboring literal range"
              (same_range
                 (integer_literal_position first_integer) left_pos andalso
               same_range
                 (integer_literal_position second_integer) right_pos);
            audit_assert "comment changed a neighboring literal spelling"
              (integer_literal_lexeme first_integer = "1_u64" andalso
               integer_literal_lexeme second_integer = "2_u64");
            audit_assert "operator range moved across the comment"
              (same_range
                (the_source_token_position
                  operator_layout Operator_Token)
                outer_plus_pos))
       | _ =>
           error "block-comment regression audit: expression AST changed")

    val comment_free_term = checked "1_u64 + 2_u64"
    val commented_term = checked_source structural_source
    val _ =
      audit_assert "comment changed the checked term"
        (Term.aconv
          (Term_Position.strip_positions comment_free_term,
           Term_Position.strip_positions commented_term))

    val (_, parser_markup) =
      capture_reports
        (fn () => ignore (checked_source structural_source))
    val _ =
      (audit_assert "outer comment lost full-span comment markup"
         (count_markup parser_markup Markup.comment1N comment_pos = 1);
       audit_assert "outer comment lost its typing label"
         (has_typing parser_markup "block comment" comment_pos);
       audit_assert "left numeral lost markup"
         (has_markup parser_markup Markup.numeralN left_pos);
       audit_assert "operator after comment lost markup"
         (has_markup parser_markup Markup.operatorN outer_plus_pos);
       audit_assert "right numeral lost markup"
         (has_markup parser_markup Markup.numeralN right_pos);
       audit_assert "comment body received operator markup"
         (not (has_markup parser_markup Markup.operatorN inner_plus_pos));
       audit_assert "comment body received keyword markup"
         (not (has_markup parser_markup Markup.keyword1N inner_keyword_pos));
       audit_assert "comment body received numeral markup"
         (not (has_markup parser_markup Markup.numeralN inner_numeral_pos));
       audit_assert "comment body received delimiter markup"
         (not (has_markup parser_markup Markup.delimiterN inner_delimiter_pos)))

    val string_text = "\"literal /* string */ text\""
    val value_aq_text = "\<llangle>''/* value */''\<rrangle>"
    val expression_aq_text =
      "\<epsilon>\<open>\<up>(''/* expression */'')\<close>"
    val _ =
      (case parse_text string_text of
         UE_Literal (LP_String (raw, _)) =>
           audit_assert "block-comment-shaped string text was consumed"
             (raw = string_text)
       | _ => error "block-comment regression audit: string AST changed")
    val _ =
      (case parse_text value_aq_text of
         UE_Literal (LP_ValAntiq antiquotation) =>
           audit_assert "value antiquotation block markers were consumed"
             (Input.string_of
               (value_antiquotation_source antiquotation) =
              "''/* value */''")
       | _ =>
           error "block-comment regression audit: value antiquotation AST changed")
    val _ =
      (case parse_text expression_aq_text of
         UE_ExprAntiq source =>
           audit_assert "expression antiquotation block markers were consumed"
             (Input.string_of source =
               "\<up>(''/* expression */'')")
       | _ =>
           error
             "block-comment regression audit: expression antiquotation AST changed")

    val _ =
      (case parse_option
          (Parser_Lex_Util.text_source block_comment) of
         NONE => ()
       | SOME _ =>
           error "block-comment regression audit: comment-only input was not empty")

    val _ =
      (case parse_text ("()" ^ block_comment) of
         UE_Unit _ => ()
       | _ =>
           error "block-comment regression audit: comment ending at EOF changed the AST")

    fun failure_message text start =
      (case Exn.result
          (fn () =>
            parse_source
              (Parser_Lex_Util.positioned_content_source text start)) () of
         Exn.Res _ =>
           error
             ("block-comment regression audit: malformed source parsed: " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else XML.content_of (YXML.parse_body (Runtime.exn_message exn)))

    fun recover () =
      (case parse_text "()" of
         UE_Unit _ => ()
       | _ =>
           error "block-comment regression audit: lexer state did not recover")

    fun expect_unterminated
        label text start expected_line =
      let
        val message = failure_message text start
        val _ =
          audit_assert (label ^ " diagnostic changed")
            (String.isSubstring "unterminated block comment" message)
        val _ =
          audit_assert (label ^ " diagnostic moved from the outer opener")
            (String.isSubstring
              ("line " ^ string_of_int expected_line) message)
        val _ = recover ()
      in () end

    val _ =
      expect_unterminated
        "outer"
        "\n/* outer"
        (Position.make0 100 1000 0 "" "" "block-comment-outer")
        101
    val _ =
      expect_unterminated
        "nested"
        "/* outer\n  /* nested */"
        (Position.make0 200 2000 0 "" "" "block-comment-nested")
        200
    val _ =
      expect_unterminated
        "short malformed"
        "/*/"
        (Position.make0 300 3000 0 "" "" "block-comment-short")
        300

    val unmatched_message =
      failure_message
        "1_u64 */ 2_u64"
        (Position.make0 400 4000 0 "" "" "block-comment-unmatched")
    val _ =
      (audit_assert "unmatched closer became a lexer error"
         (String.isSubstring "syntax error found at /" unmatched_message andalso
          not (String.isSubstring "unexpected input" unmatched_message));
       recover ())
  in
    val _ =
      writeln
        "Block-comment AST, term-shape, markup, diagnostics, and recovery regressions passed"
  end
\<close>


section\<open> Isabelle formal comments \<close>

text\<open>
Formal comments are layout for the dedicated parser. The lexer reports their complete source span
with Isabelle's inner-syntax comment style, while Isabelle's document machinery remains responsible
for checking document antiquotations inside the cartouche.
\<close>

subsection\<open> Expression and function parity \<close>

urust_expr isabelle_comment_standalone
  \<open>
    \<comment> \<open>Standalone comment before the expression, with literal block markers /* */.\<close>
    ()
  \<close>

urust_expr isabelle_comment_inline
  \<open>
    1_u64\<comment>\<open>Comment between operands: + - * / { } [ ] ( ) , ; :: =>.\<close>+2_u64
  \<close>

urust_expr isabelle_comment_trailing
  \<open>
    ();
    () \<comment> \<open>Trailing comment after the complete expression.\<close>
  \<close>

urust_expr isabelle_comment_multiline_nested
  \<open>
    \<comment> \<open>
      Outer document text with \<open>nested { grammar } punctuation\<close> and
      \<open>another \<open>deeply nested\<close> cartouche\<close>.
      Escaped Isabelle symbols remain document text: \<alpha> \<Rightarrow> \<forall>.
    \<close>
    if true {
      \<comment> \<open>Then branch.\<close>
      3_u64
    } else {
      4_u64
    }
  \<close>

urust_expr isabelle_comment_document_antiquotations
  \<open>
    \<comment> \<open>
      Modern controls: \<^term>\<open>True\<close>, \<^const>\<open>False\<close>, and
      \<^verbatim>\<open>{ grammar punctuation, :: => }\<close>.
      Legacy antiquotations: @{term True} and
      @{verbatim \<open>[legacy punctuation; + - *]\<close>}.
    \<close>
    ()
  \<close>

declare [[urust_verbosity = 2]]

urust_fn isabelle_comment_function ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    \<comment> \<open>Function-body comment with \<^term>\<open>item\<close> treated as document text.\<close>
    item \<comment> \<open>Inline function-body comment.\<close>
  \<close>

declare [[urust_verbosity = 2]]


subsection\<open> Specialized lexer contexts \<close>

definition isabelle_comment_generic ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>isabelle_comment_generic parameter \<equiv>
      lift_fun1 (\<lambda>argument. parameter + argument)\<close>

micro_rust_notation (call) isabelle_comment_generic ("Comment::generic")

urust_expr isabelle_comment_generic_layout
  \<open>
    Comment::generic::<
      1 \<comment> \<open>Generic-state layout with \<open>> , + ::\<close>.\<close> + 2
    >(3)
  \<close>

urust_expr isabelle_comment_log_data_layout
  \<open>
    l\<llangle>
      \<comment> \<open>Log-data layout before the first entry.\<close>
      "value = ",
      \<comment> \<open>Log-data layout after a separator.\<close>
      True
    \<rrangle>
  \<close>


subsection\<open> Literal comment-shaped text \<close>

text\<open>
The structural audit below feeds complete comment-shaped text directly to the lexer and verifies that
quoted strings and both uRust antiquotation states retain it byte-for-byte.
\<close>


subsection\<open> Structural, markup, diagnostic, and recovery audit \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Isabelle-comment regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "Isabelle-comment regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("Isabelle-comment regression audit: missing " ^ quote needle)
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
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_reports action =
      let
        val captured =
          Synchronized.var
            "isabelle_comment_parser_test_reports" ([] : string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
      in (result, markup) end

    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)

    fun has_markup markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup

    fun has_entity_markup markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup

    fun formal_comment body =
      Symbol.comment ^ " " ^ Symbol.open_ ^ body ^ Symbol.close

    val physical_lambda =
      Byte.bytesToString
        (Word8Vector.fromList [0wxCE, 0wxBB])
    val structural_comment =
      formal_comment
        ("physical Unicode " ^ physical_lambda ^
         "; dashes ---" ^
         "; nested " ^ Symbol.open_ ^ "{ [ ( + => :: ) ] }" ^
         Symbol.close ^ "; escaped \<alpha>")
    val structural_text =
      "1_u64 " ^ structural_comment ^
      " + 2_u64"
    val structural_start =
      Position.make0 41 400 0 "" "" "isabelle-comment-structure"
    val structural_source =
      Parser_Lex_Util.positioned_content_source
        structural_text structural_start
    val (left_raw, left_pos) =
      token_position structural_text structural_start "1_u64" 0
    val (comment_raw, comment_pos) =
      token_position structural_text structural_start structural_comment left_raw
    val (_, dash_pos) =
      token_position structural_text structural_start "---" comment_raw
    val (inner_plus_raw, inner_plus_pos) =
      token_position structural_text structural_start "+"
        comment_raw
    val (outer_plus_raw, outer_plus_pos) =
      token_position structural_text structural_start "+"
        (inner_plus_raw + 1)
    val (_, right_pos) =
      token_position structural_text structural_start "2_u64"
        outer_plus_raw

    val structural_ast = parse structural_source
    val _ =
      (case structural_ast of
         UE_Bin
           (Add,
            UE_Literal (LP_Integer first_integer),
            UE_Literal (LP_Integer second_integer),
            operator_layout) =>
           (audit_assert "comment created or changed an AST node"
              (same_range
                 (integer_literal_position first_integer) left_pos andalso
               same_range
                 (integer_literal_position second_integer) right_pos);
            audit_assert "comment changed an integer spelling"
              (integer_literal_lexeme first_integer = "1_u64" andalso
               integer_literal_lexeme second_integer = "2_u64");
            audit_assert "operator position moved across the comment"
              (same_range
                (the_source_token_position
                  operator_layout Operator_Token)
                outer_plus_pos))
       | _ =>
           error "Isabelle-comment regression audit: expression AST changed")

    val comment_free_term = checked "1_u64 + 2_u64"
    val commented_term =
      Parser_Test_Elaboration.expression ctxt structural_source
    val _ =
      audit_assert "formal comment changed the checked term"
        (Term.aconv
          (Term_Position.strip_positions comment_free_term,
           Term_Position.strip_positions commented_term))

    val (_, parser_markup) =
      capture_reports
        (fn () =>
          ignore
            (Parser_Test_Elaboration.expression ctxt structural_source))
    val _ =
      (audit_assert "formal comment lost full-span comment markup"
         (has_markup parser_markup Markup.comment1N comment_pos);
       audit_assert "formal comment lost full-span typing markup"
         (has_markup parser_markup Markup.typingN comment_pos);
       audit_assert "left numeral lost markup"
         (has_markup parser_markup Markup.numeralN left_pos);
       audit_assert "operator after comment lost markup"
         (has_markup parser_markup Markup.operatorN outer_plus_pos);
       audit_assert "right numeral lost markup"
         (has_markup parser_markup Markup.numeralN right_pos);
       audit_assert "comment dashes received uRust operator markup"
         (not (has_markup parser_markup Markup.operatorN dash_pos));
       audit_assert "comment content received uRust operator markup"
         (not (has_markup parser_markup Markup.operatorN inner_plus_pos)))

    val document_body =
      "Modern \<^term>\<open>True\<close> and " ^
      "\<^const>\<open>False\<close>; legacy @{term True}; " ^
      "\<^verbatim>\<open>modern text\<close>; " ^
      "@{verbatim \<open>legacy text\<close>}."
    val document_text =
      formal_comment document_body
    val document_start =
      Position.make0 61 600 0 "" "" "isabelle-comment-document"
    val document_source =
      Parser_Lex_Util.positioned_content_source
        document_text document_start
    val (body_raw, body_pos) =
      token_position document_text document_start
        (Symbol.open_ ^ "Modern") 0
    val body_stop =
      Position.symbol_explode
        (String.extract (document_text, body_raw, NONE))
        (Position.no_range_position body_pos)
    val full_body_pos =
      Position.range_position
        (Position.no_range_position body_pos, body_stop)
    val (modern_true_raw, modern_true_pos) =
      token_position document_text document_start "True" body_raw
    val (false_raw, false_pos) =
      token_position document_text document_start "False"
        modern_true_raw
    val (_, legacy_true_pos) =
      token_position document_text document_start "True" false_raw
    val (_, document_markup) =
      capture_reports
        (fn () =>
          Document_Output.check_comments ctxt
            (Input.source_explode document_source))
    val _ =
      (audit_assert "Isabelle checker did not mark the formal-comment cartouche"
         (has_markup document_markup Markup.cartoucheN full_body_pos);
       audit_assert "modern term antiquotation lost constant markup"
         (has_entity_markup document_markup Markup.constantN modern_true_pos);
       audit_assert "modern const antiquotation lost constant markup"
         (has_entity_markup document_markup Markup.constantN false_pos);
       audit_assert "legacy term antiquotation lost constant markup"
         (has_entity_markup document_markup Markup.constantN legacy_true_pos))

    val string_text =
      "\"" ^ formal_comment "string literal" ^ "\""
    val value_aq_text =
      "\<llangle>''" ^ formal_comment "value literal" ^ "''\<rrangle>"
    val expression_aq_text =
      "\<epsilon>\<open>literal (''" ^
      formal_comment "expression literal" ^
      "'')\<close>"
    val _ =
      (case parse_text string_text of
         UE_Literal (LP_String (raw, _)) =>
           audit_assert "comment-shaped string text was consumed"
             (raw = string_text)
       | _ =>
           error "Isabelle-comment regression audit: string AST changed")
    val _ =
      (case parse_text value_aq_text of
         UE_Literal (LP_ValAntiq antiquotation) =>
           audit_assert "comment-shaped value antiquotation text was consumed"
             (Input.string_of
                (value_antiquotation_source antiquotation) =
               "''" ^ formal_comment "value literal" ^ "''")
       | _ =>
           error
             "Isabelle-comment regression audit: value antiquotation AST changed")
    val _ =
      (case parse_text expression_aq_text of
         UE_ExprAntiq source =>
           audit_assert "comment-shaped expression antiquotation text was consumed"
             (Input.string_of source =
               "literal (''" ^ formal_comment "expression literal" ^ "'')")
       | _ =>
           error
             "Isabelle-comment regression audit: expression antiquotation AST changed")

    fun failure_message text start =
      (case Exn.result
          (fn () =>
            parse
              (Parser_Lex_Util.positioned_content_source text start)) () of
         Exn.Res _ =>
           error
             ("Isabelle-comment regression audit: malformed source parsed: " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else XML.content_of (YXML.parse_body (Runtime.exn_message exn)))

    fun recover_initial () =
      (case parse_text "()" of
         UE_Unit _ => ()
       | _ =>
           error "Isabelle-comment regression audit: initial state did not recover")

    fun recover_generic () =
      (case parse_text "Comment::generic::<1>(2)" of
         UE_Call _ => ()
       | _ =>
           error "Isabelle-comment regression audit: generic state did not recover")

    fun recover_log_data () =
      (case parse_text "l\<llangle>\"ok\", True\<rrangle>" of
         UE_LogData _ => ()
       | _ =>
           error "Isabelle-comment regression audit: log-data state did not recover")

    fun expect_positioned_failure
        label text start expected expected_line recover =
      let
        val message = failure_message text start
        val _ =
          audit_assert (label ^ " diagnostic changed")
            (String.isSubstring expected message)
        val _ =
          audit_assert (label ^ " diagnostic moved away from the comment opener")
            (String.isSubstring
              ("line " ^ string_of_int expected_line) message)
        val _ = recover ()
      in () end

    val _ =
      expect_positioned_failure
        "initial missing opener"
        ("\n" ^ Symbol.comment ^ " not-a-cartouche")
        (Position.make0 101 1000 0 "" ""
          "isabelle-comment-initial-missing")
        "opening cartouche expected after formal comment" 102
        recover_initial
    val _ =
      expect_positioned_failure
        "generic missing opener"
        ("Comment::generic::<\n  " ^
          Symbol.comment ^ " not-a-cartouche")
        (Position.make0 201 2000 0 "" ""
          "isabelle-comment-generic-missing")
        "opening cartouche expected after formal comment" 202
        recover_generic
    val _ =
      expect_positioned_failure
        "log-data missing opener"
        ("l\<llangle>\n  " ^ Symbol.comment ^ " not-a-cartouche")
        (Position.make0 301 3000 0 "" ""
          "isabelle-comment-log-missing")
        "opening cartouche expected after formal comment" 302
        recover_log_data
    val _ =
      expect_positioned_failure
        "initial unterminated cartouche"
        ("\n" ^ Symbol.comment ^ " " ^ Symbol.open_ ^
          "outer " ^ Symbol.open_ ^ "nested" ^ Symbol.close)
        (Position.make0 401 4000 0 "" ""
          "isabelle-comment-initial-unterminated")
        "unterminated formal comment" 402
        recover_initial
    val _ =
      expect_positioned_failure
        "generic unterminated cartouche"
        ("Comment::generic::<\n  " ^ Symbol.comment ^ " " ^
          Symbol.open_ ^ "outer " ^ Symbol.open_ ^ "nested" ^
          Symbol.close)
        (Position.make0 501 5000 0 "" ""
          "isabelle-comment-generic-unterminated")
        "unterminated formal comment" 502
        recover_generic
    val _ =
      expect_positioned_failure
        "log-data unterminated cartouche"
        ("l\<llangle>\n  " ^ Symbol.comment ^ " " ^ Symbol.open_ ^
          "outer " ^ Symbol.open_ ^ "nested" ^ Symbol.close)
        (Position.make0 601 6000 0 "" ""
          "isabelle-comment-log-unterminated")
        "unterminated formal comment" 602
        recover_log_data
  in
    val _ =
      writeln
        "Isabelle-comment AST, positions, markup, diagnostics, and recovery regressions passed"
  end
\<close>



section\<open>Array repeats\<close>

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]

definition repeat_global_length :: \<open>64 word\<close>
  where \<open>repeat_global_length = 4\<close>

definition repeat_small_length :: \<open>8 word\<close>
  where \<open>repeat_small_length = 3\<close>

definition repeat_wrong_length :: bool
  where \<open>repeat_wrong_length = True\<close>

definition repeat_registered_length :: \<open>64 word\<close>
  where \<open>repeat_registered_length = 3\<close>

micro_rust_notation (literal)
  repeat_registered_length ("RepeatFixture::Length")

locale repeat_contextual_lengths =
  fixes direct_context_length :: \<open>64 word\<close>
    and registered_context_length :: \<open>64 word\<close>
begin

micro_rust_notation (literal)
  registered_context_length ("RepeatFixture::ContextLength")

urust_expr repeat_direct_context_length
  \<open> [1; direct_context_length] \<close>

urust_expr repeat_registered_context_length
  \<open> [1; RepeatFixture::ContextLength] \<close>

end

subsection\<open>Accepted syntax and length arithmetic\<close>

urust_expr repeat_zero \<open> [1; 0] \<close>
urust_expr repeat_one \<open> [1; 1usize] \<close>
urust_expr repeat_many \<open> [1; 4] \<close>
urust_expr repeat_binary \<open> [1; 0b10] \<close>
urust_expr repeat_octal \<open> [1; 0o10] \<close>
urust_expr repeat_hex \<open> [1; 0x10] \<close>
urust_expr repeat_separators \<open> [1; 1_0usize] \<close>
urust_expr repeat_trailing_separator \<open> [1; 10_] \<close>
urust_expr repeat_compatibility_suffix_separator \<open> [1; 2_usize] \<close>
urust_expr repeat_cast_u8 \<open> [1; 3u8 as usize] \<close>
urust_expr repeat_cast_u16 \<open> [1; 3u16 as usize] \<close>
urust_expr repeat_cast_u32 \<open> [1; 3u32 as usize] \<close>
urust_expr repeat_cast_u64 \<open> [1; 3u64 as usize] \<close>
urust_expr repeat_cast_small_global
  \<open> [1; repeat_small_length as usize] \<close>
urust_expr repeat_global \<open> [1; repeat_global_length] \<close>
urust_expr repeat_registered \<open> [1; RepeatFixture::Length] \<close>
urust_expr repeat_add \<open> [1; 1 + 2] \<close>
urust_expr repeat_sub \<open> [1; 4 - 1] \<close>
urust_expr repeat_mul \<open> [1; 2 * 3] \<close>
urust_expr repeat_div \<open> [1; 8 / 2] \<close>
urust_expr repeat_mod \<open> [1; 7 % 4] \<close>
urust_expr repeat_precedence \<open> [1; 1 + 2 * 3] \<close>
urust_expr repeat_grouping \<open> [1; (1 + 2) * 3] \<close>
urust_expr repeat_nested \<open> [[1; 2]; 3] \<close>
urust_expr repeat_block_operand \<open> [{ 1 }; 2] \<close>
urust_expr repeat_call_operand \<open> [Some(1); 2] \<close>
urust_expr repeat_control_operand
  \<open> [if true { 1 } else { 2 }; 2] \<close>
urust_expr repeat_match_operand
  \<open>
    [match Some(1) {
       Some(value) \<Rightarrow> value,
       None \<Rightarrow> 0
     }; 2]
  \<close>
urust_expr repeat_macro_operand \<open> [vec![1, 2]; 2] \<close>
urust_expr repeat_inline_zero \<open> [const { 1 }; 0] \<close>
urust_expr repeat_inline_many \<open> [const { Some(1) }; 3] \<close>
urust_expr repeat_inline_empty_block \<open> [const {}; 2] \<close>
urust_expr repeat_inline_nested
  \<open> [const { [const { 1 }; 2] }; 3] \<close>
urust_expr repeat_inline_multistatement
  \<open> [const { let value = Some(1); value }; 2] \<close>

subsection\<open>Type behavior\<close>

urust_expr repeat_polymorphic_element ::
  \<open>(unit, nat option list, unit, unit, unit, unit) expression\<close>
  \<open> [None; 2] \<close>

urust_expr repeat_nested_inference ::
  \<open>(unit, nat list list, unit, unit, unit, unit) expression\<close>
  \<open> [[1; 2]; 3] \<close>

urust_expr repeat_inline_nested_inference ::
  \<open>(unit, nat option list list, unit, unit, unit, unit) expression\<close>
  \<open> [const { [None; 2] }; 3] \<close>

urust_expr_rejects
  \<open> [if true { 1 } else { false }; 2] \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects \<open> [1; repeat_small_length] \<close>
  \<open> Type unification failed \<close>

subsection\<open>Grammar and AST boundaries\<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "array repeat AST audit: empty parse")

    fun assert message condition =
      if condition then ()
      else error ("array repeat AST audit: " ^ message)

    fun integer expected (RL_Integer actual) =
          expected = integer_literal_lexeme actual
      | integer _ _ = false

    val _ =
      (case parse "[1; 2 + 3 * 4]" of
         UE_ArrayRepeat
           (AR_Ordinary,
            UE_Literal
              (LP_Integer (Integer_Literal ("1", _, _))),
            RL_Bin
              (Add, left,
               RL_Bin (Mul, middle, right, _), _), _) =>
             assert "operator precedence changed"
               (integer "2" left andalso
                integer "3" middle andalso
                integer "4" right)
       | _ => error "array repeat AST audit: ordinary repeat shape changed")

    val _ =
      (case parse "[const { 1 }; (2 + 3) as usize]" of
         UE_ArrayRepeat
           (AR_InlineConst, UE_Block _, RL_CastUsize (RL_Group _, _), _) => ()
       | _ => error "array repeat AST audit: inline-const repeat shape changed")

    val _ =
      (case parse "[]" of UE_Array ([], _) => ()
       | _ => error "array repeat AST audit: empty array shape changed")
    val _ =
      (case parse "[1, 2,]" of UE_Array ([_, _], _) => ()
       | _ => error "array repeat AST audit: list array shape changed")
    val _ =
      (case parse "(1, 2)" of UE_Tuple ([_, _], _) => ()
       | _ => error "array repeat AST audit: tuple shape changed")
    val _ =
      (case parse "&[1, 2]" of
         UE_Unary (U_Borrow BM_Imm, UE_Array ([_, _], _), _) => ()
       | _ => error "array repeat AST audit: direct array borrow shape changed")
    val _ =
      (case parse "items[0]" of UE_Index _ => ()
       | _ => error "array repeat AST audit: indexing shape changed")
    val _ =
      (case parse "items[1..2]" of
         UE_Index (_, UE_Range (RK_Exclusive, _, _, _), _) => ()
       | _ => error "array repeat AST audit: slice/index shape changed")
    val _ =
      (case parse "[1; 2][0]" of
         UE_Index (UE_ArrayRepeat _, _, _) => ()
       | _ => error "array repeat AST audit: repeat/index boundary changed")
  in
    val _ = writeln "Array repeat grammar and AST boundaries passed"
  end
\<close>

subsection\<open>Rejected repeat lengths and malformed syntax\<close>

urust_expr_rejects \<open> [; 2] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [1;] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [1; 2 \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [1;; 2] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [1; 2; 3] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [1; 2,] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [const 1; 2] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [const { 1; 2] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [const { 1 }, 2] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [const { 1 };] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [const { 1 }; 2,] \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [const { 1 }; 2; 3] \<close> \<open> syntax error \<close>

urust_expr_rejects \<open> [1; 2u8] \<close>
  \<open> requires an explicit `as usize` cast \<close>
urust_expr_rejects \<open> [1; 2u16] \<close>
  \<open> requires an explicit `as usize` cast \<close>
urust_expr_rejects \<open> [1; 2u32] \<close>
  \<open> requires an explicit `as usize` cast \<close>
urust_expr_rejects \<open> [1; 2u64] \<close>
  \<open> requires an explicit `as usize` cast \<close>
urust_expr_rejects \<open> [1; 2u128] \<close>
  \<open> unsupported integer-literal suffix "u128" \<close>
urust_expr_rejects \<open> [1; 2i32] \<close>
  \<open> unsupported integer-literal suffix "i32" \<close>
urust_expr_rejects \<open> [1; unresolved_repeat_length] \<close>
  \<open> does not resolve to a global constant \<close>
urust_expr_rejects
  \<open> [1; Parser_Syntax_Tests::repeat_global_length] \<close>
  \<open> qualified path "Parser_Syntax_Tests::repeat_global_length" requires an exact micro_rust_notation (literal) declaration \<close>
urust_expr_rejects \<open> [1; WrongRole::Value] \<close>
  \<open> qualified path "WrongRole::Value" requires an exact micro_rust_notation (literal) declaration \<close>
urust_expr_rejects \<open> [1; repeat_wrong_length] \<close>
  \<open> Type unification failed \<close>
urust_expr_rejects \<open> let count = 2; [1; count] \<close>
  \<open> cannot use lexical local \<close>
urust_expr_rejects \<open> [1; Some(2)] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; value.method()] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; value.field] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; values[0]] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; vec![2]] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; \<llangle>2 :: 64 word\<rrangle>] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; 1..2] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; slot = 2] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; |x| x] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; return 2] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; if true { 2 } else { 3 }] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; { 2 }] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; true] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; "two"] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; (1, 2)] \<close>
  \<open> array repeat length supports only \<close>
urust_expr_rejects \<open> [1; 2 as u32] \<close>
  \<open> array repeat length supports only \<close>

urust_expr repeat_recovery_after_rejections \<open> [7; 2] \<close>

subsection\<open>Lowering shape, compactness, and regressions\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("array repeat lowering audit: " ^ message)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "array repeat lowering audit: empty parse")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun atom_count term =
      Term.fold_aterms (fn _ => Integer.add 1) term 0

    val ordinary = checked "[1; 1_000_000]"
    val inline = checked "[const { 1 }; 1_000_000]"
    val symbolic = checked "[1; repeat_global_length]"
    val array = checked "[1, 2]"
    val borrowed_array = checked "&[1, 2]"
    val indexed_array =
      URust_Translate.mk_expression ctxt [] (parse "[1, 2][0]")
    val vector_macro = checked "vec![1, 2]"

    val _ =
      audit_assert "ordinary repeat lost its single List.replicate"
        (count_constant \<^const_name>\<open>List.replicate\<close>
          ordinary = 1)
    val _ =
      audit_assert "ordinary repeat no longer evaluates length and value through two binds"
        (count_constant \<^const_name>\<open>Core_Expression.bind\<close>
          ordinary = 2)
    val _ =
      audit_assert "ordinary large length expanded into list constructors"
        (count_constant \<^const_name>\<open>List.Cons\<close>
          ordinary = 0)
    val _ =
      audit_assert "ordinary large repeat term stopped being compact"
        (atom_count ordinary < 200)

    val _ =
      audit_assert "inline repeat lost its single List.replicate"
        (count_constant \<^const_name>\<open>List.replicate\<close>
          inline = 1)
    val _ =
      audit_assert "inline repeat lost list_sequence"
        (count_constant \<^const_name>\<open>list_sequence\<close>
          inline = 1)
    val _ =
      audit_assert "inline repeat should bind only its length"
        (count_constant \<^const_name>\<open>Core_Expression.bind\<close>
          inline = 1)
    val _ =
      audit_assert "inline large length expanded into list constructors"
        (count_constant \<^const_name>\<open>List.Cons\<close>
          inline = 0)
    val _ =
      audit_assert "inline large repeat term stopped being compact"
        (atom_count inline < 200)

    val _ =
      audit_assert "symbolic length lost the global constant"
        (count_constant
          \<^const_name>\<open>repeat_global_length\<close> symbolic = 1)
    val _ =
      audit_assert "symbolic length expanded during elaboration"
        (count_constant \<^const_name>\<open>List.replicate\<close>
          symbolic = 1 andalso
         count_constant \<^const_name>\<open>List.Cons\<close>
          symbolic = 0)

    val _ =
      audit_assert "ordinary array lowering acquired repeat machinery"
        (count_constant \<^const_name>\<open>List.replicate\<close>
          array = 0)
    val _ =
      audit_assert "ordinary array List.Cons shape changed"
        (count_constant \<^const_name>\<open>List.Cons\<close>
          array = 2)
    val _ =
      audit_assert "direct ordinary-array borrow erasure changed"
        (Term.aconv
          (Term_Position.strip_positions array,
           Term_Position.strip_positions borrowed_array))
    val _ =
      audit_assert "ordinary indexing lost its private projection recipe"
        (count_constant
          \<^const_name>\<open>urust_internal_index_projection\<close>
          indexed_array = 1)
    val _ =
      audit_assert "vec! lowering acquired repeat machinery"
        (count_constant \<^const_name>\<open>List.replicate\<close>
          vector_macro = 0)

    val _ =
      (case parse "[1; 2]" of UE_ArrayRepeat _ => ()
       | _ => error "array repeat lowering audit: parser recovery shape changed")
  in
    val _ =
      writeln
        "Array repeat lowering, compactness, and regression audits passed"
  end
\<close>

subsection\<open>Markup, positions, and recovery\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("array repeat PIDE audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("array repeat PIDE audit: missing " ^ quote needle)
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
           (token_start, Position.symbol_explode needle token_start))
      end

    fun all_token_positions text start needle =
      let
        fun collect offset positions =
          if offset + size needle > size text then rev positions
          else
            (case try (find_from text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position text start needle raw
                 in collect (raw + size needle) (position :: positions) end
             | NONE => rev positions)
      in collect 0 [] end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup_name position markup =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup

    fun has_entity kind identity position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            Properties.get properties Markup.nameN = SOME identity andalso
            has_position properties position)
        markup

    val markup_text =
      "[const { 1 }; " ^
      "(RepeatFixture::Length + repeat_global_length + " ^
      "(2u8 as usize))]"
    val markup_start =
      Position.make0 41 400 0 "" "" "array-repeat-markup-audit"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        markup_text markup_start
    val captured =
      Synchronized.var "array_repeat_markup_reports" ([]: string list)
    fun capture chunks =
      Synchronized.change captured (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression
                    ctxt markup_source)) ())
          ())
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured)) []

    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                ("delimiter " ^ quote spelling ^ " lost markup")
                (has_markup Markup.delimiterN position markup))
            (all_token_positions markup_text markup_start spelling))
        ["[", "]", "{", "}", ";", "(", ")", "::"]
    val _ =
      List.app
        (fn position =>
          audit_assert "length addition lost operator markup"
            (has_markup Markup.operatorN position markup))
        (all_token_positions markup_text markup_start "+")
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                ("numeral " ^ quote spelling ^ " lost markup")
                (has_markup Markup.numeralN position markup))
            (all_token_positions markup_text markup_start spelling))
        ["1", "2u8"]
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                ("keyword " ^ quote spelling ^ " lost markup")
                (has_markup Markup.keyword1N position markup))
            (all_token_positions markup_text markup_start spelling))
        ["const", "as", "usize"]

    val repeat_terminal =
      #2 (token_position markup_text markup_start "Length" 0)
    val global_terminal =
      #2 (token_position markup_text markup_start
        "repeat_global_length" 0)
    val _ =
      audit_assert "registered length lost notation navigation"
        (has_entity Micro_Rust_Names.notationN
          "RepeatFixture::Length" repeat_terminal markup)
    val _ =
      audit_assert "HOL global length lost constant navigation"
        (has_entity Markup.constantN
          \<^const_name>\<open>repeat_global_length\<close>
          global_terminal markup)

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun range_of position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun expect_positioned_failure serial label text needle expected =
      let
        val start =
          Position.make0 (70 + serial) (1000 + serial * 300) 0 "" ""
            ("array-repeat-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val position = #2 (token_position text start needle 0)
        val result =
          Exn.result
            (fn () =>
              Parser_Test_Elaboration.expression ctxt source) ()
        val message =
          (case result of
             Exn.Res term =>
               error
                 ("array repeat PIDE audit: " ^ label ^
                  " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else Runtime.exn_message exn)
        val _ =
          audit_assert (label ^ " diagnostic changed")
            (String.isSubstring expected message)
        val _ =
          audit_assert (label ^ " diagnostic range changed")
            (diagnostic_ranges (YXML.parse_body message) =
              [range_of position])
        val recovered = checked "[7; 2]"
        val _ =
          audit_assert (label ^ " did not recover")
            (Term.exists_subterm
              (fn Const (name, _) =>
                    name = \<^const_name>\<open>List.replicate\<close>
                | _ => false)
              recovered)
      in () end

    val _ =
      expect_positioned_failure 0 "suffix"
        "[1; 2u8]" "2u8"
        "requires an explicit `as usize` cast"
    val _ =
      expect_positioned_failure 1 "runtime-call"
        "[1; Some(2)]" "Some(2)"
        "array repeat length supports only"
    val _ =
      expect_positioned_failure 2 "symbol-offset"
        "[\<y>\<i>\<e>\<l>\<d>; missing_length]"
        "missing_length"
        "does not resolve to a global constant"
    val _ =
      expect_positioned_failure 3 "qualified-global"
        "[1; Parser_Syntax_Tests::repeat_global_length]"
        "Parser_Syntax_Tests::repeat_global_length"
        "requires an exact micro_rust_notation (literal) declaration"
  in
    val _ =
      writeln
        "Array repeat markup, navigation, positioned diagnostics, symbol offsets, and recovery passed"
  end
\<close>

subsection\<open>Evaluation count, order, and control propagation\<close>

definition repeat_tick ::
    \<open>(nat, nat, nat, unit, unit, unit) expression\<close>
  where
    \<open>
      repeat_tick =
        bind (get id) (\<lambda>current.
        bind (put Suc) (\<lambda>_.
          literal current))
    \<close>

lemma repeat_unat_word64_2 [simp]:
  \<open>unat (2 :: 64 word) = 2\<close>
  by eval

lemma repeat_unat_word64_3 [simp]:
  \<open>unat (3 :: 64 word) = 3\<close>
  by eval

lemma repeat_take_bit_word64_2 [simp]:
  \<open>take_bit LENGTH(64) (2 :: nat) = 2\<close>
  by (rule take_bit_nat_eq_self; simp)

lemma repeat_take_bit_word64_3 [simp]:
  \<open>take_bit LENGTH(64) (3 :: nat) = 3\<close>
  by (rule take_bit_nat_eq_self; simp)

lemma repeat_tick_evaluate [simp]:
  \<open>evaluate repeat_tick state = Success state (Suc state)\<close>
  by
    (simp add:
      repeat_tick_def bind_evaluate
      get_def put_def literal_def evaluate_def
      Core_Expression.bind.simps Let_def)

lemma repeat_tick_sequence_two [simp]:
  \<open>
    evaluate (list_sequence (replicate 2 repeat_tick)) state =
      Success [state, Suc state] (Suc (Suc state))
  \<close>
  by
    (simp add:
      list_sequence.simps repeat_tick_def bind_evaluate
      get_def put_def literal_def evaluate_def
      Core_Expression.bind.simps Let_def eval_nat_numeral)

lemma repeat_tick_sequence_three [simp]:
  \<open>
    evaluate (list_sequence (replicate 3 repeat_tick)) state =
      Success
        [state, Suc state, Suc (Suc state)]
        (Suc (Suc (Suc state)))
  \<close>
  by
    (simp add:
      list_sequence.simps repeat_tick_def bind_evaluate
      get_def put_def literal_def evaluate_def
      Core_Expression.bind.simps Let_def eval_nat_numeral)

lemma repeat_nested_tick_sequence [simp]:
  \<open>
    evaluate
      (list_sequence
        (replicate 3
          (list_sequence (replicate 2 repeat_tick)))) 0 =
      Success [[0, 1], [2, 3], [4, 5]] 6
  \<close>
  by
    (simp add:
      list_sequence.simps repeat_tick_def bind_evaluate
      get_def put_def literal_def evaluate_def
      Core_Expression.bind.simps Let_def eval_nat_numeral)

urust_expr repeat_ordinary_effect_zero ::
  \<open>(nat, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [\<epsilon>\<open> repeat_tick \<close>; 0] \<close>

urust_expr repeat_ordinary_effect_one ::
  \<open>(nat, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [\<epsilon>\<open> repeat_tick \<close>; 1] \<close>

urust_expr repeat_ordinary_effect_many ::
  \<open>(nat, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [\<epsilon>\<open> repeat_tick \<close>; 3] \<close>

urust_expr repeat_inline_effect_zero ::
  \<open>(nat, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [const { \<epsilon>\<open> repeat_tick \<close> }; 0] \<close>

urust_expr repeat_inline_effect_one ::
  \<open>(nat, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [const { \<epsilon>\<open> repeat_tick \<close> }; 1] \<close>

urust_expr repeat_inline_effect_many ::
  \<open>(nat, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [const { \<epsilon>\<open> repeat_tick \<close> }; 3] \<close>

urust_expr repeat_nested_inline_effects ::
  \<open>(nat, nat list list, nat, unit, unit, unit) expression\<close>
  \<open>
    [const {
      [const { \<epsilon>\<open> repeat_tick \<close> }; 2]
    }; 3]
  \<close>

lemma repeat_ordinary_effect_counts:
  \<open>
    evaluate repeat_ordinary_effect_zero 0 = Success [] 1 \<and>
    evaluate repeat_ordinary_effect_one 0 = Success [0] 1 \<and>
    evaluate repeat_ordinary_effect_many 0 = Success [0, 0, 0] 1
  \<close>
  by
    (simp add:
      repeat_ordinary_effect_zero_def
      repeat_ordinary_effect_one_def
      repeat_ordinary_effect_many_def
      repeat_tick_def
      evaluate_def get_def put_def literal_def
      Core_Expression.bind.simps;
      simp add: eval_nat_numeral)

lemma repeat_inline_effect_counts_and_order:
  \<open>
    evaluate repeat_inline_effect_zero 0 = Success [] 0 \<and>
    evaluate repeat_inline_effect_one 0 = Success [0] 1 \<and>
    evaluate repeat_inline_effect_many 0 = Success [0, 1, 2] 3 \<and>
    evaluate repeat_nested_inline_effects 0 =
      Success [[0, 1], [2, 3], [4, 5]] 6
  \<close>
  apply
    (simp add:
      repeat_inline_effect_zero_def
      repeat_inline_effect_one_def
      repeat_inline_effect_many_def
      repeat_nested_inline_effects_def)
  apply (simp add: eval_nat_numeral)
  apply (simp add: bind_evaluate literal_def)
  apply (simp add: evaluate_def Core_Expression.bind.simps)
  apply
    (simp add:
      list_sequence.simps repeat_tick_def bind_evaluate
      get_def put_def literal_def evaluate_def
      Core_Expression.bind.simps Let_def eval_nat_numeral)
  done

urust_expr repeat_length_failure_before_operand ::
  \<open>(nat, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [\<epsilon>\<open> repeat_tick \<close>; 1 / 0] \<close>

lemma repeat_length_failure_precedes_operand:
  \<open>
    evaluate repeat_length_failure_before_operand 0 =
      Abort (Panic (String.implode ''division by zero'')) 0
  \<close>
  by
    (simp add:
      repeat_length_failure_before_operand_def
      repeat_tick_def
      evaluate_def get_def put_def literal_def
      bind2_def word_udiv_def word_udiv_core_def abort_def
      Core_Expression.bind.simps)

urust_expr repeat_ordinary_return_zero ::
  \<open>(unit, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [return 7; 0] \<close>

urust_expr repeat_inline_return_zero ::
  \<open>(unit, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [const { return 7 }; 0] \<close>

urust_expr repeat_inline_return_one ::
  \<open>(unit, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [const { return 7 }; 1] \<close>

lemma repeat_return_propagation:
  \<open>
    evaluate repeat_ordinary_return_zero () = Return 7 () \<and>
    evaluate repeat_inline_return_zero () = Success [] () \<and>
    evaluate repeat_inline_return_one () = Return 7 ()
  \<close>
  by
    (simp add:
      repeat_ordinary_return_zero_def
      repeat_inline_return_zero_def
      repeat_inline_return_one_def
      evaluate_def return_func_def return_val_def literal_def
      Core_Expression.bind.simps)

urust_expr repeat_ordinary_abort_zero ::
  \<open>(unit, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [panic!("repeat abort"); 0] \<close>

urust_expr repeat_inline_abort_zero ::
  \<open>(unit, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [const { panic!("repeat abort") }; 0] \<close>

urust_expr repeat_inline_abort_one ::
  \<open>(unit, nat list, nat, unit, unit, unit) expression\<close>
  \<open> [const { panic!("repeat abort") }; 1] \<close>

lemma repeat_abort_propagation:
  \<open>
    evaluate repeat_ordinary_abort_zero () =
      Abort (Panic (String.implode ''repeat abort'')) () \<and>
    evaluate repeat_inline_abort_zero () = Success [] () \<and>
    evaluate repeat_inline_abort_one () =
      Abort (Panic (String.implode ''repeat abort'')) ()
  \<close>
  by
    (simp add:
      repeat_ordinary_abort_zero_def
      repeat_inline_abort_zero_def
      repeat_inline_abort_one_def
      evaluate_def abort_def literal_def
      Core_Expression.bind.simps)

urust_expr repeat_ordinary_yield_zero ::
  \<open>
    (unit, unit list, unit, unit,
     unit prompt, unit prompt_output) expression
  \<close>
  \<open> [\<y>\<i>\<e>\<l>\<d>; 0] \<close>

urust_expr repeat_inline_yield_zero ::
  \<open>
    (unit, unit list, unit, unit,
     unit prompt, unit prompt_output) expression
  \<close>
  \<open> [const { \<y>\<i>\<e>\<l>\<d> }; 0] \<close>

urust_expr repeat_inline_yield_one ::
  \<open>
    (unit, unit list, unit, unit,
     unit prompt, unit prompt_output) expression
  \<close>
  \<open> [const { \<y>\<i>\<e>\<l>\<d> }; 1] \<close>

lemma repeat_yield_propagation:
  \<open>
    (case evaluate repeat_ordinary_yield_zero () of
       Yield Pause () _ \<Rightarrow> True
     | _ \<Rightarrow> False) \<and>
    evaluate repeat_inline_yield_zero () = Success [] () \<and>
    (case evaluate repeat_inline_yield_one () of
       Yield Pause () _ \<Rightarrow> True
     | _ \<Rightarrow> False)
  \<close>
  by
    (simp add:
      repeat_ordinary_yield_zero_def
      repeat_inline_yield_zero_def
      repeat_inline_yield_one_def
      evaluate_def pause_def literal_def
      Core_Expression.bind.simps
      split: unit.splits)


end
