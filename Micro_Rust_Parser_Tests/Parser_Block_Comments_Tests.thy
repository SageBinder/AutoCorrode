theory Parser_Block_Comments_Tests
  imports
    Parser_Test_Utils
    Parser_Precedence_Tests
    Parser_Array_Repeats_Tests
begin

declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]

section\<open> Nested Rust block-comment layout \<close>

text\<open>
Block comments are layout only in the ordinary lexer state. These checked equations compare
commented expressions with their comment-free spelling, including current repeat and precedence
behavior. Documentation-shaped comments are layout in expressions.
\<close>

urust_expr block_comment_empty \<open> /**/ /* */ () \<close>
urust_expr block_comment_unit \<open> () \<close>
lemma block_comment_empty_layout:
  \<open>block_comment_empty = block_comment_unit\<close>
  unfolding block_comment_empty_def block_comment_unit_def by (rule refl)

urust_expr block_comment_adjacent
  \<open>
    /** documentation-shaped */1u64/* outer /* inner /* deep */ */*//**/+
    /*! inner-documentation-shaped */2u64/* trailing */
  \<close>
urust_expr block_comment_sum \<open> 1u64 + 2u64 \<close>
lemma block_comment_adjacent_layout:
  \<open>block_comment_adjacent = block_comment_sum\<close>
  unfolding block_comment_adjacent_def block_comment_sum_def by (rule refl)

urust_expr block_comment_operators
  \<open> 8u64/**//2u64 + 2u64*/* multiplication boundary */3u64 \<close>
urust_expr block_comment_operators_plain \<open> 8u64 / 2u64 + 2u64 * 3u64 \<close>
lemma block_comment_operator_layout:
  \<open>block_comment_operators = block_comment_operators_plain\<close>
  unfolding block_comment_operators_def block_comment_operators_plain_def by (rule refl)

urust_expr block_comment_bindings
  \<open>
    /* leading */ let/* keyword boundary */value/* binder boundary */=/* assignment */3u64;
    if/* head */true/* before block */{/* block */value}/* else boundary */else{4u64/* tail */}
  \<close>
urust_expr block_comment_bindings_plain
  \<open> let value = 3u64; if true { value } else { 4u64 } \<close>
lemma block_comment_binding_layout:
  \<open>block_comment_bindings = block_comment_bindings_plain\<close>
  unfolding block_comment_bindings_def block_comment_bindings_plain_def by (rule refl)

context
  fixes count :: \<open>64 word\<close>
    and references :: \<open>(unit, unit, 64 word) Global_Store.ref list\<close>
begin

urust_expr block_comment_repeats
  \<open>
    [/* operand */const/* const boundary */{/* body */Some(0u64)/* tail */}
     /* separator */;/* length */count/* arithmetic */+1usize/* close */]
  \<close>
urust_expr block_comment_repeats_plain \<open> [const { Some(0u64) }; count + 1usize] \<close>
lemma block_comment_inline_repeat_layout:
  \<open>block_comment_repeats = block_comment_repeats_plain\<close>
  unfolding block_comment_repeats_def block_comment_repeats_plain_def by (rule refl)

urust_expr block_comment_registered_repeat
  \<open>
    [1u64/* separator */;/* qualified length */RepeatFixture/* path boundary */::
     /* segment */Length/* primitive cast */as/* target */usize]
  \<close>
urust_expr block_comment_registered_repeat_plain \<open> [1u64; RepeatFixture::Length as usize] \<close>
lemma block_comment_registered_repeat_layout:
  \<open>block_comment_registered_repeat = block_comment_registered_repeat_plain\<close>
  unfolding block_comment_registered_repeat_def block_comment_registered_repeat_plain_def by (rule refl)

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
urust_expr block_comment_precedence
  \<open>
    [*/* dereference */references/* postfix */[0usize]/* cast */as/* primitive */u64;
     /* repeat */count]
  \<close>
urust_expr block_comment_precedence_plain \<open> [*(references[0usize]) as u64; count] \<close>
lemma block_comment_precedence_layout:
  \<open>block_comment_precedence = block_comment_precedence_plain\<close>
  unfolding block_comment_precedence_def block_comment_precedence_plain_def by (rule refl)
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

end

section\<open> Positioned rejection and state boundaries \<close>

urust_expr_rejects \<open> /* comment-only input */ \<close> \<open> empty expression \<close>
urust_expr_rejects \<open> /* unterminated outer comment \<close> \<open> unterminated block comment \<close>
urust_expr_rejects \<open> /* outer /* nested comment */ still open \<close> \<open> unterminated block comment \<close>
urust_expr_rejects \<open> /*/ \<close> \<open> unterminated block comment \<close>
urust_expr_rejects \<open> 1u64 */ 2u64 \<close> \<open> syntax error found at / \<close>
urust_expr_rejects \<open> 1u64 /* closed */ */ 2u64 \<close> \<open> syntax error found at / \<close>
urust_expr_rejects \<open> f::<1 /* layout */ + 2>() \<close> \<open> unexpected input "/" \<close>
urust_expr_rejects \<open> l\<llangle>"value", /* layout */ True\<rrangle> \<close> \<open> unexpected input "/" \<close>
urust_expr_rejects \<open> va/* gap */lue \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> 1/* gap */u64 \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> 1u64 </* gap */= 2u64 \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> [1; count/* repeat validation */()] \<close> \<open> array repeat length \<close>

urust_expr block_comment_after_rejection \<open> /* reset /* nested */ */ () \<close>

section\<open> AST, checked terms, symbol ranges, markup, and recovery \<close>

text\<open>
The regression audit reuses the original D128 checks with current test APIs. Positioned source
contains both escaped Isabelle symbols and physical Unicode, plus a newline. Comment spans must
be reported once through the shared symbol-aware range path, without token markup inside the body.
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
      Position.end_offset_of left = Position.end_offset_of right andalso
      Position.line_of left = Position.line_of right

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
      ";\n escaped \<alpha> \<Rightarrow>; operators + - * / //; " ^
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
    val (_, inner_plus_pos) =
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
            UE_Literal (LP_Integer ("1_u64", actual_left)),
            UE_Literal (LP_Integer ("2_u64", actual_right)),
            actual_operator) =>
           (audit_assert "comment changed a neighboring literal range"
              (same_range actual_left left_pos andalso
               same_range actual_right right_pos);
            audit_assert "operator range moved across the comment"
              (same_range actual_operator outer_plus_pos))
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
      "\<epsilon>\<open>literal (''/* expression */'')\<close>"
    val _ =
      (case parse_text string_text of
         UE_Literal (LP_String (raw, _)) =>
           audit_assert "block-comment-shaped string text was consumed"
             (raw = string_text)
       | _ => error "block-comment regression audit: string AST changed")
    val _ =
      (case parse_text value_aq_text of
         UE_Literal (LP_ValAntiq source) =>
           audit_assert "value antiquotation block markers were consumed"
             (Input.string_of source = "''/* value */''")
       | _ =>
           error "block-comment regression audit: value antiquotation AST changed")
    val _ =
      (case parse_text expression_aq_text of
         UE_ExprAntiq source =>
           audit_assert "expression antiquotation block markers were consumed"
             (Input.string_of source =
               "literal (''/* expression */'')")
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

    fun failure_details text start =
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
           else
             let val body = YXML.parse_body (Runtime.exn_message exn)
             in (XML.content_of body, fold collect_markup body []) end)

    fun failure_message text start = #1 (failure_details text start)

    fun diagnostic_at markup pos =
      exists
        (fn ((name, properties), _) =>
          name = Markup.positionN andalso
          Properties.get properties Markup.offsetN =
            Option.map Value.print_int (Position.offset_of pos) andalso
          Properties.get properties Markup.lineN =
            Option.map Value.print_int (Position.line_of pos))
        markup

    fun recover () =
      (case parse_text "/* fresh /* nested */ */ ()" of
         UE_Unit _ => ()
       | _ =>
           error "block-comment regression audit: lexer state did not recover")

    fun expect_unterminated
        label text start expected_line =
      let
        val (message, markup) = failure_details text start
        val raw = find_from text "/*" 0
        val opener = Position.symbol_explode (String.substring (text, 0, raw)) start
        val _ =
          audit_assert (label ^ " diagnostic lost its symbol offset")
            (diagnostic_at markup opener)
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

    val _ =
      expect_unterminated
        "still-nested"
        "/* outer\n /* nested"
        (Position.make0 350 3500 0 "" "" "block-comment-still-nested")
        350
    val _ =
      expect_unterminated
        "after-symbols"
        ("// escaped \<alpha>\n  /* outer\n /* nested */")
        (Position.make0 360 3600 0 "" "" "block-comment-symbol-opener")
        361

    val unmatched_text = "1_u64 /* closed */ */ 2_u64"
    val unmatched_start = Position.make0 400 4000 0 "" "" "block-comment-unmatched"
    val (_, unmatched_slash) = token_position unmatched_text unmatched_start "/" (size "1_u64 /* closed */ *")
    val (unmatched_message, unmatched_markup) =
      failure_details unmatched_text unmatched_start
    val _ =
      (audit_assert "unmatched closer became a lexer error"
         (String.isSubstring "syntax error found at /" unmatched_message andalso
          not (String.isSubstring "unexpected input" unmatched_message));
       audit_assert "unmatched closer diagnostic moved from slash"
         (diagnostic_at unmatched_markup unmatched_slash);
       recover ())


    fun expect_state_rejection (label, text) =
      let
        val start = Position.make0 500 5000 0 "" "" label
        val (_, slash) = token_position text start "/" 0
        val (message, markup) = failure_details text start
        val _ =
          audit_assert (label ^ " admitted block layout")
            (String.isSubstring "unexpected input \"/\"" message)
        val _ =
          audit_assert (label ^ " rejection lost its slash position")
            (diagnostic_at markup slash)
      in recover () end
    val _ = List.app expect_state_rejection
      [("block-comment-generic", "f::<1 /* layout */ + 2>()"),
       ("block-comment-logdata", "l\<llangle>\"value\", /* layout */ True\<rrangle>")]

    fun expect_enclosing_comment (label, text) =
      let
        val (expression, markup) = capture_reports (fn () => parse_text text)
        val _ = (case expression of UE_Unit _ => ()
          | _ => error ("block-comment regression audit: " ^ label ^ " changed AST"))
        val _ =
          audit_assert (label ^ " leaked into block-comment state")
            (not (exists (fn ((name, _), body) =>
              name = Markup.typingN andalso body = "block comment") markup))
      in recover () end
    val _ = List.app expect_enclosing_comment
      [("Rust line comment", "// /* unclosed opener and extra closer */ */ /*\n()"),
       ("Isabelle formal comment",
        Symbol.comment ^ " " ^ Symbol.open_ ^ "/* unclosed */ */ /*" ^ Symbol.close ^ " ()")]

    val _ =
      (case parse_text "\"*/ /* unclosed\"" of
         UE_Literal (LP_String (text, _)) =>
           audit_assert "unbalanced markers in string were consumed"
             (text = "\"*/ /* unclosed\"")
       | _ => error "block-comment regression audit: opaque string AST")
    val _ =
      (case parse_text "\<llangle>''*/ /* unclosed''\<rrangle>" of
         UE_Literal (LP_ValAntiq source) =>
           audit_assert "unbalanced value-antiquotation markers were consumed"
             (Input.string_of source = "''*/ /* unclosed''")
       | _ => error "block-comment regression audit: opaque value antiquotation AST")
    val _ =
      (case parse_text "\<epsilon>\<open>literal (''*/ /* unclosed'')\<close>" of
         UE_ExprAntiq source =>
           audit_assert "unbalanced expression-antiquotation markers were consumed"
             (Input.string_of source = "literal (''*/ /* unclosed'')")
       | _ => error "block-comment regression audit: opaque expression antiquotation AST")

    val adjacent_left = "/* first \<alpha> */"
    val adjacent_right = "/*! second\n /* inner */ */"
    val adjacent_text = adjacent_left ^ adjacent_right ^ "()"
    val adjacent_start = Position.make0 600 6000 0 "" "" "block-comment-adjacent"
    val (_, adjacent_left_pos) = token_position adjacent_text adjacent_start adjacent_left 0
    val (_, adjacent_right_pos) = token_position adjacent_text adjacent_start adjacent_right 0
    val (_, adjacent_markup) = capture_reports (fn () =>
      parse_source (Parser_Lex_Util.positioned_content_source adjacent_text adjacent_start))
    val _ =
      List.app (fn pos =>
        audit_assert "adjacent comment lost its separate full range"
          (count_markup adjacent_markup Markup.comment1N pos = 1 andalso
           has_typing adjacent_markup "block comment" pos))
        [adjacent_left_pos, adjacent_right_pos]

    val _ =
      (case parse_text "if * /* prefix */base/* postfix */[index] as/* cast */u64 { () }" of
         UE_If
           (UE_Cast (UE_Unary (U_Deref, UE_Index (UE_Path _, UE_Path _, _), _),
             CT_Unsigned UT_U64, _), _, _, _) => ()
       | _ => error "block-comment regression audit: control-head precedence or primitive cast")
    val _ =
      List.app (fn text =>
        (ignore (failure_message text (Position.make0 700 7000 0 "" "" "block-comment-split"));
         recover ()))
        ["va/* gap */lue", "1/* gap */u64", "1u64 </* gap */= 2u64"]
  in
    val _ =
      writeln
        "Block-comment AST, term-shape, markup, diagnostics, and recovery regressions passed"
  end
\<close>

end
