theory Parser_Test_Isabelle_Comments
  imports Parser_Test_Utils Micro_Rust_Std_Lib.StdLib_Logging
begin

declare [[urust_conformance_check = true]]

section\<open> Isabelle formal comments \<close>

text\<open>
Formal comments are layout for the dedicated parser. Isabelle's command-span processing remains
responsible for checking document antiquotations and producing formal-comment markup.
\<close>

subsection\<open> Expression and function parity \<close>

urust_expr isabelle_comment_standalone
  \<open>
    \<comment> \<open>Standalone comment before the expression.\<close>
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

declare [[urust_verbose = 1]]

urust_fn isabelle_comment_function ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    \<comment> \<open>Function-body comment with \<^term>\<open>item\<close> treated as document text.\<close>
    item \<comment> \<open>Inline function-body comment.\<close>
  \<close>

declare [[urust_verbose = 0]]


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
    val structural_text =
      "1_u64 " ^
      formal_comment
        ("physical Unicode " ^ physical_lambda ^
         "; nested " ^ Symbol.open_ ^ "{ [ ( + => :: ) ] }" ^
         Symbol.close ^ "; escaped \<alpha>") ^
      " + 2_u64"
    val structural_start =
      Position.make0 41 400 0 "" "" "isabelle-comment-structure"
    val structural_source =
      Parser_Lex_Util.positioned_content_source
        structural_text structural_start
    val (left_raw, left_pos) =
      token_position structural_text structural_start "1_u64" 0
    val (comment_raw, _) =
      token_position structural_text structural_start Symbol.comment left_raw
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
            UE_Literal (LP_Integer ("1_u64", actual_left)),
            UE_Literal (LP_Integer ("2_u64", actual_right)),
            actual_operator) =>
           (audit_assert "comment created or changed an AST node"
              (same_range actual_left left_pos andalso
               same_range actual_right right_pos);
            audit_assert "operator position moved across the comment"
              (same_range actual_operator outer_plus_pos))
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
      (audit_assert "left numeral lost markup"
         (has_markup parser_markup Markup.numeralN left_pos);
       audit_assert "operator after comment lost markup"
         (has_markup parser_markup Markup.operatorN outer_plus_pos);
       audit_assert "right numeral lost markup"
         (has_markup parser_markup Markup.numeralN right_pos);
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
      "\<epsilon>\<open>\<up>(''" ^
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
         UE_Literal (LP_ValAntiq source) =>
           audit_assert "comment-shaped value antiquotation text was consumed"
             (Input.string_of source =
               "''" ^ formal_comment "value literal" ^ "''")
       | _ =>
           error
             "Isabelle-comment regression audit: value antiquotation AST changed")
    val _ =
      (case parse_text expression_aq_text of
         UE_ExprAntiq source =>
           audit_assert "comment-shaped expression antiquotation text was consumed"
             (Input.string_of source =
               "\<up>(''" ^ formal_comment "expression literal" ^ "'')")
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

end
