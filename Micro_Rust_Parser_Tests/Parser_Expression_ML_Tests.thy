(* ML audits for expressions: ASTs, lowering, markup, diagnostics, recovery and printing.
   The readable examples are in Parser_Expression_Examples. *)

theory Parser_Expression_ML_Tests
  imports
    Parser_Expression_Examples
begin

chapter\<open> Dereference and postfix precedence \<close>

section\<open>Both expression families and assignment places\<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 0, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

ML_val\<open>
  let
    open URust_AST
    val ctxt = \<^context>
    fun parse text =
      (case URust_Parser.parse_source ctxt (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "precedence audit: empty parse")
    fun indexed_operand (UE_Unary (U_Deref, UE_Index (UE_Path _, UE_Path _, _), _)) = true
      | indexed_operand _ = false
    fun assert label condition =
      if condition then () else error ("precedence audit: " ^ label)
    val _ = assert "ordinary expression" (indexed_operand (parse "*base[index]"))
    val _ =
      (case parse "if *base[index] { () }" of
         UE_If (condition, _, _, _) => assert "if head" (indexed_operand condition)
       | _ => error "precedence audit: if shape")
    val _ =
      (case parse "if let Some(item) = *base[index] { item }" of
         UE_IfLet (_, value, _, _, _) => assert "if-let head" (indexed_operand value)
       | _ => error "precedence audit: if-let shape")
    val _ =
      (case parse "match *base[index] { _ => () }" of
         UE_Match (_, value, _, _) => assert "match head" (indexed_operand value)
       | _ => error "precedence audit: match shape")
    val _ =
      (case parse "for item in *base[index] { () }" of
         UE_For (_, value, _, _) => assert "for head" (indexed_operand value)
       | _ => error "precedence audit: for shape")
    val _ =
      (case parse "if *(base).field { () }" of
         UE_If (UE_Unary (U_Deref, UE_Field (UE_Group _, "field", _), _), _, _, _) => ()
       | _ => error "precedence audit: grouped field in control head")
    val _ =
      (case parse "if *make().field { () }" of
         UE_If (UE_Unary (U_Deref, UE_Field (UE_Call _, "field", _), _), _, _, _) => ()
       | _ => error "precedence audit: call field in control head")
    val _ =
      (case parse "**base[index]" of
         UE_Unary (U_Deref, operand, _) => assert "repeated dereference" (indexed_operand operand)
       | _ => error "precedence audit: repeated dereference shape")
    val _ =
      (case parse "*base[index] as u64 + tail" of
         UE_Bin (Add, UE_Cast (operand, SCT_Primitive (CT_Unsigned UT_U64, _), _), UE_Path _, _) =>
           assert "cast and binary boundary" (indexed_operand operand)
       | _ => error "precedence audit: cast and binary shape")
    val _ =
      (case parse "&*base[index]" of
         UE_Unary (U_Borrow BM_Imm, operand, _) =>
           assert "borrow boundary" (indexed_operand operand)
       | _ => error "precedence audit: borrow shape")
    val _ =
      (case parse "*base[index] = value" of
         UE_Assign (Assign, UP_Deref (UE_Index (UE_Path _, UE_Path _, _), _), UE_Path _, _) => ()
       | _ => error "precedence audit: indexed dereference assignment place")
    val _ =
      (case parse "(*base)[index] = value" of
         UE_Assign (Assign, UP_Index (UP_Deref (UE_Path _, _), UE_Path _, _), UE_Path _, _) => ()
       | _ => error "precedence audit: explicitly grouped assignment place")
    val _ =
      (case parse "*base[index].field.0.method()?" of
         UE_Unary
           (U_Deref,
            UE_Unary
              (U_Propagate,
               UE_Call
                 (UC_Method
                   (UE_TupleProjection
                     (UE_Field (UE_Index _, "field", _), 0, _),
                    Path_Segment ("method", _, _)),
                  [], _),
               _),
            _) => ()
       | _ => error "precedence audit: complete postfix chain")
  in () end
\<close>

chapter\<open> Array repeats \<close>

section\<open>Array repeats\<close>

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

    fun integer expected (RL_Integer (Integer_Literal (actual, Source_Layout ( _, _), _))) =
          expected = actual
      | integer _ _ = false

    val _ =
      (case parse "[1; 2 + 3 * 4]" of
         UE_ArrayRepeat
           (AR_Ordinary, UE_Literal (LP_Integer (Integer_Literal ("1", Source_Layout ( _, _), _))),
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
    val _ =
      (case parse "[*base[index]; 2]" of
         UE_ArrayRepeat
           (AR_Ordinary, UE_Unary (U_Deref, UE_Index _, _), _, _) => ()
       | _ => error "array repeat AST audit: ordinary dereference operand grouping changed")
    val _ =
      (case parse "[const { *base[index] }; 2]" of
         UE_ArrayRepeat
           (AR_InlineConst,
            UE_Block (UE_Unary (U_Deref, UE_Index _, _), _), _, _) => ()
       | _ => error "array repeat AST audit: inline-const dereference operand grouping changed")
    val _ =
      (case parse "*[reference; 2][index]" of
         UE_Unary (U_Deref, UE_Index (UE_ArrayRepeat _, _, _), _) => ()
       | _ => error "array repeat AST audit: dereference of indexed repeat changed")
  in
    val _ = writeln "Array repeat grammar and AST boundaries passed"
  end
\<close>

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
      (case Exn.result
          (fn () => Parser_Test_Elaboration.expression_with_arguments ctxt
            [("count", Position.none)]
            (Parser_Lex_Util.text_source "[1; count]")) () of
         Exn.Exn exn =>
           audit_assert "declaration argument bypassed lexical-local rejection"
             (String.isSubstring "cannot use lexical local" (Runtime.exn_message exn))
       | Exn.Res _ =>
           error "array repeat lowering audit: declaration argument accepted as a length")

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
      audit_assert "ordinary indexing lost index_const"
        (count_constant \<^const_name>\<open>index_const\<close>
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
      expect_positioned_failure 3 "qualified-length"
        "[1; RepeatFixture::MissingLength]" "MissingLength"
        "requires an exact micro_rust_notation (literal) declaration"
    val _ =
      expect_positioned_failure 3 "qualified-global"
        "[1; Parser_Expression_Examples::repeat_global_length]"
        "repeat_global_length"
        "requires an exact micro_rust_notation (literal) declaration"
    val _ =
      expect_positioned_failure 4 "length-before-operand"
        "[missing_operand; missing_length]" "missing_length"
        "does not resolve to a global constant"
  in
    val _ =
      writeln
        "Array repeat markup, navigation, positioned diagnostics, symbol offsets, and recovery passed"
  end
\<close>

chapter\<open> Block comments \<close>

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
            UE_Literal (LP_Integer (Integer_Literal ("1_u64", Source_Layout ( actual_left, _), _))),
            UE_Literal (LP_Integer (Integer_Literal ("2_u64", Source_Layout ( actual_right, _), _))),
            actual_operator) =>
           (audit_assert "comment changed a neighboring literal range"
              (same_range actual_left left_pos andalso
               same_range actual_right right_pos);
            audit_assert "operator range moved across the comment"
              (same_range
                (the_source_token_position actual_operator Operator_Token)
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
      "\<epsilon>\<open>literal (''/* expression */'')\<close>"
    val _ =
      (case parse_text string_text of
         UE_Literal (LP_String (raw, _)) =>
           audit_assert "block-comment-shaped string text was consumed"
             (raw = string_text)
       | _ => error "block-comment regression audit: string AST changed")
    val _ =
      (case parse_text value_aq_text of
         UE_Literal (LP_ValAntiq (Value_Antiquotation (source, _))) =>
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
         UE_Literal (LP_ValAntiq (Value_Antiquotation (source, _))) =>
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
             SCT_Primitive (CT_Unsigned UT_U64, _), _), _, _, _) => ()
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

chapter\<open> Printer \<close>

section\<open> Canonical AST printer \<close>

declare [[urust_verbosity = 2]]

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

  fun parse_datatype_input source =
    (case URust_Parser.parse_datatype_source \<^context>
        source of
       SOME item => item
     | NONE => error "datatype printer test parsed empty source")

  fun parse_datatype source =
    parse_datatype_input (Parser_Lex_Util.text_source source)

  fun render options source =
    URust_Printer.string_of_expr options (parse source)

  fun render_datatype options source =
    URust_Printer.string_of_datatype options
      (parse_datatype source)

  fun render_margin margin options source =
    URust_Printer.pretty_expr options (parse source)
    |> Pretty.string_of_ops (Pretty.pure_output_ops (SOME margin))

  fun render_datatype_margin margin options source =
    URust_Printer.pretty_datatype options
      (parse_datatype source)
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

  fun serialized_roundtrip source =
    let
      val first =
        render URust_Printer.serialized_options source
      val second =
        render URust_Printer.serialized_options first
    in
      assert
        ("serialized printer roundtrip failed for " ^
          quote source ^ "\nfirst:\n" ^ first ^
          "\nsecond:\n" ^ second)
        (first = second)
    end

  fun canonical_datatype source expected =
    let
      val actual =
        render_datatype URust_Printer.serialized_options source
    in
      assert
        ("canonical datatype printer output changed for " ^
          quote source ^
          "\nexpected: " ^ quote expected ^
          "\nactual:   " ^ quote actual)
        (actual = expected)
    end

  fun datatype_human_idempotence source =
    let
      val first =
        render_datatype URust_Printer.human_options source
      val second =
        render_datatype URust_Printer.human_options first
    in
      assert
        ("human datatype printer idempotence failed for " ^
          quote source ^ "\nfirst:\n" ^ first ^
          "\nsecond:\n" ^ second)
        (first = second)
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

subsection\<open> Literal and cast source metadata roundtrips \<close>

ML_val\<open>
  let
    open Parser_Printer_Test
    open URust_AST

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left =
        Position.end_offset_of right

    fun expected_position source spelling cursor =
      let
        val text = Input.text_of source
        fun seek offset =
          if offset + size spelling > size text then
            error
              ("printer metadata roundtrip: missing " ^
                quote spelling)
          else if
            String.substring
              (text, offset, size spelling) = spelling
          then offset
          else seek (offset + 1)
        val raw = seek cursor
        val layout =
          Parser_Lex_Util.make_source_layout source
      in
        Position.range_position
          (Parser_Lex_Util.text_range
            layout (raw, spelling))
      end

    val roundtrip_sources =
      ["0b10_01u8",
       "0o7_5_u16",
       "0xff_00u32",
       "0xff_u32 as *const u8",
       "\<llangle>value\<rrangle>"]

    val _ =
      List.app serialized_roundtrip roundtrip_sources

    val _ =
      List.app
        (fn (source, expected) =>
          canonical source expected)
        [("0b10_01u8", "0b10_01u8"),
         ("0o7_5_u16", "0o7_5_u16"),
         ("0xff_00u32", "0xff_00u32"),
         ("0xff_u32 as *const u8",
          "0xff_u32 as * const u8"),
         ("\<llangle>value\<rrangle>",
          "\<llangle>value\<rrangle>")]

    val cast_text =
      render URust_Printer.serialized_options
        "0xff_u32 as *const u8"
    val cast_source =
      Parser_Lex_Util.positioned_content_source
        cast_text
        (Position.make0 31 9000 0 "" ""
          "printer-cast-metadata-roundtrip")
    val _ =
      (case parse_input cast_source of
         UE_Cast
           (UE_Literal (LP_Integer integer),
            primitive_target as SCT_Primitive _, _) =>
           (assert "printer roundtrip changed the integer spelling"
              (integer_literal_lexeme integer = "0xff_u32");
            assert "printer roundtrip changed the numeric range"
              (same_range
                (integer_literal_numeric_position integer)
                (expected_position cast_source "0xff" 0));
            assert "printer roundtrip changed the suffix range"
              (case integer_literal_suffix_position integer of
                 SOME actual =>
                   same_range actual
                     (expected_position cast_source "_u32" 0)
               | NONE => false);
            assert "printer roundtrip changed the cast type range"
              (case
                  source_cast_target_type_position
                    primitive_target of
                 SOME actual =>
                   same_range actual
                     (expected_position cast_source "u8"
                       (size "0xff_u32"))
               | NONE => false))
       | _ =>
           error
             "printer metadata roundtrip: cast AST changed")

    val antiquotation_text =
      render URust_Printer.serialized_options
        "\<llangle>value\<rrangle>"
    val antiquotation_source =
      Parser_Lex_Util.positioned_content_source
        antiquotation_text
        (Position.make0 37 12000 0 "" ""
          "printer-antiquotation-metadata-roundtrip")
    val _ =
      (case parse_input antiquotation_source of
         UE_Literal (LP_ValAntiq antiquotation) =>
           (case
               source_tokens
                 (value_antiquotation_source_layout
                   antiquotation) of
              [(Literal_Token, open_pos),
               (Literal_Token, close_pos)] =>
                (assert
                   "printer roundtrip changed the value-antiquotation opener range"
                   (same_range open_pos
                     (expected_position antiquotation_source
                       "\<llangle>" 0));
                 assert
                   "printer roundtrip changed the value-antiquotation closer range"
                   (same_range close_pos
                     (expected_position antiquotation_source
                       "\<rrangle>" 0)))
            | _ =>
                error
                  "printer metadata roundtrip: value-antiquotation delimiter layout changed")
       | _ =>
           error
             "printer metadata roundtrip: value-antiquotation AST changed")
  in
    ()
  end
\<close>

subsection\<open> Datatype token, pretty, and string operations \<close>

ML_val\<open>
  let
    open Parser_Printer_Test

    val unit_struct = "struct PrinterUnit;"
    val tuple_struct =
      "struct PrinterTuple(u32, bool, " ^
        "\<tau>\<open>  nat option  \<close>);"
    val named_struct =
      "struct PrinterNamed { left: u32, right: bool, }"
    val enum_item =
      "enum C { E, P(u8, ()), " ^
        "N { c: i32, r: " ^
        "\<tau>\<open>8 word\<close>, }, }"
    val all_primitives =
      "struct PrinterPrimitives(" ^
        "u8, u16, u32, u64, usize, i32, i64, bool, ());"

    val _ = canonical_datatype unit_struct unit_struct
    val _ =
      canonical_datatype tuple_struct
        ("struct PrinterTuple(u32, bool, " ^
          "\<tau>\<open>  nat option  \<close>);")
    val _ =
      canonical_datatype named_struct
        "struct PrinterNamed { left: u32, right: bool }"
    val _ =
      canonical_datatype enum_item
        ("enum C { E, P(u8, ()), " ^
          "N { c: i32, r: " ^
          "\<tau>\<open>8 word\<close> } }")
    val _ =
      canonical_datatype all_primitives all_primitives

    val sources =
      [unit_struct, tuple_struct, named_struct,
       enum_item, all_primitives]
    val _ = List.app datatype_human_idempotence sources

    val named_human =
      render_datatype_margin 80
        URust_Printer.human_options named_struct
    val _ =
      assert
        ("human named struct layout changed:\n" ^
          named_human)
        (named_human =
          "struct PrinterNamed {\n" ^
          "  left: u32,\n" ^
          "  right: bool\n" ^
          "}")

    val enum_human =
      render_datatype_margin 80
        URust_Printer.human_options enum_item
    val _ =
      assert
        ("human enum layout changed:\n" ^
          enum_human)
        (enum_human =
          "enum C {\n" ^
          "  E,\n" ^
          "  P(u8, ()),\n" ^
          "  N {\n" ^
          "    c: i32,\n" ^
          "    r: \<tau>\<open>8 word\<close>\n" ^
          "  }\n" ^
          "}")

    val positioned_text =
      "enum Positioned { Unit, Tuple(u64), " ^
        "Named { value: \<tau>\<open>  nat option  \<close>, }, }"
    val left =
      Parser_Lex_Util.positioned_content_source
        positioned_text
        (Position.make0 12 300 0 "" "datatype-printer-left" "")
    val right =
      Parser_Lex_Util.positioned_content_source
        positioned_text
        (Position.make0 40 900 0 "" "datatype-printer-right" "")
    val left_item = parse_datatype_input left
    val right_item = parse_datatype_input right
    val left_tokens =
      URust_Printer.tokens_of_datatype
        URust_Printer.serialized_options left_item
    val right_tokens =
      URust_Printer.tokens_of_datatype
        URust_Printer.serialized_options right_item
    val _ =
      assert "datatype tokens retained source positions"
        (left_tokens = right_tokens)
    val token_pretty =
      URust_Printer.pretty_tokens left_tokens
      |> Pretty.string_of_ops
          (Pretty.pure_output_ops (SOME 80))
    val datatype_pretty =
      URust_Printer.pretty_datatype
        URust_Printer.serialized_options left_item
      |> Pretty.string_of_ops
          (Pretty.pure_output_ops (SOME 80))
    val _ =
      assert "datatype token and direct pretty operations disagree"
        (token_pretty = datatype_pretty)
    val _ =
      assert "raw positioned HOL type body was normalized"
        (String.isSubstring
          "\<tau>\<open>  nat option  \<close>"
          datatype_pretty)
  in
    ()
  end
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
        "|(left, right)| left + right",
        "|item, (left, (right, _))| item",
        "|whole @ (left, right)| left",
        "|[rest @ ..]| rest",
        "|_| value",
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
        "match value { [head, middle @ .., tail] => middle, _ => [] }",
        "let whole @ [rest @ ..] = value; (whole, rest)",
        "let (whole @ [rest @ ..], other) = value; (whole, rest, other)",
        "for whole @ [rest @ ..] in values { (whole, rest) }",
        "match value { Some(item) => return item, None => return 0 }",
        "match value { Some(item) => { return item; } None => return 0 }",
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
      assert "human mode omitted the group around an or-pattern closure formal"
        (render URust_Printer.human_options "|(left | right)| left" =
          "|(left | right)| left")
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
    val left_ast = parse_source left_source
    val right_ast = parse_source right_source
    val left_tokens =
      URust_Printer.tokens_of_expr URust_Printer.serialized_options
        left_ast
    val right_tokens =
      URust_Printer.tokens_of_expr URust_Printer.serialized_options
        right_ast
    val _ =
      assert "source layouts did not retain independent offsets"
        (Position.offset_of (URust_AST.expression_position left_ast) <>
         Position.offset_of (URust_AST.expression_position right_ast))
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
          if Position.file_of (Position.thread_data ()) =
              SOME source_name
          then Synchronized.change target (append chunks)
          else ()
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.warning_fn
              (collect warnings)
              (Unsynchronized.setmp Private_Output.writeln_fn
                (collect ordinary)
                (Unsynchronized.setmp Private_Output.writeln_urgent_fn
                  (collect urgent)
                  (run_command source_name command_text))) ())
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
    val function_source =
      Symbol.open_ ^
      " fn PrettyBody(item: u64) -> u64 { " ^
      "let value = (((item))); (value + 1u64) * 2u64 } " ^
      Symbol.close
    val rust_function_source =
      Symbol.open_ ^
      " fn PrettyRust(item: u64, flag: bool) -> u64 { " ^
      "if flag { item } else { 0u64 } } " ^
      Symbol.close
    val antiquotation_source =
      Symbol.open_ ^ " \<llangle>item :: nat\<rrangle> " ^ Symbol.close

    val pretty_expression =
      capture "pretty-expression"
        ("urust_expr " ^
          "[pretty, verbosity = 2] " ^
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
          "[pretty = true, verbosity = 2] " ^
          "pretty_function " ^ function_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty function" expected
            (#ordinary pretty_function))
        ["definition pretty_function_def:",
         "pretty_function item \<equiv>",
         "let value = item;",
         "(value + 1u64) * 2u64"]
    val _ =
      assert_contains "pretty function layout"
        ("pretty_function item \<equiv> FunctionBody \<mu>" ^ Symbol.open_ ^
          "\n  let value = item;")
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

    val pretty_rust_function =
      capture "pretty-rust-function"
        ("urust_fn " ^
          "[pretty = true, verbosity = 2] " ^
          "pretty_rust_function " ^ rust_function_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty Rust function" expected
            (#ordinary pretty_rust_function))
        ["definition pretty_rust_function_def:",
         "pretty_rust_function item flag \<equiv>",
         "if flag {",
         "item",
         "0u64"]
    val _ =
      assert_contains "pretty Rust function layout"
        ("pretty_rust_function item flag \<equiv> FunctionBody \<mu>" ^
          Symbol.open_ ^ "\n  if flag {")
        (#ordinary pretty_rust_function)
    val _ =
      List.app
        (fn unexpected =>
          assert_absent "pretty Rust function"
            unexpected (#ordinary pretty_rust_function))
        ["|item, flag|", "fn PrettyRust", "Ignored::Result", "->"]
    val _ =
      List.app
        (fn name =>
          assert_marked_text "pretty Rust function formal"
            Markup.boundN name (#ordinary_body pretty_rust_function))
        ["item", "flag"]
    val _ =
      assert_symbolic_urust_wrapper "pretty Rust function wrapper"
        (#ordinary pretty_rust_function)
        (#ordinary_body pretty_rust_function)

    val pretty_abbreviation =
      capture "pretty-abbreviation"
        ("urust_expr " ^
          "[abbrev, pretty, verbosity = 2] " ^
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
          "[application_def, pretty, verbosity = 2] " ^
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
          "[application_def, pretty, verbosity = 2] " ^
          "pretty_application_function " ^ function_source)
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
        ("pretty_application_function item \<equiv> FunctionBody \<mu>" ^
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
          "[pretty, verbosity = 2] _ " ^
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
    val _ =
      assert_absent "pretty anonymous expression"
        "FunctionBody" (#ordinary pretty_anonymous)

    val pretty_anonymous_function =
      capture "pretty-anonymous-function"
        ("urust_fn " ^
          "[pretty, verbosity = 2] _ " ^
          function_source)
    val _ =
      assert_contains "pretty anonymous function"
        ("FunctionBody \<mu>" ^ Symbol.open_)
        (#ordinary pretty_anonymous_function)
    val _ =
      assert_symbolic_urust_wrapper "pretty anonymous function wrapper"
        (#ordinary pretty_anonymous_function)
        (#ordinary_body pretty_anonymous_function)

    val scoped_pretty =
      capture "pretty-scoped"
        ("declare [[urust_pretty = true]]\n" ^
          "declare [[urust_verbosity = 2]]\n" ^
          "urust_expr " ^
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
          "urust_expr [pretty = false] " ^
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
          "[pretty, verbosity = 0] " ^
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
    val layout = make_source_layout pos []
    val literal_layout =
      make_source_layout pos [(Literal_Token, pos)]
    val integer =
      Integer_Literal ("1", literal_layout, NONE)
    val antiquotation =
      Value_Antiquotation
        (Parser_Lex_Util.text_source "callee", layout)
    val unit = UE_Unit layout
    val one = UE_Literal (LP_Integer integer)
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
      (fn () => print (UE_Tuple ([unit], layout)))
    val _ = expect_error "one-element tuple pattern"
      "tuple pattern requires at least 2 members"
      (fn () =>
        print
          (UE_Match
            (MF_Auto, unit,
             [UR_Arm
               (P_Tuple ([P_Wild pos], layout), NONE, unit, layout)],
             layout)))
    val _ = serialized_roundtrip
      "match value { EmptyTuple() => (), EmptyNamed {} => () }"
    val _ = expect_error "singleton or-pattern"
      "or-pattern requires at least 2 members"
      (fn () =>
        print
          (UE_Match
            (MF_Auto, unit,
             [UR_Arm
               (P_Or ([P_Wild pos], layout), NONE, unit, layout)],
             layout)))
    val _ = expect_error "invalid tuple projection"
      "tuple projection index 16"
      (fn () => print (UE_TupleProjection (unit, 16, layout)))
    val _ = expect_error "invalid function-literal arity"
      "outside the supported range 1 through 14"
      (fn () =>
        print
          (UE_Call
            (UC_FunLiteral
              (antiquotation, 0, pos, NONE),
             [], layout)))
    val _ = expect_error "primitive path without associated item"
      "primitive path requires an associated-item segment"
      (fn () => print (UE_Path primitive_single))
    val _ = expect_error "primitive named cast target"
      "named cast target cannot use a primitive path head"
      (fn () =>
        print (UE_Cast (one, SCT_Named primitive_single, layout)))
    val _ = expect_error "matches arguments payload"
      "matches! requires the dedicated expression/pattern payload"
      (fn () =>
        print
          (UE_Macro
            (matches_path, MP_Arguments [one], layout)))
    val _ = expect_error "wrong matches payload head"
      "MP_Matches requires the exact matches! macro head"
      (fn () =>
        print
          (UE_Macro
            (path, MP_Matches (one, P_Wild pos), layout)))
    val _ = expect_error "inline const without block"
      "inline-const array repeat operand requires a block"
      (fn () =>
        print
          (UE_ArrayRepeat
            (AR_InlineConst, one, RL_Integer integer, layout)))
    val _ = expect_error "if without success block"
      "if success branch requires a block"
      (fn () => print (UE_If (one, one, NONE, layout)))
    val _ = expect_error "terminal return sequence"
      "terminal return cannot be represented"
      (fn () =>
        print
          (UE_Seq
            (UE_Return (NONE, layout), UE_Unit layout, layout)))

    fun print_datatype item =
      URust_Printer.string_of_datatype
        URust_Printer.serialized_options item
    fun field name =
      Datatype_Field
        (name, pos, Primitive_Type (DPT_U32, pos))
    fun variant name shape =
      Datatype_Variant (name, pos, shape)

    val _ = if print_datatype (Struct_Item ("EmptyTuple", pos, Tuple_Shape [], pos)) =
      "struct EmptyTuple();" then () else error "empty tuple struct did not roundtrip"
    val _ = if print_datatype (Struct_Item ("EmptyNamed", pos, Named_Shape [], pos)) =
      "struct EmptyNamed {}" then () else error "empty named struct did not roundtrip"
    val _ = expect_error "empty enum"
      "enum declaration requires at least one member"
      (fn () =>
        print_datatype
          (Enum_Item ("EmptyEnum", pos, [], pos)))
    val _ = expect_error "duplicate enum variant"
      "duplicate identifier"
      (fn () =>
        print_datatype
          (Enum_Item
            ("DuplicateVariant", pos,
             [variant "Same" Unit_Shape,
              variant "Same" Unit_Shape], pos)))
    val _ = expect_error "duplicate datatype field"
      "duplicate identifier"
      (fn () =>
        print_datatype
          (Struct_Item
            ("DuplicateField", pos,
             Named_Shape [field "value", field "value"],
             pos)))
    val _ = expect_error "placeholder datatype name"
      "cannot be `_`"
      (fn () =>
        print_datatype
          (Struct_Item ("_", pos, Unit_Shape, pos)))
    val _ = expect_error "placeholder datatype field"
      "cannot be `_`"
      (fn () =>
        print_datatype
          (Struct_Item
            ("PlaceholderField", pos,
             Named_Shape [field "_"], pos)))
    val _ = expect_error "empty raw datatype type"
      "HOL datatype type source is empty"
      (fn () =>
        print_datatype
          (Struct_Item
            ("EmptyRawType", pos,
             Tuple_Shape
               [HOL_Type_Source
                 (Parser_Lex_Util.text_source "")],
             pos)))
    val _ = expect_error "excessive datatype arity"
      "at most 14 are supported"
      (fn () =>
        print_datatype
          (Struct_Item
            ("Excessive", pos,
             Tuple_Shape
               (replicate 15
                 (Primitive_Type (DPT_U32, pos))),
             pos)))
  in
    ()
  end
\<close>

end
