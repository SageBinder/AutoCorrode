theory Parser_Tests_Array_Repeats
  imports
    Parser_Tests_Negative_Conformance
    Shallow_Micro_Rust.Eval
begin

section\<open>Array repeats\<close>

declare [[urust_conformance = false]]
declare [[urust_pp_test = true]]
declare [[urust_verbosity = 0]]
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

new_urust_rejects audit
  \<open> [if true { 1 } else { false }; 2] \<close>
  \<open> Type unification failed \<close>

new_urust_rejects audit \<open> [1; repeat_small_length] \<close>
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

    fun integer expected (RL_Integer (actual, _)) =
          expected = actual
      | integer _ _ = false

    val _ =
      (case parse "[1; 2 + 3 * 4]" of
         UE_ArrayRepeat
           (AR_Ordinary, UE_Literal (LP_Integer ("1", _)),
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

new_urust_rejects audit \<open> [; 2] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [1;] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [1; 2 \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [1;; 2] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [1; 2; 3] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [1; 2,] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [const 1; 2] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [const { 1; 2] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [const { 1 }, 2] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [const { 1 };] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [const { 1 }; 2,] \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> [const { 1 }; 2; 3] \<close> \<open> syntax error \<close>

new_urust_rejects audit \<open> [1; 2u8] \<close>
  \<open> requires an explicit `as usize` cast \<close>
new_urust_rejects audit \<open> [1; 2u16] \<close>
  \<open> requires an explicit `as usize` cast \<close>
new_urust_rejects audit \<open> [1; 2u32] \<close>
  \<open> requires an explicit `as usize` cast \<close>
new_urust_rejects audit \<open> [1; 2u64] \<close>
  \<open> requires an explicit `as usize` cast \<close>
new_urust_rejects audit \<open> [1; 2u128] \<close>
  \<open> unsupported integer-literal suffix "u128" \<close>
new_urust_rejects audit \<open> [1; 2i32] \<close>
  \<open> unsupported integer-literal suffix "i32" \<close>
new_urust_rejects audit \<open> [1; unresolved_repeat_length] \<close>
  \<open> does not resolve to a global constant \<close>
new_urust_rejects audit
  \<open> [1; Parser_Tests_Array_Repeats::repeat_global_length] \<close>
  \<open> qualified path "Parser_Tests_Array_Repeats::repeat_global_length" requires an exact micro_rust_notation (literal) declaration \<close>
new_urust_rejects audit \<open> [1; WrongRole::Value] \<close>
  \<open> qualified path "WrongRole::Value" requires an exact micro_rust_notation (literal) declaration \<close>
new_urust_rejects audit \<open> [1; repeat_wrong_length] \<close>
  \<open> Type unification failed \<close>
new_urust_rejects audit \<open> let count = 2; [1; count] \<close>
  \<open> cannot use lexical local \<close>
new_urust_rejects audit \<open> [1; Some(2)] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; value.method()] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; value.field] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; values[0]] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; vec![2]] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; \<llangle>2 :: 64 word\<rrangle>] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; 1..2] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; slot = 2] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; |x| x] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; return 2] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; if true { 2 } else { 3 }] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; { 2 }] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; true] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; "two"] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; (1, 2)] \<close>
  \<open> array repeat length supports only \<close>
new_urust_rejects audit \<open> [1; 2 as u32] \<close>
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

    val legacy_repeat_spelling =
      Syntax.read_term ctxt "\<lbrakk> [1; 2] \<rbrakk>"
    val current_repeat = checked "[1; 2]"
    val _ =
      audit_assert "legacy frontend unexpectedly acquired repeat lowering"
        (count_constant \<^const_name>\<open>List.replicate\<close>
          legacy_repeat_spelling = 0)
    val _ =
      audit_assert "legacy/frontend array-repeat divergence disappeared"
        (not
          (Term.aconv
            (Term_Position.strip_positions current_repeat,
             Term_Position.strip_positions legacy_repeat_spelling)))
  in
    val _ =
      writeln
        "Array repeat lowering, compactness, regression, and frontend-boundary audits passed"
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
        "[1; Parser_Tests_Array_Repeats::repeat_global_length]"
        "Parser_Tests_Array_Repeats::repeat_global_length"
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
