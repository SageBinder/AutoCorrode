theory Parser_Semantic_Navigation_Tests
  imports
    Parser_Test_Utils
    Micro_Rust_Std_Lib.StdLib_Logging
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open>Resolved navigation fixtures\<close>

consts
  semantic_navigation_ref ::
    \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  semantic_navigation_word :: \<open>32 word\<close>
  semantic_navigation_shift :: \<open>64 word\<close>
  semantic_navigation_gref :: \<open>(unit, unit) gref\<close>

definition semantic_navigation_allocate ::
    \<open>32 word \<Rightarrow>
      (unit, (unit, unit, 32 word) Global_Store.ref,
       unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_allocate _ =
        FunctionBody (literal semantic_navigation_ref)
    \<close>

definition semantic_navigation_dereference ::
    \<open>(unit, unit, 32 word) Global_Store.ref \<Rightarrow>
      (unit, 32 word, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_dereference _ =
        FunctionBody (literal 0)
    \<close>

definition semantic_navigation_update ::
    \<open>(unit, unit, 32 word) Global_Store.ref \<Rightarrow> 32 word \<Rightarrow>
      (unit, unit, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_update _ _ =
        FunctionBody (literal ())
    \<close>

definition semantic_navigation_assign_add ::
    \<open>(unit, unit, 32 word) Global_Store.ref \<Rightarrow> 32 word \<Rightarrow>
      (unit, unit, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_assign_add _ _ =
        FunctionBody (literal ())
    \<close>

adhoc_overloading
  store_reference_const \<rightleftharpoons> semantic_navigation_allocate

adhoc_overloading
  store_dereference_const \<rightleftharpoons> semantic_navigation_dereference

adhoc_overloading
  store_update_const \<rightleftharpoons> semantic_navigation_update

adhoc_overloading
  assign_add_const \<rightleftharpoons> semantic_navigation_assign_add

definition semantic_navigation_field :: \<open>(nat, nat) lens\<close>
  where \<open>semantic_navigation_field = id\<^sub>L\<close>

definition semantic_navigation_focus ::
    \<open>(nat, nat) lens \<Rightarrow> nat \<Rightarrow> nat\<close>
  where
    \<open>semantic_navigation_focus field value = lens_view field value\<close>

adhoc_overloading
  focus_lens_const \<rightleftharpoons> semantic_navigation_focus

micro_rust_notation (field)
  semantic_navigation_field
  ("navigationField")

definition semantic_navigation_named_macro ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_named_macro =
        lift_fun1 (\<lambda>value. value)
    \<close>

abbreviation semantic_navigation_abbrev_macro ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_abbrev_macro \<equiv>
        semantic_navigation_named_macro
    \<close>

micro_rust_notation (call)
  semantic_navigation_named_macro
  ("NavigationMacro::named!")

micro_rust_notation (call)
  semantic_navigation_abbrev_macro
  ("NavigationMacro::abbrev!")

micro_rust_notation (call)
  \<open>lift_fun1 (\<lambda>value :: bool. value)\<close>
  ("NavigationMacro::anonymous!")

section\<open>Checked resolved denotations\<close>

ML_val\<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("resolved semantic navigation audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle ^ " in " ^ quote text)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun nth_from text needle occurrence =
      let
        fun seek index offset =
          let val found = find_from text needle offset
          in
            if index = occurrence then found
            else seek (index + 1) (found + size needle)
          end
      in seek 0 0 end

    fun token_position text start needle occurrence =
      let
        val raw = nth_from text needle occurrence
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (token_start, Position.symbol_explode needle token_start)
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun entity_names kind position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN = SOME kind andalso
                has_position properties position
            then Properties.get properties Markup.nameN
            else NONE)

    fun constant_targets position markup =
      entity_names Markup.constantN position markup

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    fun contains_navigation_marker term =
      Term.exists_subterm
        (fn Const (name, _) =>
              name =
                \<^const_name>\<open>semantic_navigation_target\<close> orelse
              name =
                \<^const_name>\<open>semantic_navigation_annotation\<close> orelse
              name =
                \<^const_name>\<open>semantic_navigation_probe\<close>
          | _ => false)
        term

    fun head_constant_name label term =
      (case Term.head_of (Term_Position.strip_positions term) of
         Const (name, _) => name
       | head =>
           error
             ("resolved semantic navigation audit: " ^
               label ^ " has non-constant head " ^
               Syntax.string_of_term ctxt head))

    val ucast_name =
      head_constant_name "ucast" \<^term>\<open>ucast\<close>
    val scast_name =
      head_constant_name "scast" \<^term>\<open>scast\<close>
    val word_type_name =
      (case \<^typ>\<open>64 word\<close> of
         Type (name, _) => name
       | _ =>
           error
             "resolved semantic navigation audit: word type is not a type constructor")
    val abbreviation_name =
      (case
          Proof_Context.read_const
            {proper = true, strict = false} ctxt
            "semantic_navigation_abbrev_macro" of
         Const (name, _) => name
       | _ =>
           error
             "resolved semantic navigation audit: abbreviation identity is not a constant")
    val info_name =
      (case
          Proof_Context.read_const
            {proper = true, strict = false} ctxt "info" of
         Const (name, _) => name
       | _ =>
           error
             "resolved semantic navigation audit: logger identity is not a constant")

    fun capture serial label text =
      let
        val start =
          Position.make0
            (500 + serial) (120000 + serial * 1000)
            0 "" ""
            ("resolved-semantic-navigation-" ^ label)
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (term, markup) =
          Parser_Test_Reports.markup (fn () =>
            Parser_Test_Elaboration.expression ctxt source)
        val _ =
          audit_assert
            (label ^ " returned an internal navigation marker")
            (not (contains_navigation_marker term))
      in
        {start = start, term = term, markup = markup}
      end

    fun audit_case serial label text specifications =
      let
        val {start, markup, ...} =
          capture serial label text
        fun check (needle, occurrence, expected) =
          let
            val position =
              token_position text start needle occurrence
            val actual = constant_targets position markup
          in
            audit_assert
              (label ^ " target changed at " ^
                quote needle ^ " occurrence " ^
                string_of_int occurrence ^
                ": expected " ^ commas_quote expected ^
                ", found " ^ commas_quote actual)
              (actual = expected);
            audit_assert
              (label ^ " native constant styling count changed")
              (count_markup Markup.constN position markup =
                length expected)
          end
      in List.app check specifications end

    fun audit_target_group serial label text specifications expected =
      let
        val {start, markup, ...} =
          capture serial label text
        fun targets (needle, occurrence) =
          constant_targets
            (token_position text start needle occurrence)
            markup
        val actual = map targets specifications
        val _ =
          List.app
            (fn (specification, found) =>
              let
                val (needle, occurrence) = specification
              in
                audit_assert
                  (label ^ " target changed at " ^
                    quote needle ^ " occurrence " ^
                    string_of_int occurrence ^
                    ": expected " ^ commas_quote expected ^
                    ", found " ^ commas_quote found)
                  (found = expected);
                audit_assert
                  (label ^ " native constant styling count changed")
                  (count_markup Markup.constN
                    (token_position text start
                      needle occurrence) markup =
                    length expected)
              end)
            (specifications ~~ actual)
        val _ =
          audit_assert
            (label ^ " paired or grouped tokens diverged")
            (case actual of
               [] => false
             | first :: rest =>
                 List.all (fn targets => targets = first) rest)
      in () end

    fun audit_markup_count serial label text needle occurrence
        markup_name expected =
      let
        val {start, markup, ...} =
          capture serial label text
        val position =
          token_position text start needle occurrence
      in
        audit_assert (label ^ " markup count changed")
          (count_markup markup_name position markup = expected)
      end

    fun audit_term_invariant serial label text =
      let
        val {term = positioned, ...} =
          capture serial label text
        val plain =
          Parser_Test_Elaboration.expression ctxt
            (Parser_Lex_Util.text_source text)
        val strip = Term_Position.strip_positions
      in
        audit_assert
          (label ^ " navigation changed the checked term")
          (Term.aconv (strip positioned, strip plain));
        audit_assert
          (label ^ " unpositioned term retained a marker")
          (not (contains_navigation_marker plain))
      end

    fun audit_type_token serial label text needle occurrence =
      let
        val {start, markup, ...} = capture serial label text
        val position = token_position text start needle occurrence
      in
        audit_assert (label ^ " type target changed")
          (entity_names Markup.type_nameN position markup =
            [word_type_name]);
        audit_assert (label ^ " type styling changed")
          (count_markup Markup.tconstN position markup = 1);
        audit_assert (label ^ " type token acquired a constant target")
          (constant_targets position markup = [])
      end

    val deferred_text = "panic!()"
    val deferred_start =
      Position.make0 450 100000 0 "" ""
        "resolved-semantic-navigation-deferred"
    val deferred_source =
      Parser_Lex_Util.positioned_content_source
        deferred_text deferred_start
    val ((deferred_term, deferred_reports), during_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.capture (fn () =>
          Parser_Test_Elaboration.expression ctxt deferred_source))
    val deferred_name =
      token_position deferred_text deferred_start "panic" 0
    val deferred_bang =
      token_position deferred_text deferred_start "!" 0
    val _ =
      audit_assert "checked capture leaked a target before replay"
        (constant_targets deferred_name during_markup = [] andalso
         constant_targets deferred_bang during_markup = [])
    val ((), replay_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.replay ctxt deferred_reports)
    val deferred_targets =
      [\<^const_name>\<open>abort\<close>,
       \<^const_name>\<open>Panic\<close>]
    val _ =
      List.app
        (fn position =>
          audit_assert
            "checked replay lost stable deduplication or primary-last order"
            (constant_targets position replay_markup =
              deferred_targets))
        [deferred_name, deferred_bang]
    val _ =
      audit_assert "checked deferred term retained an internal marker"
        (not (contains_navigation_marker deferred_term))

    val type_text = "0u64"
    val type_start =
      Position.make0 451 101000 0 "" ""
        "resolved-semantic-navigation-type"
    val type_source =
      Parser_Lex_Util.positioned_content_source
        type_text type_start
    val type_position =
      token_position type_text type_start "u64" 0
    val ((type_term, type_reports), during_type_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.capture (fn () =>
          Parser_Test_Elaboration.expression
            ctxt type_source))
    val _ =
      audit_assert "deferred type entity escaped before replay"
        (entity_names Markup.type_nameN
           type_position during_type_markup = [] andalso
         count_markup Markup.tconstN
           type_position during_type_markup = 0)
    val ((), replay_type_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.replay ctxt type_reports)
    val _ =
      audit_assert "deferred type entity target changed"
        (entity_names Markup.type_nameN
           type_position replay_type_markup =
             [word_type_name] andalso
         count_markup Markup.tconstN
           type_position replay_type_markup = 1)
    val _ =
      audit_assert "type-report elaboration retained a marker"
        (not (contains_navigation_marker type_term))

    val _ =
      audit_case 0 "addition" "1u32 + 2u32"
        [("+", 0,
          [\<^const_name>\<open>word_add_no_wrap\<close>])]
    val _ =
      audit_case 1 "boolean-negation" "!true"
        [("!", 0, [\<^const_name>\<open>negation\<close>])]
    val _ =
      audit_case 2 "word-negation" "!1u32"
        [("!", 0,
          [\<^const_name>\<open>Numeric_Types.word_bitwise_not\<close>])]
    val _ =
      audit_case 3 "iteration"
        "for item in [1u64] { let _ = item; () }"
        [("in", 0, [\<^const_name>\<open>list_into_iter\<close>])]
    val _ =
      audit_case 4 "scalar-index"
        "\<llangle>[1 :: nat]\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>list_index\<close>])]
    val _ =
      audit_case 5 "range-index"
        "\<llangle>[1 :: nat, 2]\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>list_index_range\<close>])]
    val _ =
      audit_case 6 "field-focus"
        "\<llangle>1 :: nat\<rrangle>.navigationField"
        [(".", 0,
          [\<^const_name>\<open>semantic_navigation_focus\<close>])]
    val _ =
      audit_case 7 "option-propagation"
        "\<llangle>Some (1 :: nat)\<rrangle>?"
        [("?", 0, [\<^const_name>\<open>propagate_option\<close>])]
    val _ =
      audit_case 8 "result-propagation"
        "\<llangle>(Ok (1 :: nat) :: (nat, String.literal) result)\<rrangle>?"
        [("?", 0, [\<^const_name>\<open>propagate_result\<close>])]
    val _ =
      audit_case 9 "allocation"
        "let mut slot = 0u32; slot"
        [("mut", 0,
          [\<^const_name>\<open>semantic_navigation_allocate\<close>])]
    val _ =
      audit_case 10 "dereference"
        "*semantic_navigation_ref"
        [("*", 0,
          [\<^const_name>\<open>semantic_navigation_dereference\<close>])]
    val _ =
      audit_case 11 "update"
        "semantic_navigation_ref = semantic_navigation_word"
        [("=", 0,
          [\<^const_name>\<open>semantic_navigation_update\<close>])]
    val _ =
      audit_case 12 "additive-assignment"
        "semantic_navigation_ref += semantic_navigation_word"
        [("+=", 0,
          [\<^const_name>\<open>semantic_navigation_assign_add\<close>])]
    val _ =
      audit_case 13 "compound-assignment"
        "semantic_navigation_ref -= semantic_navigation_word"
        [("-=", 0,
          [\<^const_name>\<open>word_minus_no_wrap\<close>,
           \<^const_name>\<open>semantic_navigation_update\<close>])]

    val _ =
      audit_case 14 "unsigned-cast" "0u64 as u8"
        [("as", 0, [ucast_name])]
    val _ =
      audit_case 15 "signed-cast" "0u64 as i32"
        [("as", 0, [scast_name])]
    val _ =
      audit_case 16 "raw-pointer-cast"
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u8"
        [("as", 0, [\<^const_name>\<open>raw_ptr_cast\<close>])]

    val _ =
      audit_case 17 "switch-match"
        "match 1u64 { 1 => true, _ => false }"
        [("match", 0, [\<^const_name>\<open>ncase_selector\<close>])]
    val _ =
      audit_case 18 "constructor-match"
        "match \<llangle>Some (1 :: nat)\<rrangle> { Some(value) => value, None => 0 }"
        [("match", 0,
          [\<^const_name>\<open>case_nil\<close>,
           \<^const_name>\<open>case_cons\<close>,
           \<^const_name>\<open>case_elem\<close>,
           \<^const_name>\<open>case_abs\<close>,
           \<^const_name>\<open>case_guard\<close>,
           \<^const_name>\<open>case_option\<close>])]

    val binary_audits =
      [("subtraction", "3u32 - 2u32", "-",
        \<^const_name>\<open>word_minus_no_wrap\<close>),
       ("multiplication", "3u32 * 2u32", "*",
        \<^const_name>\<open>word_mul_no_wrap\<close>),
       ("division", "4u32 / 2u32", "/",
        \<^const_name>\<open>word_udiv\<close>),
       ("remainder", "4u32 % 3u32", "%",
        \<^const_name>\<open>word_umod\<close>),
       ("shift-left", "1u32 << 2u64", "<<",
        \<^const_name>\<open>word_shift_left_shift64\<close>),
       ("shift-right", "4u32 >> 1u64", ">>",
        \<^const_name>\<open>word_shift_right_shift64\<close>),
       ("bitwise-and", "3u32 & 1u32", "&",
        \<^const_name>\<open>word_bitwise_and\<close>),
       ("bitwise-or", "2u32 | 1u32", "|",
        \<^const_name>\<open>word_bitwise_or\<close>),
       ("bitwise-xor", "3u32 ^ 1u32", "^",
        \<^const_name>\<open>word_bitwise_xor\<close>),
       ("equality", "1u32 == 1u32", "==",
        \<^const_name>\<open>urust_eq\<close>),
       ("inequality", "1u32 != 2u32", "!=",
        \<^const_name>\<open>urust_neq\<close>),
       ("less-than", "1u32 < 2u32", "<",
        \<^const_name>\<open>comp_lt\<close>),
       ("less-equal", "1u32 <= 2u32", "<=",
        \<^const_name>\<open>comp_le\<close>),
       ("greater-than", "2u32 > 1u32", ">",
        \<^const_name>\<open>comp_gt\<close>),
       ("greater-equal", "2u32 >= 1u32", ">=",
        \<^const_name>\<open>comp_ge\<close>),
       ("conjunction", "true && false", "&&",
        \<^const_name>\<open>urust_conj\<close>),
       ("disjunction", "true || false", "||",
        \<^const_name>\<open>urust_disj\<close>)]
    val _ =
      binary_audits
      |> map_index
          (fn (index, (label, text, token, target)) =>
            audit_case (30 + index) label text
              [(token, 0, [target])])
      |> ignore

    val assignment_audits =
      [("subtract-assignment", "-=", "semantic_navigation_word",
        \<^const_name>\<open>word_minus_no_wrap\<close>),
       ("multiply-assignment", "*=", "semantic_navigation_word",
        \<^const_name>\<open>word_mul_no_wrap\<close>),
       ("remainder-assignment", "%=", "semantic_navigation_word",
        \<^const_name>\<open>word_umod\<close>),
       ("and-assignment", "&=", "semantic_navigation_word",
        \<^const_name>\<open>word_bitwise_and\<close>),
       ("or-assignment", "|=", "semantic_navigation_word",
        \<^const_name>\<open>word_bitwise_or\<close>),
       ("xor-assignment", "^=", "semantic_navigation_word",
        \<^const_name>\<open>word_bitwise_xor\<close>),
       ("shift-left-assignment", "<<=", "semantic_navigation_shift",
        \<^const_name>\<open>word_shift_left_shift64\<close>),
       ("shift-right-assignment", ">>=", "semantic_navigation_shift",
        \<^const_name>\<open>word_shift_right_shift64\<close>)]
    val _ =
      assignment_audits
      |> map_index
          (fn (index, (label, token, rhs, arithmetic)) =>
            audit_case (50 + index) label
              ("semantic_navigation_ref " ^ token ^
                " " ^ rhs)
              [(token, 0,
                [arithmetic,
                 \<^const_name>\<open>semantic_navigation_update\<close>])])
      |> ignore

    val _ =
      audit_case 60 "list-scalar-index-pair"
        "\<llangle>[1 :: nat]\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>list_index\<close>]),
         ("]", 1, [\<^const_name>\<open>list_index\<close>])]
    val _ =
      audit_case 61 "list-range-index-pair"
        "\<llangle>[1 :: nat, 2]\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>list_index_range\<close>]),
         ("]", 1, [\<^const_name>\<open>list_index_range\<close>])]
    val _ =
      audit_case 62 "array-scalar-index-pair"
        "\<llangle>array_of_list [1 :: nat] :: (nat, 2) array\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>array_index\<close>]),
         ("]", 1, [\<^const_name>\<open>array_index\<close>])]
    val _ =
      audit_case 63 "array-range-index-pair"
        "\<llangle>array_of_list [1 :: nat, 2] :: (nat, 2) array\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>array_index_range\<close>]),
         ("]", 1, [\<^const_name>\<open>array_index_range\<close>])]
    val _ =
      audit_case 64 "vector-scalar-index-pair"
        "\<llangle>vector_of_list [1 :: nat] :: (nat, 2) vector\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>vector_index\<close>]),
         ("]", 1, [\<^const_name>\<open>vector_index\<close>])]
    val _ =
      audit_case 65 "vector-range-index-pair"
        "\<llangle>vector_of_list [1 :: nat, 2] :: (nat, 2) vector\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>vector_index_range\<close>]),
         ("]", 1, [\<^const_name>\<open>vector_index_range\<close>])]

    val _ =
      audit_case 66 "array-iteration"
        "for item in \<llangle>array_of_list [1 :: nat] :: (nat, 2) array\<rrangle> { () }"
        [("in", 0, [\<^const_name>\<open>array_into_iter\<close>])]
    val _ =
      audit_case 67 "vector-iteration"
        "for item in \<llangle>vector_of_list [1 :: nat] :: (nat, 2) vector\<rrangle> { () }"
        [("in", 0, [\<^const_name>\<open>vector_into_iter\<close>])]
    val _ =
      audit_case 68 "range-iteration"
        "for item in 0u64..1u64 { () }"
        [("in", 0, [\<^const_name>\<open>range_into_iter\<close>])]
    val _ =
      audit_case 69 "iterator-iteration"
        "for item in \<llangle>make_iterator_from_list [1 :: nat]\<rrangle> { () }"
        [("in", 0, [\<^const_name>\<open>iterator_into_iter\<close>])]

    val literal_target =
      [\<^const_name>\<open>Core_Expression.literal\<close>]
    val literal_audits =
      [("decimal-literal", "17u32", "17"),
       ("binary-literal", "0b1010u8", "0b1010"),
       ("octal-literal", "0o17_u16", "0o17"),
       ("hex-literal", "0xFFusize", "0xFF")]
    val _ =
      literal_audits
      |> map_index
          (fn (index, (label, text, numeric)) =>
            audit_case (70 + index) label text
              [(numeric, 0, literal_target)])
      |> ignore
    val _ =
      audit_type_token 74 "decimal-suffix" "17u32" "u32" 0
    val _ =
      audit_type_token 75 "binary-suffix" "0b1010u8" "u8" 0
    val _ =
      audit_type_token 76 "octal-suffix" "0o17_u16" "_u16" 0
    val _ =
      audit_type_token 77 "hex-suffix" "0xFFusize" "usize" 0
    val _ =
      audit_case 78 "string-literal" "\"navigation\""
        [("\"navigation\"", 0, literal_target)]
    val _ =
      audit_case 79 "value-antiquotation"
        "\<llangle>1 :: nat\<rrangle>"
        [("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target)]

    val _ =
      audit_type_token 80 "unsigned-cast-type"
        "0u64 as u8" "u8" 0
    val _ =
      audit_type_token 81 "signed-cast-type"
        "0u64 as i32" "i32" 0
    val _ =
      audit_type_token 82 "raw-pointer-cast-type"
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u8"
        "u8" 0
    val complete_cast_audits =
      [("unsigned-u8", "0u64 as u8", ucast_name),
       ("unsigned-u16", "0u64 as u16", ucast_name),
       ("unsigned-u32", "0u64 as u32", ucast_name),
       ("unsigned-u64", "0u64 as u64", ucast_name),
       ("unsigned-usize", "0u64 as usize", ucast_name),
       ("signed-i32", "0u64 as i32", scast_name),
       ("signed-i64", "0u64 as i64", scast_name),
       ("raw-const-u8",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u8",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-u16",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u16",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-u32",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u32",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-u64",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u64",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-usize",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const usize",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u8",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u8",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u16",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u16",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u32",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u32",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u64",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u64",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-usize",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut usize",
        \<^const_name>\<open>raw_ptr_cast\<close>)]
    val _ =
      complete_cast_audits
      |> map_index
          (fn (index, (label, text, target)) =>
            audit_case (110 + index) label text
              [("as", 0, [target])])
      |> ignore

    val _ =
      audit_case 83 "let-binding-sequence"
        "let value = 1u32; value"
        [(";", 0,
          [\<^const_name>\<open>Core_Expression.sequence\<close>])]
    val _ =
      audit_case 84 "const-binding-sequence"
        "const value = 1u32; value"
        [(";", 0,
          [\<^const_name>\<open>Core_Expression.sequence\<close>])]
    val _ =
      audit_case 85 "immutable-borrow"
        "&semantic_navigation_ref"
        [("&", 0, [\<^const_name>\<open>ro_ref_from_ref\<close>])]
    val _ =
      audit_case 86 "mutable-borrow"
        "& mut semantic_navigation_ref"
        [("&", 0, [\<^const_name>\<open>mut_ref_from_ref\<close>]),
         ("mut", 0, [\<^const_name>\<open>mut_ref_from_ref\<close>])]
    val _ =
      audit_case 87 "ordinary-repeat"
        "[1u32; 2usize]"
        [("[", 0, [\<^const_name>\<open>List.replicate\<close>]),
         (";", 0, [\<^const_name>\<open>List.replicate\<close>]),
         ("]", 0, [\<^const_name>\<open>List.replicate\<close>])]
    val _ =
      audit_case 88 "inline-const-repeat"
        "[const { 1u32 }; 2usize]"
        [("[", 0, [\<^const_name>\<open>List.replicate\<close>]),
         (";", 0, [\<^const_name>\<open>List.replicate\<close>]),
         ("const", 0, [\<^const_name>\<open>List.replicate\<close>]),
         ("]", 0, [\<^const_name>\<open>List.replicate\<close>])]
    val _ =
      audit_case 89 "primitive-log-antiquotations"
        "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[] :: log_data\<rrangle>"
        [("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target),
         ("\<llangle>", 1, literal_target),
         ("\<rrangle>", 1, literal_target)]
    val _ =
      audit_case 90 "log-data-antiquotation"
        "l\<llangle>\"left\", semantic_navigation_word\<rrangle>"
        [("l", 0, literal_target),
         ("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target),
         (",", 0, [])]
    val _ =
      audit_case 91 "macro-message-string"
        "panic!(\"navigation\")"
        [("\"navigation\"", 0, literal_target)]
    val _ =
      audit_case 92 "macro-message-antiquotation"
        "panic!(\<llangle>''navigation''\<rrangle>)"
        [("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target)]

    val _ =
      audit_case 93 "yield-link" "\<y>\<i>\<e>\<l>\<d>"
        [("\<y>\<i>\<e>\<l>\<d>", 0,
          [\<^const_name>\<open>pause\<close>])]
    val _ =
      audit_case 94 "erased-array-borrow" "&[1u32]"
        [("&", 0, [])]
    val _ =
      audit_case 100 "erased-mutable-array-borrow"
        "& mut [1u32]"
        [("&", 0, []), ("mut", 0, [])]
    val _ =
      audit_case 95 "method-dot"
        "\<llangle>[1 :: nat]\<rrangle>.into_iter()"
        [(".", 0, [])]
    val _ =
      audit_case 96 "group-and-block"
        "{ (1u32) }"
        [("{", 0, []), ("(", 0, []),
         (")", 0, []), ("}", 0, [])]
    val _ =
      audit_case 97 "match-alternative"
        "match \<llangle>Some (1 :: nat)\<rrangle> { Some(_) | None => () }"
        [("|", 0, [])]
    val _ =
      audit_case 98 "expression-antiquotation"
        "\<epsilon>\<open>literal (1 :: nat)\<close>"
        [("\<epsilon>", 0, []),
         ("\<open>", 0, []),
         ("\<close>", 0, [])]
    val _ =
      audit_case 101 "unsafe-erasure"
        "unsafe { 1u32 }"
        [("unsafe", 0, []), ("{", 0, []), ("}", 0, [])]
    val _ =
      audit_case 102 "switch-pattern-literal"
        "match 1u64 { 0x1 => true, _ => false }"
        [("0x1", 0, literal_target)]

    val bind_target =
      [\<^const_name>\<open>Core_Expression.bind\<close>]
    val sequence_target =
      [\<^const_name>\<open>Core_Expression.sequence\<close>]
    val funcall1_target =
      [\<^const_name>\<open>funcall1\<close>]
    val list_cons_target =
      [\<^const_name>\<open>List.Cons\<close>]
    val list_nil_target =
      [\<^const_name>\<open>List.Nil\<close>]
    val pair_target =
      [\<^const_name>\<open>Product_Type.Pair\<close>]
    val list_case_target =
      [\<^const_name>\<open>List.case_list\<close>]
    val bounded_while_target =
      [\<^const_name>\<open>bounded_while\<close>]
    val conditional_target =
      [\<^const_name>\<open>two_armed_conditional\<close>]
    val option_case_targets =
      [\<^const_name>\<open>case_nil\<close>,
       \<^const_name>\<open>case_cons\<close>,
       \<^const_name>\<open>case_elem\<close>,
       \<^const_name>\<open>case_abs\<close>,
       \<^const_name>\<open>case_guard\<close>,
       \<^const_name>\<open>case_option\<close>]

    val _ =
      audit_target_group 200 "empty-array-pair" "[]"
        [("[", 0), ("]", 0)] list_nil_target
    val _ =
      audit_target_group 201 "nonempty-array-pair" "[1u32]"
        [("[", 0), ("]", 0)] list_cons_target
    val _ =
      audit_target_group 202 "tuple-pair" "(1u32, 2u32)"
        [("(", 0), (")", 0)] pair_target
    val _ =
      audit_target_group 203 "struct-brace-pair"
        "semantic_navigation_allocate { value: 0u32 }"
        [("{", 0), ("}", 0)] funcall1_target
    val _ =
      audit_target_group 204 "ordinary-call-pair"
        "semantic_navigation_allocate(0u32)"
        [("(", 0), (")", 0)] funcall1_target
    val _ =
      audit_target_group 205 "method-call-pair"
        "\<llangle>[1 :: nat]\<rrangle>.into_iter()"
        [("(", 0), (")", 0)] funcall1_target
    val _ =
      audit_target_group 206 "erased-borrow-array-pair"
        "&[1u32]"
        [("[", 0), ("]", 0)] list_cons_target
    val _ =
      audit_case 207 "erased-borrow-array-prefix"
        "&[1u32]" [("&", 0, [])]
    val _ =
      audit_target_group 208 "erased-mutable-borrow-array-pair"
        "& mut [1u32]"
        [("[", 0), ("]", 0)] list_cons_target
    val _ =
      audit_case 209 "erased-mutable-borrow-array-prefix"
        "& mut [1u32]"
        [("&", 0, []), ("mut", 0, [])]

    val _ =
      audit_target_group 210 "let-binding-head"
        "let value = 1u32; value"
        [("let", 0), ("=", 0)] bind_target
    val _ =
      audit_case 211 "let-binding-separator"
        "let value = 1u32; value"
        [(";", 0, sequence_target)]
    val _ =
      audit_target_group 212 "mutable-binding-head"
        "let mut value = 1u32; value"
        [("let", 0), ("=", 0)] bind_target
    val _ =
      audit_case 213 "mutable-binding-roles"
        "let mut value = 1u32; value"
        [("mut", 0,
          [\<^const_name>\<open>semantic_navigation_allocate\<close>]),
         (";", 0, sequence_target)]
    val _ =
      audit_target_group 214 "const-binding-head"
        "const value = 1u32; value"
        [("const", 0), ("=", 0)] bind_target
    val _ =
      audit_case 215 "const-binding-separator"
        "const value = 1u32; value"
        [(";", 0, sequence_target)]

    val guarded_match_text =
      "match \<llangle>Some (1 :: nat)\<rrangle> { " ^
      "Some(value) if true => value, None => 0 }"
    val _ =
      audit_case 216 "guarded-match"
        guarded_match_text
        [("match", 0, option_case_targets),
         ("if", 0,
          [\<^const_name>\<open>two_armed_conditional\<close>])]

    val lhs_dereference_text =
      "*semantic_navigation_ref = semantic_navigation_word"
    val _ =
      audit_case 217 "lhs-dereference"
        lhs_dereference_text
        [("*", 0,
          [\<^const_name>\<open>semantic_navigation_dereference\<close>]),
         ("=", 0,
          [\<^const_name>\<open>semantic_navigation_update\<close>])]

    val boolean_pattern_text =
      "match \<llangle>Some True\<rrangle> { " ^
      "Some(true) => true, Some(false) => false, None => false }"
    val _ =
      audit_case 218 "boolean-patterns"
        boolean_pattern_text
        [("match", 0, option_case_targets),
         ("true", 0, literal_target),
         ("false", 0, literal_target)]
    val _ =
      audit_markup_count 219 "true-pattern-keyword-style"
        boolean_pattern_text "true" 0 Markup.keyword1N 1
    val _ =
      audit_markup_count 220 "false-pattern-keyword-style"
        boolean_pattern_text "false" 0 Markup.keyword1N 1

    val range_pattern_text =
      "match \<llangle>Some (2 :: nat)\<rrangle> { " ^
      "Some(1..=3) => true, _ => false }"
    val _ =
      audit_case 221 "range-pattern-match-scope"
        range_pattern_text
        [("match", 0, option_case_targets)]

    val _ =
      audit_case 227 "explicit-switch-match"
        "match_switch 1u64 { 1 => true, _ => false }"
        [("match_switch", 0,
          [\<^const_name>\<open>ncase_selector\<close>])]
    val string_match_text =
      "match_case \"ok\" { \"ok\" => true, _ => false }"
    val _ =
      audit_case 228 "string-match-case"
        string_match_text
        [("match_case", 0, conditional_target)]
    val antiquoted_value_match_text =
      "match \<llangle>2 :: nat\<rrangle> { " ^
      "\<llangle>2 :: nat\<rrangle> => true, _ => false }"
    val _ =
      audit_case 229 "antiquoted-value-match"
        antiquoted_value_match_text
        [("match", 0, conditional_target)]
    val boolean_disjunction_match_text =
      "match true { true | false => true }"
    val _ =
      audit_case 230 "boolean-disjunction-match"
        boolean_disjunction_match_text
        [("match", 0, conditional_target)]
    val top_level_range_match_text =
      "match_case \<llangle>2 :: nat\<rrangle> { " ^
      "1..=3 => true, _ => false }"
    val _ =
      audit_case 231 "top-level-range-match"
        top_level_range_match_text
        [("match_case", 0, conditional_target)]
    val guarded_value_match_text =
      "match_case \<llangle>2 :: nat\<rrangle> { " ^
      "\<llangle>2 :: nat\<rrangle> if true => true, _ => false }"
    val _ =
      audit_case 232 "guarded-value-match"
        guarded_value_match_text
        [("match_case", 0, conditional_target),
         ("if", 0, conditional_target)]
    val wildcard_match_text =
      "match_case 1u64 { _ => true }"
    val _ =
      audit_case 233 "irrefutable-wildcard-match"
        wildcard_match_text
        [("match_case", 0, bind_target)]
    val binder_match_text =
      "match_case \<llangle>1 :: nat\<rrangle> { value => value }"
    val _ =
      audit_case 234 "irrefutable-binder-match"
        binder_match_text
        [("match_case", 0, bind_target)]

    val top_slice_text =
      "match \<llangle>[1 :: nat, 2]\<rrangle> { " ^
      "[head, ..] => head, _ => 0 }"
    val _ =
      audit_target_group 222 "top-level-slice-navigation"
        top_slice_text
        [("[", 1), ("..", 0), ("]", 1)]
        list_case_target
    val nested_slice_text =
      "match \<llangle>Some [1 :: nat, 2]\<rrangle> { " ^
      "Some([head, ..]) => head, _ => 0 }"
    val _ =
      audit_target_group 223 "nested-slice-navigation"
        nested_slice_text
        [("[", 1), ("..", 0), ("]", 1)]
        list_case_target

    val while_text =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] " ^
      "while (false) { () }"
    val _ =
      audit_target_group 224 "fuelled-while-navigation"
        while_text
        [("#[", 0), ("fuel", 0), ("]", 0), ("while", 0)]
        bounded_while_target
    val while_let_text =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] " ^
      "while let Some(_) = " ^
      "\<llangle>None :: unit option\<rrangle> { () }"
    val _ =
      audit_target_group 225 "fuelled-while-let-navigation"
        while_let_text
        [("#[", 0), ("fuel", 0), ("]", 0), ("while", 0)]
        bounded_while_target
    val loop_text =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () }"
    val _ =
      audit_target_group 226 "fuelled-loop-navigation"
        loop_text
        [("#[", 0), ("fuel", 0), ("]", 0), ("loop", 0)]
        bounded_while_target

    val function_suffixes =
      ["\<^sub>1", "\<^sub>2", "\<^sub>3", "\<^sub>4",
       "\<^sub>5", "\<^sub>6", "\<^sub>7", "\<^sub>8",
       "\<^sub>9", "\<^sub>1\<^sub>0",
       "\<^sub>1\<^sub>1", "\<^sub>1\<^sub>2",
       "\<^sub>1\<^sub>3", "\<^sub>1\<^sub>4"]
    val lift_targets =
      [\<^const_name>\<open>lift_fun1\<close>,
       \<^const_name>\<open>lift_fun2\<close>,
       \<^const_name>\<open>lift_fun3\<close>,
       \<^const_name>\<open>lift_fun4\<close>,
       \<^const_name>\<open>lift_fun5\<close>,
       \<^const_name>\<open>lift_fun6\<close>,
       \<^const_name>\<open>lift_fun7\<close>,
       \<^const_name>\<open>lift_fun8\<close>,
       \<^const_name>\<open>lift_fun9\<close>,
       \<^const_name>\<open>lift_fun10\<close>,
       \<^const_name>\<open>lift_fun11\<close>,
       \<^const_name>\<open>lift_fun12\<close>,
       \<^const_name>\<open>lift_fun13\<close>,
       \<^const_name>\<open>lift_fun14\<close>]
    val function_parameters =
      ["a", "b", "c", "d", "e", "f", "g",
       "h", "i", "j", "k", "l", "m", "n"]

    fun function_literal_text arity suffix =
      let
        val parameters = take arity function_parameters
        val first = hd parameters
      in
        "\<llangle>\<lambda>" ^
        space_implode " " parameters ^
        ". (" ^ first ^ " :: nat)\<rrangle>" ^
        suffix ^ "(" ^
        space_implode ", " (replicate arity "0") ^ ")"
      end

    val _ =
      (function_suffixes ~~ lift_targets)
      |> map_index
          (fn (index, (suffix, target)) =>
            let
              val arity = index + 1
              val label =
                "function-literal-arity-" ^
                string_of_int arity
              val text =
                function_literal_text arity suffix
            in
              audit_target_group (240 + index)
                label text
                [("\<llangle>", 0), ("\<rrangle>", 0),
                 (suffix, 0)]
                [target];
              audit_term_invariant (260 + index)
                (label ^ "-term") text
            end)
      |> ignore

    val invariant_sources =
      [("empty-array", "[]"),
       ("nonempty-array", "[1u32]"),
       ("tuple", "(1u32, 2u32)"),
       ("struct",
        "semantic_navigation_allocate { value: 0u32 }"),
       ("ordinary-call",
        "semantic_navigation_allocate(0u32)"),
       ("method-call",
        "\<llangle>[1 :: nat]\<rrangle>.into_iter()"),
       ("erased-array-borrow", "&[1u32]"),
       ("erased-mutable-array-borrow", "& mut [1u32]"),
       ("let-binding", "let value = 1u32; value"),
       ("mutable-binding", "let mut value = 1u32; value"),
       ("const-binding", "const value = 1u32; value"),
       ("guarded-match", guarded_match_text),
       ("lhs-dereference", lhs_dereference_text),
       ("boolean-patterns", boolean_pattern_text),
       ("range-pattern", range_pattern_text),
       ("explicit-switch-match",
        "match_switch 1u64 { 1 => true, _ => false }"),
       ("string-match-case", string_match_text),
       ("antiquoted-value-match",
        antiquoted_value_match_text),
       ("boolean-disjunction-match",
        boolean_disjunction_match_text),
       ("top-level-range-match",
        top_level_range_match_text),
       ("guarded-value-match",
        guarded_value_match_text),
       ("irrefutable-wildcard-match",
        wildcard_match_text),
       ("irrefutable-binder-match",
        binder_match_text),
       ("top-level-slice", top_slice_text),
       ("nested-slice", nested_slice_text),
       ("fuelled-while", while_text),
       ("fuelled-while-let", while_let_text),
       ("fuelled-loop", loop_text)]
    val _ =
      invariant_sources
      |> map_index
          (fn (index, (label, text)) =>
            audit_term_invariant (280 + index)
              (label ^ "-invariant") text)
      |> ignore

    fun audit_registered_macro serial label text notation expected_backend
        expected_keyword3 =
      let
        val {start, markup, ...} =
          capture serial label text
        val qualifier =
          if String.isSubstring "NavigationMacro" text
          then SOME (token_position text start "NavigationMacro" 0)
          else NONE
        val terminal =
          token_position text start label 0
        val bang = token_position text start "!" 0
      in
        Option.app
          (fn position =>
            audit_assert
              (label ^ " qualifier lost notation navigation")
              (entity_names Micro_Rust_Names.notationN
                position markup = [notation]))
          qualifier;
        audit_assert (label ^ " terminal lost notation navigation")
          (entity_names Micro_Rust_Names.notationN
            terminal markup = [notation]);
        audit_assert (label ^ " bang acquired notation navigation")
          (entity_names Micro_Rust_Names.notationN
            bang markup = []);
        audit_assert (label ^ " terminal backend target changed")
          (constant_targets terminal markup = expected_backend);
        audit_assert (label ^ " bang backend target changed")
          (constant_targets bang markup = expected_backend);
        audit_assert (label ^ " keyword3 styling changed")
          (count_markup Markup.keyword3N terminal markup =
            expected_keyword3)
      end

    val _ =
      audit_registered_macro 19 "named"
        "NavigationMacro::named!(true)"
        "NavigationMacro::named!"
        [\<^const_name>\<open>semantic_navigation_named_macro\<close>] 1
    val _ =
      audit_registered_macro 20 "abbrev"
        "NavigationMacro::abbrev!(true)"
        "NavigationMacro::abbrev!"
        [abbreviation_name] 1
    val _ =
      audit_registered_macro 21 "anonymous"
        "NavigationMacro::anonymous!(true)"
        "NavigationMacro::anonymous!"
        [] 1
    val _ =
      audit_registered_macro 99 "info"
        "info!(l\<llangle>\"navigation\"\<rrangle>)"
        "info!"
        [info_name] 1

    val failure_text = "1u32 + true"
    val failure_start =
      Position.make0 700 300000 0 "" ""
        "resolved-semantic-navigation-failure"
    val failure_source =
      Parser_Lex_Util.positioned_content_source
        failure_text failure_start
    val (failure_result, failure_markup) =
      Parser_Test_Reports.markup (fn () =>
        Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression
              ctxt failure_source)
          ())
    val _ =
      (case failure_result of
         Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ()
       | Exn.Res _ =>
           error
             "resolved semantic navigation audit: failing expression elaborated")
    val _ =
      List.app
        (fn (needle, occurrence) =>
          let
            val position =
              token_position failure_text failure_start
                needle occurrence
          in
            audit_assert
              ("failed elaboration replayed a target at " ^
                quote needle)
              (constant_targets position failure_markup = [] andalso
               count_markup Markup.constN
                 position failure_markup = 0)
          end)
        [("1", 0), ("u32", 0), ("+", 0), ("true", 0)]
    val failure_type_position =
      token_position failure_text failure_start "u32" 0
    val _ =
      audit_assert "failed elaboration replayed a type target"
        (entity_names Markup.type_nameN
           failure_type_position failure_markup = [] andalso
         count_markup Markup.tconstN
           failure_type_position failure_markup = 0)

    val marker_names =
      [\<^const_name>\<open>semantic_navigation_target\<close>,
       \<^const_name>\<open>semantic_navigation_annotation\<close>,
       \<^const_name>\<open>semantic_navigation_probe\<close>]
    val _ =
      List.app
        (fn marker_name =>
          (case
              Exn.result (Syntax.check_term ctxt)
                (Const (marker_name, dummyT)) of
             Exn.Exn exn =>
               if Exn.is_interrupt exn
               then Exn.reraise exn
               else ()
           | Exn.Res _ =>
               error
                 ("resolved semantic navigation audit: " ^
                   "internal marker " ^ quote marker_name ^
                   " survived checking")))
        marker_names
  in
    val _ =
      writeln
        "Checked exact-range overload, delimiter, binding, case, slice, loop, macro, transaction, failure, term-invariance, and marker-erasure navigation audits passed"
  end
\<close>

end
