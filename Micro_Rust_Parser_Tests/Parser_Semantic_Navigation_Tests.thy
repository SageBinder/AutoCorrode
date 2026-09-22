theory Parser_Semantic_Navigation_Tests
  imports Parser_Test_Utils
begin

declare [[urust_conformance = false]]
declare [[urust_verbosity = 0]]

section\<open>Deferred shallow-term targets\<close>

ML_val\<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("semantic navigation target audit: " ^ message)

    fun collect_markup_order (XML.Text _) = []
      | collect_markup_order (XML.Elem (markup, body)) =
          markup :: maps collect_markup_order body

    fun capture_markup label action =
      let
        val captured =
          Synchronized.var
            ("semantic_navigation_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured
            (fn current => current @ chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ())
              ())
        val markup =
          Synchronized.value captured
          |> maps YXML.parse_body
          |> maps collect_markup_order
      in (result, markup) end

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle)
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

    fun constant_targets position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN =
                  SOME Markup.constantN andalso
                has_position properties position
            then Properties.get properties Markup.nameN
            else NONE)

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    val source_text = "panic!"
    val source_start =
      Position.make0 410 97000 0 "" ""
        "semantic-navigation-target-audit"
    val panic_position =
      token_position source_text source_start "panic" 0
    val bang_position =
      token_position source_text source_start "!" 0
    val message = Free ("semantic_navigation_message", dummyT)

    val (((), reports), during_markup) =
      capture_markup "capture" (fn () =>
        Navigation.capture (fn () =>
          (Navigation.defer_report ctxt bang_position Markup.keyword3;
           Navigation.with_source
             [panic_position, bang_position, panic_position]
             (fn () =>
               (ignore (URust_Shallow_Terms.panic_message message);
                ignore (URust_Shallow_Terms.panic_message message))))))
    val _ =
      List.app
        (fn (label, position) =>
          (audit_assert
             (label ^ " emitted targets before replay")
             (constant_targets position during_markup = []);
           audit_assert
             (label ^ " emitted constant styling before replay")
             (count_markup Markup.constN
                position during_markup = 0)))
        [("panic token", panic_position),
         ("bang token", bang_position)]
    val _ =
      audit_assert "generic markup was not deferred"
        (count_markup Markup.keyword3N
          bang_position during_markup = 0)

    val ((), replay_markup) =
      capture_markup "replay" (fn () =>
        Navigation.replay ctxt reports)
    val expected_targets =
      [\<^const_name>\<open>abort\<close>,
       \<^const_name>\<open>Panic\<close>]
    val _ =
      List.app
        (fn (label, position) =>
          (audit_assert
             (label ^
              " target order, stable deduplication, or primary-last " ^
              "classification changed")
             (constant_targets position replay_markup =
               expected_targets);
           audit_assert
             (label ^ " native constant styling count changed")
             (count_markup Markup.constN
                position replay_markup = 2)))
        [("panic token", panic_position),
         ("bang token", bang_position)]
    val _ =
      audit_assert "generic deferred markup was not replayed"
        (count_markup Markup.keyword3N
          bang_position replay_markup = 1)

    val (failure_result, failure_markup) =
      capture_markup "failure" (fn () =>
        Exn.result
          (fn () =>
            Navigation.capture (fn () =>
              Navigation.with_source_position panic_position
                (fn () =>
                  (ignore
                    (URust_Shallow_Terms.panic_message message);
                   error "intentional semantic navigation failure"))))
          ())
    val _ =
      (case failure_result of
         Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ()
       | Exn.Res _ =>
           error
             ("semantic navigation target audit: " ^
              "intentional failure unexpectedly succeeded"))
    val _ =
      audit_assert "failed capture leaked semantic targets"
        (constant_targets panic_position failure_markup = [] andalso
         count_markup Markup.constN panic_position failure_markup = 0)
  in
    val _ =
      writeln
        "Deferred target order, exact ranges, deduplication, native markup, generic replay, and failure isolation passed"
  end
\<close>


section\<open>Registered macro bang targets\<close>

definition semantic_navigation_named_macro ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_named_macro =
        lift_fun1 (\<lambda>value. value)
    \<close>

micro_rust_notation (call)
  semantic_navigation_named_macro
  ("NavigationMacro::named!")

micro_rust_notation (call)
  \<open>lift_fun1 (\<lambda>value :: bool. value)\<close>
  ("NavigationMacro::anonymous!")

ML_val\<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("registered macro bang target audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle)
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

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    fun capture serial label text =
      let
        val start =
          Position.make0 (430 + serial) (99000 + serial * 500) 0 "" ""
            ("registered-macro-" ^ label ^ "-target-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (term, markup) =
          Parser_Test_Reports.markup (fn () =>
            Parser_Test_Elaboration.expression ctxt source)
      in (start, term, markup) end

    val named_text = "NavigationMacro::named!(true)"
    val (named_start, named_term, named_markup) =
      capture 0 "named" named_text
    val named_qualifier =
      token_position named_text named_start "NavigationMacro" 0
    val named_terminal =
      token_position named_text named_start "named"
        (size "NavigationMacro::")
    val named_bang =
      token_position named_text named_start "!" 0
    val named_notation = "NavigationMacro::named!"
    val _ =
      audit_assert "named qualifier lost notation navigation"
        (entity_names Micro_Rust_Names.notationN
          named_qualifier named_markup = [named_notation])
    val _ =
      audit_assert "named identifier lost notation navigation"
        (entity_names Micro_Rust_Names.notationN
          named_terminal named_markup = [named_notation])
    val _ =
      audit_assert "named bang acquired notation navigation"
        (entity_names Micro_Rust_Names.notationN
          named_bang named_markup = [])
    val _ =
      audit_assert "named bang target changed"
        (entity_names Markup.constantN named_bang named_markup =
          [\<^const_name>\<open>semantic_navigation_named_macro\<close>])
    val _ =
      audit_assert "named bang constant styling changed"
        (count_markup Markup.constN named_bang named_markup = 1)
    val _ =
      audit_assert "named backend term changed"
        (Term.exists_subterm
          (fn Const (name, _) =>
                name =
                  \<^const_name>\<open>semantic_navigation_named_macro\<close>
            | _ => false)
          named_term)

    val deferred_start =
      Position.make0 432 100000 0 "" ""
        "registered-macro-deferred-target-audit"
    val deferred_source =
      Parser_Lex_Util.positioned_content_source
        named_text deferred_start
    val ((_, deferred_reports), during_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.capture (fn () =>
          Parser_Test_Elaboration.expression ctxt deferred_source))
    val deferred_terminal =
      token_position named_text deferred_start "named"
        (size "NavigationMacro::")
    val deferred_bang =
      token_position named_text deferred_start "!" 0
    val _ =
      audit_assert "selected notation escaped deferred capture"
        (entity_names Micro_Rust_Names.notationN
          deferred_terminal during_markup = [])
    val _ =
      audit_assert "selected bang target escaped deferred capture"
        (entity_names Markup.constantN
          deferred_bang during_markup = [] andalso
         count_markup Markup.constN
          deferred_bang during_markup = 0)
    val ((), deferred_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.replay ctxt deferred_reports)
    val _ =
      audit_assert "selected notation was not replayed"
        (entity_names Micro_Rust_Names.notationN
          deferred_terminal deferred_markup = [named_notation])
    val _ =
      audit_assert "selected bang target was not replayed"
        (entity_names Markup.constantN
          deferred_bang deferred_markup =
            [\<^const_name>\<open>semantic_navigation_named_macro\<close>] andalso
         count_markup Markup.constN
          deferred_bang deferred_markup = 1)

    val anonymous_text =
      "NavigationMacro::anonymous!(true)"
    val (anonymous_start, _, anonymous_markup) =
      capture 1 "anonymous" anonymous_text
    val anonymous_qualifier =
      token_position anonymous_text anonymous_start
        "NavigationMacro" 0
    val anonymous_terminal =
      token_position anonymous_text anonymous_start
        "anonymous" (size "NavigationMacro::")
    val anonymous_bang =
      token_position anonymous_text anonymous_start "!" 0
    val anonymous_notation = "NavigationMacro::anonymous!"
    val _ =
      audit_assert "anonymous qualifier lost notation navigation"
        (entity_names Micro_Rust_Names.notationN
          anonymous_qualifier anonymous_markup =
          [anonymous_notation])
    val _ =
      audit_assert "anonymous identifier lost notation navigation"
        (entity_names Micro_Rust_Names.notationN
          anonymous_terminal anonymous_markup =
          [anonymous_notation])
    val _ =
      audit_assert "anonymous bang acquired notation navigation"
        (entity_names Micro_Rust_Names.notationN
          anonymous_bang anonymous_markup = [])
    val _ =
      audit_assert "anonymous bang acquired a false constant target"
        (entity_names Markup.constantN
          anonymous_bang anonymous_markup = [])
    val _ =
      audit_assert "anonymous bang acquired constant styling"
        (count_markup Markup.constN
          anonymous_bang anonymous_markup = 0)
  in
    val _ =
      writeln
        "Registered macro identifier navigation and distinct named-or-unlinked bang targets passed"
  end
\<close>

section\<open>Surface denotation navigation\<close>

definition semantic_navigation_call0 ::
    \<open>(unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_call0 =
        FunctionBody (literal 7)
    \<close>

definition semantic_navigation_plain_macro ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_plain_macro =
        lift_fun1 (\<lambda>value. value)
    \<close>

definition semantic_navigation_field ::
    \<open>(nat, nat) lens\<close>
  where
    \<open> semantic_navigation_field = id\<^sub>L \<close>

micro_rust_notation (call)
  semantic_navigation_plain_macro
  ("NavigationPlain!")

micro_rust_notation (field)
  semantic_navigation_field
  ("navigationField")

consts
  semantic_navigation_ref ::
    \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  semantic_navigation_word :: \<open>32 word\<close>

ML_val\<open>
  local
    open URust_AST
    structure Navigation = Micro_Rust_Semantic_Navigation

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("surface semantic navigation audit: " ^ message)

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

    fun constant_targets position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN =
                  SOME Markup.constantN andalso
                has_position properties position
            then Properties.get properties Markup.nameN
            else NONE)

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    fun head_constant_name label term =
      (case Term.head_of (Term_Position.strip_positions term) of
         Const (name, _) => name
       | head =>
           error
             ("surface semantic navigation audit: " ^
               label ^ " has non-constant head " ^
               Syntax.string_of_term ctxt head))

    val ucastu8_name =
      head_constant_name "ucastu8" \<^term>\<open>ucastu8\<close>
    val ucastu16_name =
      head_constant_name "ucastu16" \<^term>\<open>ucastu16\<close>
    val ucastu32_name =
      head_constant_name "ucastu32" \<^term>\<open>ucastu32\<close>
    val ucastu64_name =
      head_constant_name "ucastu64" \<^term>\<open>ucastu64\<close>
    val ucasti32_name =
      head_constant_name "ucasti32" \<^term>\<open>ucasti32\<close>
    val ucasti64_name =
      head_constant_name "ucasti64" \<^term>\<open>ucasti64\<close>
    val raw_ptr_cast_u8_name =
      head_constant_name
        "raw_ptr_cast_u8" \<^term>\<open>raw_ptr_cast_u8\<close>
    val raw_ptr_cast_u16_name =
      head_constant_name
        "raw_ptr_cast_u16" \<^term>\<open>raw_ptr_cast_u16\<close>
    val raw_ptr_cast_u32_name =
      head_constant_name
        "raw_ptr_cast_u32" \<^term>\<open>raw_ptr_cast_u32\<close>
    val raw_ptr_cast_u64_name =
      head_constant_name
        "raw_ptr_cast_u64" \<^term>\<open>raw_ptr_cast_u64\<close>
    val tuple_index_0_name =
      head_constant_name
        "tuple_index_0" \<^term>\<open>tuple_index_0\<close>

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE =>
           error "surface semantic navigation audit: empty parse")

    fun capture serial label text =
      let
        val start =
          Position.make0 (500 + serial) (120000 + serial * 1000)
            0 "" "" ("surface-semantic-navigation-" ^ label)
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val ((term, reports), during_markup) =
          Parser_Test_Reports.markup (fn () =>
            Navigation.capture (fn () =>
              URust_Translate.mk_expression ctxt [] (parse source)))
        val ((), replay_markup) =
          Parser_Test_Reports.markup (fn () =>
            Navigation.replay ctxt reports)
      in
        {start = start, term = term,
         during = during_markup, replay = replay_markup}
      end

    fun capture_checked serial label text =
      let
        val start =
          Position.make0 (700 + serial) (300000 + serial * 1000)
            0 "" "" ("checked-semantic-navigation-" ^ label)
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (term, markup) =
          Parser_Test_Reports.markup (fn () =>
            Parser_Test_Elaboration.expression ctxt source)
      in {start = start, term = term, markup = markup} end

    fun audit_case serial label text specifications =
      let
        val {start, during, replay, ...} =
          capture serial label text
        fun check (needle, occurrence, expected) =
          let
            val position =
              token_position text start needle occurrence
            val actual = constant_targets position replay
          in
            audit_assert
              (label ^ " target changed at " ^
                quote needle ^ " occurrence " ^
                string_of_int occurrence ^
                ": expected " ^
                commas_quote expected ^
                ", found " ^ commas_quote actual)
              (actual = expected);
            audit_assert
              (label ^ " emitted a denotation before replay")
              (constant_targets position during = []);
            audit_assert
              (label ^ " native constant styling changed")
              (count_markup Markup.constN position replay =
                length expected)
          end
      in List.app check specifications end

    fun audit_case_trace serial label text needle occurrence =
      let
        val {start, replay, ...} =
          capture serial label text
        val position =
          token_position text start needle occurrence
        val actual = constant_targets position replay
        val secondary =
          [\<^const_name>\<open>case_nil\<close>,
           \<^const_name>\<open>case_cons\<close>,
           \<^const_name>\<open>case_elem\<close>,
           \<^const_name>\<open>case_abs\<close>]
      in
        audit_assert (label ^ " lost its selected case constants")
          (List.all (member (op =) actual) secondary);
        audit_assert (label ^ " root selector is not primary-last")
          (not (null actual) andalso
           List.last actual = \<^const_name>\<open>case_guard\<close>);
        actual
      end

    val binary_cases =
      [("+", \<^const_name>\<open>urust_add\<close>),
       ("-", \<^const_name>\<open>word_minus_no_wrap\<close>),
       ("*", \<^const_name>\<open>word_mul_no_wrap\<close>),
       ("/", \<^const_name>\<open>word_udiv\<close>),
       ("%", \<^const_name>\<open>word_umod\<close>),
       ("<<", \<^const_name>\<open>word_shift_left_shift64\<close>),
       (">>", \<^const_name>\<open>word_shift_right_shift64\<close>),
       ("&", \<^const_name>\<open>word_bitwise_and\<close>),
       ("|", \<^const_name>\<open>word_bitwise_or\<close>),
       ("^", \<^const_name>\<open>word_bitwise_xor\<close>),
       ("==", \<^const_name>\<open>urust_eq\<close>),
       ("!=", \<^const_name>\<open>urust_neq\<close>),
       ("<", \<^const_name>\<open>comp_lt\<close>),
       ("<=", \<^const_name>\<open>comp_le\<close>),
       (">", \<^const_name>\<open>comp_gt\<close>),
       (">=", \<^const_name>\<open>comp_ge\<close>),
       ("&&", \<^const_name>\<open>urust_conj\<close>),
       ("||", \<^const_name>\<open>urust_disj\<close>)]
    val _ =
      binary_cases
      |> map_index
          (fn (index, (operator, target)) =>
            audit_case (index + 10)
              ("binary-" ^ string_of_int index)
              ("1u32 " ^ operator ^ " 2u32")
              [(operator, 0, [target])])
      |> List.app I

    val unary_cases =
      [("unary-not", "!true", "!", 0,
        [\<^const_name>\<open>negation_const\<close>]),
       ("unary-borrow", "&true", "&", 0,
        [\<^const_name>\<open>ro_ref_from_ref\<close>]),
       ("unary-mut-borrow", "& mut true", "&", 0,
        [\<^const_name>\<open>mut_ref_from_ref\<close>]),
       ("unary-deref", "*semantic_navigation_ref", "*", 0,
        [\<^const_name>\<open>store_dereference_const\<close>]),
       ("unary-propagate",
        "\<llangle>Some (1 :: nat)\<rrangle>?", "?", 0,
        [\<^const_name>\<open>propagate_const\<close>])]
    val _ =
      unary_cases
      |> map_index
          (fn (index, (label, text, token, occurrence, targets)) =>
            audit_case (index + 40) label text
              [(token, occurrence, targets)])
      |> List.app I

    val cast_cases =
      [("u8", ucastu8_name),
       ("u16", ucastu16_name),
       ("u32", ucastu32_name),
       ("u64", ucastu64_name),
       ("usize", ucastu64_name),
       ("i32", ucasti32_name),
       ("i64", ucasti64_name),
       ("*const u8", raw_ptr_cast_u8_name),
       ("*const u16", raw_ptr_cast_u16_name),
       ("*const u32", raw_ptr_cast_u32_name),
       ("*const u64", raw_ptr_cast_u64_name),
       ("*const usize", raw_ptr_cast_u64_name),
       ("*mut u8", raw_ptr_cast_u8_name),
       ("*mut u16", raw_ptr_cast_u16_name),
       ("*mut u32", raw_ptr_cast_u32_name),
       ("*mut u64", raw_ptr_cast_u64_name),
       ("*mut usize", raw_ptr_cast_u64_name)]
    val _ =
      cast_cases
      |> map_index
          (fn (index, (target, constant)) =>
            audit_case (index + 50)
              ("cast-" ^ string_of_int index)
              ("0u64 as " ^ target)
              [("as", 0, [constant])])
      |> List.app I

    val assignment_cases =
      [("=", [\<^const_name>\<open>store_update_const\<close>]),
       ("+=", [\<^const_name>\<open>assign_add_const\<close>]),
       ("-=", [\<^const_name>\<open>word_minus_no_wrap\<close>,
               \<^const_name>\<open>store_update_const\<close>]),
       ("*=", [\<^const_name>\<open>word_mul_no_wrap\<close>,
               \<^const_name>\<open>store_update_const\<close>]),
       ("%=", [\<^const_name>\<open>word_umod\<close>,
               \<^const_name>\<open>store_update_const\<close>]),
       ("&=", [\<^const_name>\<open>word_bitwise_and\<close>,
               \<^const_name>\<open>store_update_const\<close>]),
       ("|=", [\<^const_name>\<open>word_bitwise_or\<close>,
               \<^const_name>\<open>store_update_const\<close>]),
       ("^=", [\<^const_name>\<open>word_bitwise_xor\<close>,
               \<^const_name>\<open>store_update_const\<close>]),
       ("<<=", [\<^const_name>\<open>word_shift_left_shift64\<close>,
                \<^const_name>\<open>store_update_const\<close>]),
       (">>=", [\<^const_name>\<open>word_shift_right_shift64\<close>,
                \<^const_name>\<open>store_update_const\<close>])]
    val _ =
      assignment_cases
      |> map_index
          (fn (index, (operator, targets)) =>
            audit_case (index + 70)
              ("assignment-" ^ string_of_int index)
              ("semantic_navigation_ref " ^ operator ^
                " semantic_navigation_word")
              [(operator, 0, targets)])
      |> List.app I

    val _ =
      audit_case 90 "booleans" "(true, false)"
        [("true", 0, [\<^const_name>\<open>Bool_Type.true\<close>]),
         ("false", 0, [\<^const_name>\<open>Bool_Type.false\<close>]),
         ("(", 0, [\<^const_name>\<open>Product_Type.Pair\<close>])]
    val _ =
      audit_case 91 "bindings"
        "let mut slot = 0u32; const saved = slot; saved"
        [("let", 0, [\<^const_name>\<open>Core_Expression.bind\<close>]),
         ("mut", 0, [\<^const_name>\<open>store_reference_const\<close>]),
         ("const", 0, [\<^const_name>\<open>Core_Expression.bind\<close>])]
    val _ =
      audit_case 92 "sequencing-return-yield"
        "return { \<y>\<i>\<e>\<l>\<d>; () }"
        [("return", 0, [\<^const_name>\<open>return_func\<close>]),
         ("\<y>\<i>\<e>\<l>\<d>", 0,
          [\<^const_name>\<open>pause\<close>]),
         (";", 0, [\<^const_name>\<open>Core_Expression.sequence\<close>])]
    val _ =
      audit_case 93 "conditional"
        "if true { 1u32 } else { 2u32 }"
        [("if", 0, [\<^const_name>\<open>two_armed_conditional\<close>]),
         ("else", 0, [\<^const_name>\<open>two_armed_conditional\<close>])]
    val _ =
      audit_case 94 "while"
        "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) { () }"
        [("fuel", 0, [\<^const_name>\<open>bounded_while\<close>]),
         ("while", 0, [\<^const_name>\<open>bounded_while\<close>])]
    val _ =
      audit_case 95 "loop"
        "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () }"
        [("fuel", 0, [\<^const_name>\<open>bounded_while\<close>]),
         ("loop", 0, [\<^const_name>\<open>bounded_while\<close>])]
    val _ =
      audit_case 96 "for"
        "for item in [1u64] { let _ = item; () }"
        [("for", 0, [\<^const_name>\<open>for_loop\<close>]),
         ("in", 0, [\<^const_name>\<open>into_iter\<close>])]
    val _ =
      audit_case 97 "call"
        "semantic_navigation_call0()"
        [("(", 0, [\<^const_name>\<open>funcall0\<close>])]
    val _ =
      audit_case 98 "closure" "|value| value"
        [("|", 0, [\<^const_name>\<open>FunctionBody\<close>]),
         ("|", 1, [\<^const_name>\<open>FunctionBody\<close>])]
    val _ =
      audit_case 99 "arrays-tuples"
        "([1u64, 2u64], [])"
        [("(", 0, [\<^const_name>\<open>Product_Type.Pair\<close>]),
         ("[", 0, [\<^const_name>\<open>List.Cons\<close>]),
         ("[", 1, [\<^const_name>\<open>List.Nil\<close>])]
    val _ =
      audit_case 100 "ordinary-repeat" "[1u64; 3usize]"
        [(";", 0, [\<^const_name>\<open>List.replicate\<close>])]
    val _ =
      audit_case 101 "inline-repeat"
        "[const { Some(1u64) }; 3usize]"
        [("const", 0, [\<^const_name>\<open>List.replicate\<close>]),
         (";", 0, [\<^const_name>\<open>List.replicate\<close>])]
    val _ =
      audit_case 102 "ranges"
        "(1u64..2u64, 1u64..=2u64)"
        [("..", 0, [\<^const_name>\<open>range_new\<close>]),
         ("..=", 0, [\<^const_name>\<open>range_eq_new\<close>])]
    val _ =
      audit_case 103 "index"
        "\<llangle>[1 :: nat]\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>index_const\<close>])]
    val _ =
      audit_case 104 "projection"
        "\<llangle>(1 :: nat, 2 :: nat)\<rrangle>.0"
        [("0", 0, [tuple_index_0_name])]
    val _ =
      audit_case 105 "field"
        "\<llangle>1 :: nat\<rrangle>.navigationField"
        [(".", 0, [\<^const_name>\<open>focus_lens_const\<close>])]

    val switch_targets =
      let
        val text =
          "match 1u64 { 1 => true, _ => false }"
        val {start, replay, ...} =
          capture 106 "auto-switch" text
      in
        constant_targets
          (token_position text start "match" 0) replay
      end
    val _ =
      audit_assert "auto numeral match stopped selecting ncase_selector"
        (switch_targets =
          [\<^const_name>\<open>ncase_selector\<close>])
    val case_targets =
      audit_case_trace 107 "auto-case"
        "match \<llangle>Some (1 :: nat)\<rrangle> { Some(value) => value, None => 0 }"
        "match" 0
    val _ =
      audit_assert "similar auto matches no longer select distinct targets"
        (switch_targets <> case_targets)
    val _ =
      audit_case 108 "explicit-switch"
        "match_switch 1u64 { 1 => true, _ => false }"
        [("match_switch", 0,
          [\<^const_name>\<open>ncase_selector\<close>])]
    val _ =
      ignore
        (audit_case_trace 109 "if-let"
          "if let Some(value) = \<llangle>Some (1 :: nat)\<rrangle> { value } else { 0 }"
          "if" 0)
    val _ =
      ignore
        (audit_case_trace 110 "while-let"
          "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) = \<llangle>Some (1 :: nat)\<rrangle> { () }"
          "let" 0)
    val _ =
      audit_case 111 "while-let-loop-target"
        "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) = \<llangle>Some (1 :: nat)\<rrangle> { () }"
        [("fuel", 0, [\<^const_name>\<open>bounded_while\<close>]),
         ("while", 0, [\<^const_name>\<open>bounded_while\<close>])]

    val macro_cases =
      [("assert", "assert!(true)",
        [\<^const_name>\<open>assert\<close>]),
       ("debug_assert", "debug_assert!(true)",
        [\<^const_name>\<open>assert\<close>]),
       ("assert_eq", "assert_eq!(true, true)",
        [\<^const_name>\<open>assert_eq\<close>]),
       ("debug_assert_eq", "debug_assert_eq!(true, true)",
        [\<^const_name>\<open>assert_eq\<close>]),
       ("assert_ne", "assert_ne!(true, false)",
        [\<^const_name>\<open>assert_ne\<close>]),
       ("debug_assert_ne", "debug_assert_ne!(true, false)",
        [\<^const_name>\<open>assert_ne\<close>]),
       ("panic", "panic!()",
        [\<^const_name>\<open>abort\<close>,
         \<^const_name>\<open>Panic\<close>]),
       ("unreachable", "unreachable!()",
        [\<^const_name>\<open>abort\<close>,
         \<^const_name>\<open>Panic\<close>]),
       ("fatal", "fatal!()",
        [\<^const_name>\<open>fatal\<close>]),
       ("unimplemented", "unimplemented!()",
        [\<^const_name>\<open>abort\<close>,
         \<^const_name>\<open>Unimplemented\<close>]),
       ("todo", "todo!()",
        [\<^const_name>\<open>abort\<close>,
         \<^const_name>\<open>Unimplemented\<close>]),
       ("vec", "vec![1u64]",
        [\<^const_name>\<open>List.Cons\<close>]),
       ("addr_of", "addr_of!(semantic_navigation_ref)",
        [\<^const_name>\<open>bindlift1\<close>]),
       ("addr_of_mut", "addr_of_mut!(semantic_navigation_ref)",
        [\<^const_name>\<open>bindlift1\<close>])]
    val _ =
      macro_cases
      |> map_index
          (fn (index, (name, text, targets)) =>
            audit_case (index + 120) ("macro-" ^ name) text
              [(name, 0, targets), ("!", 0, targets)])
      |> List.app I

    val plain_macro_text = "NavigationPlain!(true)"
    val {start = plain_macro_start,
         markup = plain_macro_markup, ...} =
      capture_checked 140 "plain-registered-macro"
        plain_macro_text
    val plain_macro_bang =
      token_position plain_macro_text plain_macro_start "!" 0
    val _ =
      audit_assert "plain registered macro bang target changed"
        (constant_targets plain_macro_bang plain_macro_markup =
          [\<^const_name>\<open>semantic_navigation_plain_macro\<close>] andalso
         count_markup Markup.constN
           plain_macro_bang plain_macro_markup = 1)
    val _ =
      ignore
        (audit_case_trace 141 "matches-macro"
          "matches!(\<llangle>Some (1 :: nat)\<rrangle>, Some(_))"
          "matches" 0)
    val matches_text =
      "matches!(\<llangle>Some (1 :: nat)\<rrangle>, Some(_))"
    val {start = matches_start, replay = matches_markup, ...} =
      capture 142 "matches-bang" matches_text
    val matches_name_targets =
      constant_targets
        (token_position matches_text matches_start "matches" 0)
        matches_markup
    val matches_bang_targets =
      constant_targets
        (token_position matches_text matches_start "!" 0)
        matches_markup
    val _ =
      audit_assert "matches! name and bang semantic traces diverged"
        (matches_name_targets = matches_bang_targets andalso
         not (null matches_name_targets) andalso
         List.last matches_name_targets =
           \<^const_name>\<open>case_guard\<close>)

    val _ =
      audit_case 143 "erased-group-block-unsafe"
        "unsafe { (true) }"
        [("unsafe", 0, []),
         ("{", 0, []),
         ("(", 0, []),
         (")", 0, []),
         ("}", 0, [])]
    val _ =
      audit_case 144 "erased-array-borrow"
        "&[true]"
        [("&", 0, []),
         ("[", 0, [\<^const_name>\<open>List.Cons\<close>])]
    val _ =
      audit_case 145 "ignored-macro-operand"
        "debug_assert!(true, 1u32 + 2u32)"
        [("+", 0, [])]

    val failure_text = "1u32 + true"
    val failure_start =
      Position.make0 650 270000 0 "" ""
        "surface-semantic-navigation-failure"
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
             "surface semantic navigation audit: failing expression elaborated")
    val failure_operator =
      token_position failure_text failure_start "+" 0
    val _ =
      audit_assert "failed elaboration leaked a denotation target"
        (constant_targets failure_operator failure_markup = [] andalso
         count_markup Markup.constN
           failure_operator failure_markup = 0)
  in
    val _ =
      writeln
        "Surface denotation navigation matrix, route selection, erasure, macro retention, and failure isolation passed"
  end
\<close>

end
