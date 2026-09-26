theory Parser_Automatic_Read_Hardening_Tests
  imports
    Parser_Automatic_Read_Tests
begin

datatype_record automatic_read_array_leaf =
  automatic_read_leaf_values :: \<open>(32 word, 4) array\<close>
micro_rust_record automatic_read_array_leaf

datatype_record automatic_read_array_branch =
  automatic_read_branch_leaf :: automatic_read_array_leaf
micro_rust_record automatic_read_array_branch

datatype_record automatic_read_reference_leaf =
  automatic_read_reference_value_field ::
    \<open>(unit, unit, 32 word) Global_Store.ref\<close>
micro_rust_record automatic_read_reference_leaf

datatype_record automatic_read_reference_branch =
  automatic_read_reference_leaf_field ::
    \<open>(unit, unit, automatic_read_reference_leaf) Global_Store.ref\<close>
micro_rust_record automatic_read_reference_branch

datatype_record automatic_read_reference_trunk =
  automatic_read_reference_branch_field ::
    \<open>(unit, unit, automatic_read_reference_branch) Global_Store.ref\<close>
micro_rust_record automatic_read_reference_trunk

datatype_record automatic_read_pair_record =
  automatic_read_pair_left :: \<open>32 word\<close>
  automatic_read_pair_right :: \<open>32 word\<close>
micro_rust_record automatic_read_pair_record

datatype_record automatic_read_reference_wrapper =
  automatic_read_wrapped_reference ::
    \<open>(unit, unit, 32 word) Global_Store.ref\<close>
micro_rust_record automatic_read_reference_wrapper

datatype_record automatic_read_record_wrapper =
  automatic_read_wrapped_record :: automatic_read_record
micro_rust_record automatic_read_record_wrapper

definition automatic_read_array_leaf_value ::
  automatic_read_array_leaf
  where \<open> automatic_read_array_leaf_value \<equiv> undefined \<close>

definition automatic_read_array_branch_value ::
  automatic_read_array_branch
  where \<open> automatic_read_array_branch_value \<equiv> undefined \<close>

definition automatic_read_reference_leaf_value ::
  automatic_read_reference_leaf
  where \<open> automatic_read_reference_leaf_value \<equiv> undefined \<close>

definition automatic_read_reference_branch_value ::
  automatic_read_reference_branch
  where \<open> automatic_read_reference_branch_value \<equiv> undefined \<close>

definition automatic_read_reference_trunk_value ::
  automatic_read_reference_trunk
  where \<open> automatic_read_reference_trunk_value \<equiv> undefined \<close>

definition automatic_read_pair_reference ::
  \<open>(unit, unit, automatic_read_pair_record) Global_Store.ref\<close>
  where \<open> automatic_read_pair_reference \<equiv> undefined \<close>

definition automatic_read_pair_references ::
  \<open>
    ((unit, unit, automatic_read_pair_record) Global_Store.ref, 2) array
  \<close>
  where \<open> automatic_read_pair_references \<equiv> undefined \<close>

definition automatic_read_reference_wrapper_value ::
  automatic_read_reference_wrapper
  where \<open> automatic_read_reference_wrapper_value \<equiv> undefined \<close>

definition automatic_read_record_wrapper_value ::
  automatic_read_record_wrapper
  where \<open> automatic_read_record_wrapper_value \<equiv> undefined \<close>

definition automatic_read_dynamic_index ::
  \<open>(unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> automatic_read_dynamic_index \<equiv> undefined \<close>

definition automatic_read_callback_consumer ::
  \<open>
    (32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body) \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_callback_consumer \<equiv> undefined \<close>

definition automatic_read_reference_result_call ::
  \<open>
    (unit, (unit, unit, 32 word) Global_Store.ref, unit, unit, unit)
      function_body
  \<close>
  where \<open> automatic_read_reference_result_call \<equiv> undefined \<close>

definition automatic_read_reference_method_backend ::
  \<open>
    (unit, unit, 32 word) Global_Store.ref \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_reference_method_backend \<equiv> undefined \<close>

definition automatic_read_value_method_backend ::
  \<open>
    32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_value_method_backend \<equiv> undefined \<close>

definition automatic_read_ambiguous_reference_backend ::
  \<open>
    (unit, unit, 32 word) Global_Store.ref \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_ambiguous_reference_backend \<equiv> undefined \<close>

definition automatic_read_ambiguous_value_backend ::
  \<open>
    32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_ambiguous_value_backend \<equiv> undefined \<close>

definition automatic_read_result_reference_backend ::
  \<open>
    (unit, unit, 32 word) Global_Store.ref \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_result_reference_backend \<equiv> undefined \<close>

definition automatic_read_result_value_backend ::
  \<open>
    32 word \<Rightarrow>
    (unit, bool, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_result_value_backend \<equiv> undefined \<close>

micro_rust_notation (call)
  automatic_read_reference_method_backend
  ("automatic_read_reference_method")
micro_rust_notation (call)
  automatic_read_value_method_backend
  ("automatic_read_value_method")
micro_rust_notation (call)
  automatic_read_ambiguous_reference_backend
  ("automatic_read_ambiguous_method")
micro_rust_notation (call)
  automatic_read_ambiguous_value_backend
  ("automatic_read_ambiguous_method")
micro_rust_notation (call)
  automatic_read_result_reference_backend
  ("automatic_read_result_method")
micro_rust_notation (call)
  automatic_read_result_value_backend
  ("automatic_read_result_method")

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture
adhoc_overloading assign_add_const \<rightleftharpoons> parser_assign_add_fixture
adhoc_overloading index_const \<rightleftharpoons> parser_reference_array_index_fixture

section\<open>Automatic-read abstraction boundaries\<close>

text\<open>
The automatic-read mechanism has one deliberately small syntax boundary. Mutable allocated paths
and field/index projections may carry a pending read; groups and blocks preserve that result.
Every other result is plain. Borrow, explicit dereference, and assignment places consume the raw
form, while ordinary value positions consume the adjusted form.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val adjustment_name =
      \<^const_name>\<open>urust_internal_read_adjustment\<close>

    fun audit_assert message condition =
      if condition then ()
      else error ("automatic read boundary audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "automatic read boundary audit: empty parse")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    fun count_adjustments term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = adjustment_name then Integer.add 1 else I
          | _ => I)
        term 0

    fun expect_count label expected source =
      let val actual = count_adjustments (unchecked source)
      in
        audit_assert
          (label ^ " expected " ^ string_of_int expected ^
           " pending adjustment(s), found " ^ string_of_int actual)
          (actual = expected)
      end

    val _ =
      List.app (fn (label, source) => expect_count label 1 source)
        [
          ("allocated mutable path",
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; value"),
          ("direct field projection",
           "\<llangle>automatic_read_record_value\<rrangle>.automatic_read_field"),
          ("direct index projection",
           "\<llangle>automatic_read_array_value\<rrangle>[0_usize]"),
          ("parenthesized allocated path",
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; (value)"),
          ("blocked allocated path",
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; { value }"),
          ("parenthesized field projection",
           "(\<llangle>automatic_read_record_value\<rrangle>.automatic_read_field)"),
          ("blocked index projection",
           "{ \<llangle>automatic_read_array_value\<rrangle>[0_usize] }"),
          ("value-consuming binary operand",
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; value + 1_u32"),
          ("value-consuming call argument",
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
             "automatic_read_value_call(value)"),
          ("assignment right-hand side",
           "let mut target = \<llangle>1 :: 32 word\<rrangle>; " ^
             "let mut source = \<llangle>2 :: 32 word\<rrangle>; " ^
             "target = source; ()")
        ]

    val _ =
      List.app (fn (label, source) => expect_count label 0 source)
        [
          ("ordinary literal", "1_u32"),
          ("ordinary immutable path",
           "let value = \<llangle>1 :: 32 word\<rrangle>; value"),
          ("call result", "automatic_read_value_call(1_u32)"),
          ("tuple projection", "(1_u32, 2_u32).0"),
          ("explicit dereference raw boundary",
           "let mut value = \<llangle>automatic_read_record_value\<rrangle>; " ^
             "*(value.automatic_read_field)"),
          ("borrow raw boundary",
           "let mut value = \<llangle>automatic_read_record_value\<rrangle>; " ^
             "&value.automatic_read_field"),
          ("assignment target raw boundary",
           "let mut target = \<llangle>1 :: 32 word\<rrangle>; " ^
             "target = 2_u32; ()")
        ]
  in
    val _ = ()
  end
\<close>

section\<open>Opaque interface policy\<close>

ML_val\<open>
  local
    structure D = URust_Auto_Deref
    val ctxt = \<^context>
    val adjustment_name =
      \<^const_name>\<open>urust_internal_read_adjustment\<close>
    val field_projection_name =
      \<^const_name>\<open>urust_internal_field_projection\<close>
    val index_projection_name =
      \<^const_name>\<open>urust_internal_index_projection\<close>
    val atom = Free ("automatic_read_policy_atom", dummyT)
    val field_atom =
      Free ("automatic_read_policy_field", dummyT)
    val index_atom =
      Free ("automatic_read_policy_index", dummyT)

    fun audit_assert message condition =
      if condition then ()
      else error ("automatic read interface audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "automatic read interface audit: empty parse")

    fun count_adjustments term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = adjustment_name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_constant target term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = target then Integer.add 1 else I
          | _ => I)
        term 0

    fun expect_error label expected action =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("automatic read interface audit: " ^ label ^
              " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert
               (label ^ " produced the wrong diagnostic: " ^
                Runtime.exn_message exn)
               (String.isSubstring expected
                 (Runtime.exn_message exn)))

    val path = parse "value"
    val field =
      parse
        "\<llangle>automatic_read_record_value\<rrangle>.automatic_read_field"
    val index =
      parse "\<llangle>automatic_read_array_value\<rrangle>[0_usize]"
    val grouped = parse "(value)"
    val blocked = parse "{ value }"
    val literal = parse "1_u32"

    val plain = D.plain atom
    val _ =
      audit_assert "plain raw extraction changed its term"
        (Term.aconv (D.raw_term plain, atom))
    val _ =
      audit_assert "plain value extraction introduced an adjustment"
        (Term.aconv (D.value_term literal plain, atom))

    fun check_path_candidate label expression =
      let
        val candidate = D.eligible expression atom
        val raw = D.raw_term candidate
        val value = D.value_term expression candidate
      in
        audit_assert (label ^ " raw extraction changed its term")
          (Term.aconv (raw, atom));
        audit_assert (label ^ " did not create exactly one value adjustment")
          (count_adjustments value = 1)
      end

    val _ = check_path_candidate "path candidate" path

    val field_candidate =
      D.project_field field (D.plain atom) field_atom
    val _ =
      audit_assert "raw single-field projection retained an internal recipe"
        (count_constant field_projection_name
           (D.raw_term field_candidate) = 0)
    val _ =
      audit_assert "field projection did not create exactly one value adjustment"
        (count_adjustments
           (D.value_term field field_candidate) = 1)

    val index_candidate =
      D.project_index index field_candidate index_atom
    val _ =
      audit_assert "index projection lost its ordered field/index recipe"
        (count_constant field_projection_name
             (D.raw_term index_candidate) = 1 andalso
         count_constant index_projection_name
             (D.raw_term index_candidate) = 1)
    val _ =
      audit_assert "composed projection duplicated its value adjustment"
        (count_adjustments
           (D.value_term index index_candidate) = 1)

    val carried =
      D.eligible path atom
      |> D.transparent grouped
      |> D.transparent blocked
    val _ =
      audit_assert "transparent carriers changed raw extraction"
        (Term.aconv (D.raw_term carried, atom))
    val _ =
      audit_assert "transparent carriers duplicated or dropped the adjustment"
        (count_adjustments (D.value_term blocked carried) = 1)

    val _ =
      expect_error "field through eligible"
        "projection requires a projection operation"
        (fn () => D.eligible field atom)
    val _ =
      expect_error "index through eligible"
        "projection requires a projection operation"
        (fn () => D.eligible index atom)
    val _ =
      expect_error "literal candidate"
        "ineligible expression cannot create a candidate"
        (fn () => D.eligible literal atom)
    val _ =
      expect_error "field operation on a path"
        "field projection requires a field expression"
        (fn () => D.project_field path plain field_atom)
    val _ =
      expect_error "index operation on a field"
        "index projection requires an index expression"
        (fn () => D.project_index field plain index_atom)

    val _ =
      List.app
        (fn (label, expression) =>
          expect_error label
            "non-transparent expression cannot carry a candidate"
            (fn () => D.transparent expression plain))
        [
          ("path carrier", path),
          ("field carrier", field),
          ("index carrier", index),
          ("literal carrier", literal)
        ]
  in
    val _ = ()
  end
\<close>

section\<open>Composed place recipes\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val dereference_name =
      \<^const_name>\<open>parser_dereference_fixture\<close>
    val index_name =
      \<^const_name>\<open>parser_reference_array_index_fixture\<close>
    val dynamic_index_name =
      \<^const_name>\<open>automatic_read_dynamic_index\<close>
    val marker_names =
      [\<^const_name>\<open>urust_internal_read_adjustment\<close>,
       \<^const_name>\<open>urust_internal_field_projection\<close>,
       \<^const_name>\<open>urust_internal_index_projection\<close>]

    fun audit_assert message condition =
      if condition then ()
      else error ("composed automatic read audit: " ^ message)

    fun checked source =
      Parser_Test_Report_Lock.run (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source source))
      |> Term_Position.strip_positions

    fun count_constant target term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = target then Integer.add 1 else I
          | _ => I)
        term 0

    fun marker_count term =
      fold (fn name => Integer.add (count_constant name term))
        marker_names 0

    fun check_row
        {label, implicit_source, explicit_source,
         reads, indices, dynamic_indices, constants} =
      let
        val implicit = checked implicit_source
        val explicit = checked explicit_source
        fun constants_match term =
          List.all
            (fn (name, expected) =>
              count_constant name term = expected)
            constants
        fun reject reason =
          error
            ("composed automatic read audit " ^ quote label ^ ": " ^
             reason ^ "\nimplicit: " ^
             Syntax.string_of_term ctxt implicit ^ "\nexplicit: " ^
             Syntax.string_of_term ctxt explicit)
      in
        if not (Term.aconv (implicit, explicit)) then
          reject "implicit and explicit controls differ"
        else if count_constant dereference_name implicit <> reads then
          reject "implicit dereference count changed"
        else if count_constant dereference_name explicit <> reads then
          reject "explicit dereference count changed"
        else if count_constant index_name implicit <> indices orelse
            count_constant index_name explicit <> indices then
          reject "reference-index backend count changed"
        else if count_constant dynamic_index_name implicit <>
            dynamic_indices orelse
            count_constant dynamic_index_name explicit <>
              dynamic_indices then
          reject "dynamic index evaluation count changed"
        else if not (constants_match implicit) orelse
            not (constants_match explicit) then
          reject "field or operation backend identity changed"
        else if marker_count implicit <> 0 orelse
            marker_count explicit <> 0 then
          reject "an internal place marker survived checking"
        else ()
      end

    val rows =
      [
        {label = "field followed by index",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "leaf.automatic_read_leaf_values[0_usize]",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "*(leaf.automatic_read_leaf_values[0_usize])",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_array_leaf_automatic_read_leaf_values_lens\<close>,
             1)]},
        {label = "multiple fields followed by index",
         implicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize]",
         explicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "*(branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize])",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_array_branch_automatic_read_branch_leaf_lens\<close>,
             1),
            (\<^const_name>\<open>automatic_read_array_leaf_automatic_read_leaf_values_lens\<close>,
             1)]},
        {label = "dynamic index exactly once",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "leaf.automatic_read_leaf_values[automatic_read_dynamic_index()]",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "*(leaf.automatic_read_leaf_values[" ^
           "automatic_read_dynamic_index()])",
         reads = 1, indices = 1, dynamic_indices = 1,
         constants =
           [(\<^const_name>\<open>automatic_read_array_leaf_automatic_read_leaf_values_lens\<close>,
             1)]},
        {label = "ordinary field returning a reference",
         implicit_source =
           "\<llangle>automatic_read_reference_leaf_value\<rrangle>." ^
           "automatic_read_reference_value_field",
         explicit_source =
           "\<llangle>automatic_read_reference_leaf_value\<rrangle>." ^
           "automatic_read_reference_value_field",
         reads = 0, indices = 0, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_reference_leaf_automatic_read_reference_value_field_lens\<close>,
             1)]},
        {label = "reference-valued intermediate followed by field",
         implicit_source =
           "\<llangle>automatic_read_reference_branch_value\<rrangle>." ^
           "automatic_read_reference_leaf_field." ^
           "automatic_read_reference_value_field",
         explicit_source =
           "*(\<llangle>automatic_read_reference_branch_value\<rrangle>." ^
           "automatic_read_reference_leaf_field." ^
           "automatic_read_reference_value_field)",
         reads = 1, indices = 0, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_reference_branch_automatic_read_reference_leaf_field_lens\<close>,
             1),
            (\<^const_name>\<open>automatic_read_reference_leaf_automatic_read_reference_value_field_lens\<close>,
             1)]},
        {label = "direct field projection",
         implicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "branch.automatic_read_branch_leaf",
         explicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "*(branch.automatic_read_branch_leaf)",
         reads = 1, indices = 0, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_array_branch_automatic_read_branch_leaf_lens\<close>,
             1)]},
        {label = "chained field projection",
         implicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "branch.automatic_read_branch_leaf.automatic_read_leaf_values",
         explicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "*(branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values)",
         reads = 1, indices = 0, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_array_branch_automatic_read_branch_leaf_lens\<close>,
             1),
            (\<^const_name>\<open>automatic_read_array_leaf_automatic_read_leaf_values_lens\<close>,
             1)]},
        {label = "parenthesized projection chain",
         implicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "(branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize])",
         explicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "(*(branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize]))",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "blocked projection chain",
         implicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "{ branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize] }",
         explicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "{ *(branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize]) }",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "multiple core-reference boundaries",
         implicit_source =
           "\<llangle>automatic_read_reference_trunk_value\<rrangle>." ^
           "automatic_read_reference_branch_field." ^
           "automatic_read_reference_leaf_field." ^
           "automatic_read_reference_value_field",
         explicit_source =
           "*((* (\<llangle>automatic_read_reference_trunk_value\<rrangle>." ^
           "automatic_read_reference_branch_field." ^
           "automatic_read_reference_leaf_field))." ^
           "automatic_read_reference_value_field)",
         reads = 2, indices = 0, dynamic_indices = 0,
         constants = []},
        {label = "match expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "match_switch leaf.automatic_read_leaf_values[0_usize] " ^
           "{ 0 \<Rightarrow> 1_u32, _ \<Rightarrow> 2_u32 }",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "match_switch *(leaf.automatic_read_leaf_values[0_usize]) " ^
           "{ 0 \<Rightarrow> 1_u32, _ \<Rightarrow> 2_u32 }",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "constructor expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "Some(leaf.automatic_read_leaf_values[0_usize])",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "Some(*(leaf.automatic_read_leaf_values[0_usize]))",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "numeric expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "leaf.automatic_read_leaf_values[0_usize] + 1_u32",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "*(leaf.automatic_read_leaf_values[0_usize]) + 1_u32",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "comparison expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "leaf.automatic_read_leaf_values[0_usize] == 1_u32",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "*(leaf.automatic_read_leaf_values[0_usize]) == 1_u32",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "return expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "return leaf.automatic_read_leaf_values[0_usize];",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "return *(leaf.automatic_read_leaf_values[0_usize]);",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "call expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "automatic_read_value_call(" ^
           "leaf.automatic_read_leaf_values[0_usize])",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "automatic_read_value_call(" ^
           "*(leaf.automatic_read_leaf_values[0_usize]))",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "branch expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "if true { leaf.automatic_read_leaf_values[0_usize] } " ^
           "else { 0_u32 }",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "if true { *(leaf.automatic_read_leaf_values[0_usize]) } " ^
           "else { 0_u32 }",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "higher-order callback expected type",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "automatic_read_callback_consumer(" ^
           "|ignored| leaf.automatic_read_leaf_values[0_usize])",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "automatic_read_callback_consumer(" ^
           "|ignored| *(leaf.automatic_read_leaf_values[0_usize]))",
         reads = 1, indices = 1, dynamic_indices = 0,
         constants = []},
        {label = "reference-valued iterator item",
         implicit_source =
           "for slot in \<llangle>automatic_read_pair_references\<rrangle> { " ^
           "let left = slot.automatic_read_pair_left; () }",
         explicit_source =
           "for slot in \<llangle>automatic_read_pair_references\<rrangle> { " ^
           "let left = *(slot.automatic_read_pair_left); () }",
         reads = 1, indices = 0, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_pair_record_automatic_read_pair_left_lens\<close>,
             1)]},
        {label = "two fields from one reference-valued iterator item",
         implicit_source =
           "for slot in \<llangle>automatic_read_pair_references\<rrangle> { " ^
           "let left = slot.automatic_read_pair_left; " ^
           "let right = slot.automatic_read_pair_right; () }",
         explicit_source =
           "for slot in \<llangle>automatic_read_pair_references\<rrangle> { " ^
           "let left = *(slot.automatic_read_pair_left); " ^
           "let right = *(slot.automatic_read_pair_right); () }",
         reads = 2, indices = 0, dynamic_indices = 0,
         constants =
           [(\<^const_name>\<open>automatic_read_pair_record_automatic_read_pair_left_lens\<close>,
             1),
            (\<^const_name>\<open>automatic_read_pair_record_automatic_read_pair_right_lens\<close>,
             1)]}
      ]

    val _ = List.app check_row rows
  in
    val _ = ()
  end
\<close>

section\<open>Notation dispatch and place expectations\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val dereference_name =
      \<^const_name>\<open>parser_dereference_fixture\<close>
    val reference_backend =
      \<^const_name>\<open>automatic_read_reference_method_backend\<close>
    val value_backend =
      \<^const_name>\<open>automatic_read_value_method_backend\<close>
    val result_reference_backend =
      \<^const_name>\<open>automatic_read_result_reference_backend\<close>
    val result_value_backend =
      \<^const_name>\<open>automatic_read_result_value_backend\<close>
    val marker_names =
      [\<^const_name>\<open>urust_internal_read_adjustment\<close>,
       \<^const_name>\<open>urust_internal_field_projection\<close>,
       \<^const_name>\<open>urust_internal_index_projection\<close>]

    fun checked source =
      Parser_Test_Report_Lock.run (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source source))
      |> Term_Position.strip_positions

    fun count_constant target term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = target then Integer.add 1 else I
          | _ => I)
        term 0

    fun marker_count term =
      fold (fn name => Integer.add (count_constant name term))
        marker_names 0

    fun reject label reason terms =
      error
        ("automatic read notation audit " ^ quote label ^ ": " ^
         reason ^
         String.concat
           (map
             (fn term =>
               "\nterm: " ^ Syntax.string_of_term ctxt term)
             terms))

    fun check_pair
        {label, implicit_source, explicit_source,
         reads, backend, backend_count} =
      let
        val implicit = checked implicit_source
        val explicit = checked explicit_source
      in
        if not (Term.aconv (implicit, explicit)) then
          reject label "implicit and explicit controls differ"
            [implicit, explicit]
        else if count_constant dereference_name implicit <> reads orelse
            count_constant dereference_name explicit <> reads then
          reject label "dereference count changed" [implicit, explicit]
        else if count_constant backend implicit <> backend_count orelse
            count_constant backend explicit <> backend_count then
          reject label "notation backend changed" [implicit, explicit]
        else if marker_count implicit <> 0 orelse
            marker_count explicit <> 0 then
          reject label "an internal marker survived" [implicit, explicit]
        else ()
      end

    fun check_selected
        {label, source, reads, selected, rejected} =
      let val term = checked source
      in
        if count_constant dereference_name term <> reads then
          reject label "dereference count changed" [term]
        else if count_constant selected term <> 1 then
          reject label "selected backend changed" [term]
        else if count_constant rejected term <> 0 then
          reject label "an incompatible backend survived" [term]
        else if marker_count term <> 0 then
          reject label "an internal marker survived" [term]
        else ()
      end

    val _ =
      check_pair
        {label = "value-consuming mutable receiver",
         implicit_source =
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
           "value.automatic_read_value_method()",
         explicit_source =
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
           "(*value).automatic_read_value_method()",
         reads = 1, backend = value_backend, backend_count = 1}

    val _ =
      check_pair
        {label = "value-consuming projected receiver",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "leaf.automatic_read_leaf_values[0_usize]." ^
           "automatic_read_value_method()",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "(*(leaf.automatic_read_leaf_values[0_usize]))." ^
           "automatic_read_value_method()",
         reads = 1, backend = value_backend, backend_count = 1}

    val _ =
      check_selected
        {label = "reference-consuming mutable receiver",
         source =
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
           "value.automatic_read_reference_method()",
         reads = 0, selected = reference_backend,
         rejected = value_backend}

    val _ =
      check_selected
        {label = "reference-consuming projected receiver",
         source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "leaf.automatic_read_leaf_values[0_usize]." ^
           "automatic_read_reference_method()",
         reads = 0, selected = reference_backend,
         rejected = value_backend}

    val _ =
      check_selected
        {label = "result type selects reference backend",
         source =
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
           "value.automatic_read_result_method() + 1_u32",
         reads = 0, selected = result_reference_backend,
         rejected = result_value_backend}

    val _ =
      check_pair
        {label = "result type selects value backend",
         implicit_source =
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
           "if value.automatic_read_result_method() " ^
           "{ 1_u32 } else { 0_u32 }",
         explicit_source =
           "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
           "if (*value).automatic_read_result_method() " ^
           "{ 1_u32 } else { 0_u32 }",
         reads = 1, backend = result_value_backend,
         backend_count = 1}

    val ordinary_receiver =
      checked
        ("\<llangle>1 :: 32 word\<rrangle>." ^
         "automatic_read_value_method()")
    val _ =
      if count_constant value_backend ordinary_receiver = 1 andalso
         count_constant dereference_name ordinary_receiver = 0 andalso
         marker_count ordinary_receiver = 0
      then ()
      else
        reject "ordinary value receiver"
          "ordinary receiver acquired a read or wrong backend"
          [ordinary_receiver]

    val ambiguous_source =
      "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
      "value.automatic_read_ambiguous_method()"
    val ambiguous_result = Exn.result checked ambiguous_source
    val _ =
      (case ambiguous_result of
         Exn.Res term =>
           reject "genuine reference/value ambiguity"
             "ambiguous receiver selected a backend" [term]
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message = Runtime.exn_message exn
               val internal =
                 ["urust_internal_read_adjustment",
                  "urust_internal_field_projection",
                  "urust_internal_index_projection"]
             in
               if not
                   (String.isSubstring
                     "Ambiguous uRust notation"
                     message)
               then
                 error
                   ("automatic read notation audit: ambiguity diagnostic changed: " ^
                    message)
               else if not
                   (String.isSubstring
                     "automatic_read_ambiguous_reference_backend"
                     message) orelse
                   not
                     (String.isSubstring
                       "automatic_read_ambiguous_value_backend"
                       message)
               then
                 error
                   ("automatic read notation audit: ambiguity omitted a backend: " ^
                    message)
               else if exists
                   (fn name => String.isSubstring name message)
                   internal
               then
                 error
                   ("automatic read notation audit: internal marker leaked: " ^
                    message)
               else ()
             end)
  in
    val _ = ()
  end
\<close>

urust_expr automatic_read_recovery_after_failed_dispatch
  \<open> 1_u32 \<close>

section\<open>Raw places and ordinary receivers\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val dereference_name =
      \<^const_name>\<open>parser_dereference_fixture\<close>
    val reference_index_name =
      \<^const_name>\<open>parser_reference_array_index_fixture\<close>
    val update_name =
      \<^const_name>\<open>parser_update_fixture\<close>
    val assign_add_name =
      \<^const_name>\<open>parser_assign_add_fixture\<close>
    val reference_backend =
      \<^const_name>\<open>automatic_read_reference_method_backend\<close>
    val marker_names =
      [\<^const_name>\<open>urust_internal_read_adjustment\<close>,
       \<^const_name>\<open>urust_internal_field_projection\<close>,
       \<^const_name>\<open>urust_internal_index_projection\<close>]

    fun checked source =
      Parser_Test_Report_Lock.run (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source source))
      |> Term_Position.strip_positions

    fun count_constant target term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = target then Integer.add 1 else I
          | _ => I)
        term 0

    fun check label source expectations =
      let
        val term = checked source
        fun mismatch (name, expected) =
          count_constant name term <> expected
        val marker_count =
          fold
            (fn name => Integer.add (count_constant name term))
            marker_names 0
      in
        if exists mismatch expectations then
          error
            ("automatic read raw-place audit " ^ quote label ^
             ": operation count changed\nterm: " ^
             Syntax.string_of_term ctxt term)
        else if marker_count <> 0 then
          error
            ("automatic read raw-place audit " ^ quote label ^
             ": internal marker survived")
        else ()
      end

    val composed =
      "branch.automatic_read_branch_leaf." ^
      "automatic_read_leaf_values[0_usize]"

    val _ =
      check "assignment target"
        ("let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         composed ^ " = 1_u32; ()")
        [(dereference_name, 0), (reference_index_name, 1),
         (update_name, 1)]

    val _ =
      check "assignment right-hand side"
        ("let mut target = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         "let mut source = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         "target.automatic_read_branch_leaf." ^
         "automatic_read_leaf_values[0_usize] = " ^
         "source.automatic_read_branch_leaf." ^
         "automatic_read_leaf_values[0_usize]; ()")
        [(dereference_name, 1), (reference_index_name, 2),
         (update_name, 1)]

    val _ =
      check "compound assignment target"
        ("let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         composed ^ " += 1_u32; ()")
        [(dereference_name, 0), (reference_index_name, 1),
         (assign_add_name, 1)]

    val _ =
      check "borrow boundary"
        ("let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         "&" ^ composed)
        [(dereference_name, 0), (reference_index_name, 1)]

    val _ =
      check "explicit dereference boundary"
        ("let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         "*(" ^ composed ^ ")")
        [(dereference_name, 1), (reference_index_name, 1)]

    val _ =
      check "expected reference boundary"
        ("let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         composed ^ ".automatic_read_reference_method()")
        [(dereference_name, 0), (reference_index_name, 1),
         (reference_backend, 1)]

    val _ =
      check "ordinary value field and index"
        ("\<llangle>automatic_read_array_leaf_value\<rrangle>." ^
         "automatic_read_leaf_values[0_usize]")
        [(dereference_name, 0), (reference_index_name, 0),
         (\<^const_name>\<open>array_index\<close>, 1)]
  in
    val _ = ()
  end
\<close>

section\<open>Untyped ordinary receiver constraints\<close>

text\<open>
Projection recipes expose enough type information for an untyped declaration argument to be
classified without assuming that it is a core reference. The explicit controls below constrain the
same source argument through an antiquotation; both forms must elaborate identically and without an
automatic read.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val argument_pos =
      Position.make0 1 0 0 "" "" "automatic-read-untyped-argument"
    val dereference_name =
      \<^const_name>\<open>parser_dereference_fixture\<close>
    val reference_index_name =
      \<^const_name>\<open>parser_reference_array_index_fixture\<close>
    val marker_names =
      [\<^const_name>\<open>urust_internal_read_adjustment\<close>,
       \<^const_name>\<open>urust_internal_field_projection\<close>,
       \<^const_name>\<open>urust_internal_index_projection\<close>]

    fun checked source =
      Parser_Test_Report_Lock.run (fn () =>
        Parser_Test_Elaboration.expression_with_arguments ctxt
          [("record", argument_pos)]
          (Parser_Lex_Util.text_source source))
      |> Term_Position.strip_positions

    fun count_constant target term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = target then Integer.add 1 else I
          | _ => I)
        term 0

    fun marker_count term =
      fold (fn name => Integer.add (count_constant name term))
        marker_names 0

    fun check
        {label, implicit_source, control_source, constants} =
      let
        val implicit = checked implicit_source
        val control = checked control_source
        fun constants_match term =
          List.all
            (fn (name, expected) =>
              count_constant name term = expected)
            constants
        fun reject reason =
          error
            ("automatic read untyped receiver audit " ^ quote label ^
             ": " ^ reason ^
             "\nimplicit: " ^ Syntax.string_of_term ctxt implicit ^
             "\ncontrol: " ^ Syntax.string_of_term ctxt control)
      in
        if not (Term.aconv (implicit, control)) then
          reject "implicit and explicitly typed controls differ"
        else if count_constant dereference_name implicit <> 0 orelse
            count_constant dereference_name control <> 0 then
          reject "ordinary receiver acquired an automatic read"
        else if count_constant reference_index_name implicit <> 0 orelse
            count_constant reference_index_name control <> 0 then
          reject "ordinary receiver selected reference indexing"
        else if not (constants_match implicit) orelse
            not (constants_match control) then
          reject "field or index backend identity changed"
        else if marker_count implicit <> 0 orelse
            marker_count control <> 0 then
          reject "an internal marker survived checking"
        else ()
      end

    val _ =
      check
        {label = "untyped direct ordinary field",
         implicit_source =
           "record.automatic_read_pair_left + 0_u32",
         control_source =
           "\<llangle>record :: automatic_read_pair_record\<rrangle>." ^
           "automatic_read_pair_left + 0_u32",
         constants =
           [(\<^const_name>\<open>automatic_read_pair_record_automatic_read_pair_left_lens\<close>,
             1)]}

    val _ =
      check
        {label = "untyped ordinary field followed by index",
         implicit_source =
           "record.automatic_read_leaf_values[0_usize] + 0_u32",
         control_source =
           "\<llangle>record :: automatic_read_array_leaf\<rrangle>." ^
           "automatic_read_leaf_values[0_usize] + 0_u32",
         constants =
           [(\<^const_name>\<open>automatic_read_array_leaf_automatic_read_leaf_values_lens\<close>,
             1),
            (\<^const_name>\<open>array_index\<close>, 1)]}

    val _ =
      check
        {label = "untyped chained ordinary projection",
         implicit_source =
           "record.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize] + 0_u32",
         control_source =
           "\<llangle>record :: automatic_read_array_branch\<rrangle>." ^
           "automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize] + 0_u32",
         constants =
           [(\<^const_name>\<open>automatic_read_array_branch_automatic_read_branch_leaf_lens\<close>,
             1),
            (\<^const_name>\<open>automatic_read_array_leaf_automatic_read_leaf_values_lens\<close>,
             1),
            (\<^const_name>\<open>array_index\<close>, 1)]}
  in
    val _ = ()
  end
\<close>

section\<open>Intentional negative boundaries\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val dereference_name =
      \<^const_name>\<open>parser_dereference_fixture\<close>
    val internal_names =
      ["urust_internal_read_adjustment",
       "urust_internal_field_projection",
       "urust_internal_index_projection"]

    fun checked source =
      Parser_Test_Report_Lock.run (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source source))
      |> Term_Position.strip_positions

    fun count_constant target term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = target then Integer.add 1 else I
          | _ => I)
        term 0

    fun expect_rejection label source =
      (case Exn.result checked source of
         Exn.Res term =>
           error
             ("automatic read negative audit " ^ quote label ^
              ": source unexpectedly elaborated\nterm: " ^
              Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn
             in
               if exists
                   (fn name => String.isSubstring name message)
                   internal_names
               then
                 error
                   ("automatic read negative audit " ^ quote label ^
                    ": internal marker leaked into diagnostic: " ^
                    message)
               else ()
             end)

    val _ =
      expect_rejection "reference-returning call result"
        "automatic_read_reference_result_call() + 1_u32"

    val _ =
      expect_rejection "reference wrapper field"
        ("\<llangle>automatic_read_reference_wrapper_value\<rrangle>." ^
         "automatic_read_wrapped_reference + 1_u32")

    val _ =
      expect_rejection "implicit method borrow"
        ("\<llangle>1 :: 32 word\<rrangle>." ^
         "automatic_read_reference_method()")

    val _ =
      expect_rejection "general wrapper autoderef"
        ("\<llangle>automatic_read_record_wrapper_value\<rrangle>." ^
         "automatic_read_field")

    val _ =
      expect_rejection "call-result method autoderef"
        ("automatic_read_reference_result_call()." ^
         "automatic_read_value_method()")

    val explicit_call =
      checked
        "*(automatic_read_reference_result_call()) + 1_u32"
    val explicit_wrapper =
      checked
        ("*(\<llangle>automatic_read_reference_wrapper_value\<rrangle>." ^
         "automatic_read_wrapped_reference) + 1_u32")
    val _ =
      if count_constant dereference_name explicit_call = 1 andalso
         count_constant dereference_name explicit_wrapper = 1
      then ()
      else
        error
          "automatic read negative audit: explicit boundary controls changed"
  in
    val _ = ()
  end
\<close>

section\<open>Mutation-guard sanity\<close>

text\<open>
The focused assertions below are themselves checked against representative mutated terms. This
pins sensitivity to traversal order, duplicate effects, backend identity, ordinary receivers, and
unresolved markers; the opaque-interface section above separately pins candidate policy.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val dereference_name =
      \<^const_name>\<open>parser_dereference_fixture\<close>
    val dynamic_index_name =
      \<^const_name>\<open>automatic_read_dynamic_index\<close>
    val value_backend =
      \<^const_name>\<open>automatic_read_value_method_backend\<close>
    val reference_backend =
      \<^const_name>\<open>automatic_read_reference_method_backend\<close>
    val adjustment_name =
      \<^const_name>\<open>urust_internal_read_adjustment\<close>

    fun checked source =
      Parser_Test_Report_Lock.run (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source source))
      |> Term_Position.strip_positions

    fun count_constant target term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = target then Integer.add 1 else I
          | _ => I)
        term 0

    fun assert_detected label condition =
      if condition then ()
      else
        error
          ("automatic read mutation guard did not detect " ^ label)

    val dynamic =
      checked
        ("let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
         "leaf.automatic_read_leaf_values[automatic_read_dynamic_index()]")
    val duplicated_dynamic = HOLogic.mk_prod (dynamic, dynamic)
    val _ =
      assert_detected "duplicate index evaluation"
        (count_constant dynamic_index_name duplicated_dynamic <> 1)

    val ordered_left =
      checked
        ("let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         "branch.automatic_read_branch_leaf." ^
         "automatic_read_leaf_values[0_usize]")
    val ordered_right =
      checked
        ("let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
         "branch.automatic_read_branch_leaf." ^
         "automatic_read_leaf_values[1_usize]")
    val _ =
      assert_detected "projection traversal order"
        (not
          (Term.aconv
            (HOLogic.mk_prod (ordered_left, ordered_right),
             HOLogic.mk_prod (ordered_right, ordered_left))))

    val value_method =
      checked
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "value.automatic_read_value_method()")
    val wrong_backend =
      Term.map_aterms
        (fn Const (name, typ) =>
              if name = value_backend
              then Const (reference_backend, typ)
              else Const (name, typ)
          | atom => atom)
        value_method
    val _ =
      assert_detected "notation backend selection"
        (count_constant value_backend wrong_backend <> 1)

    val ordinary =
      checked
        ("\<llangle>automatic_read_array_leaf_value\<rrangle>." ^
         "automatic_read_leaf_values[0_usize]")
    val forced_ordinary_read =
      checked
        ("*(\<llangle>automatic_read_reference_wrapper_value\<rrangle>." ^
         "automatic_read_wrapped_reference)")
    val _ =
      assert_detected "ordinary receiver read"
        (count_constant dereference_name ordinary = 0 andalso
         count_constant dereference_name forced_ordinary_read <> 0)

    val unresolved =
      Const (adjustment_name, dummyT) $
        Free ("automatic_read_mutation_payload", dummyT) $ ordinary
    val _ =
      assert_detected "unresolved internal marker"
        (count_constant adjustment_name unresolved <> 0)
  in
    val _ = ()
  end
\<close>

no_adhoc_overloading index_const \<rightleftharpoons> parser_reference_array_index_fixture
no_adhoc_overloading assign_add_const \<rightleftharpoons> parser_assign_add_fixture
no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

end
