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

definition automatic_read_dynamic_index ::
  \<open>(unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> automatic_read_dynamic_index \<equiv> undefined \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
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
         reads, indices, dynamic_indices} =
      let
        val implicit = checked implicit_source
        val explicit = checked explicit_source
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
         reads = 1, indices = 1, dynamic_indices = 0},
        {label = "multiple fields followed by index",
         implicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize]",
         explicit_source =
           "let mut branch = \<llangle>automatic_read_array_branch_value\<rrangle>; " ^
           "*(branch.automatic_read_branch_leaf." ^
           "automatic_read_leaf_values[0_usize])",
         reads = 1, indices = 1, dynamic_indices = 0},
        {label = "dynamic index exactly once",
         implicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "leaf.automatic_read_leaf_values[automatic_read_dynamic_index()]",
         explicit_source =
           "let mut leaf = \<llangle>automatic_read_array_leaf_value\<rrangle>; " ^
           "*(leaf.automatic_read_leaf_values[" ^
           "automatic_read_dynamic_index()])",
         reads = 1, indices = 1, dynamic_indices = 1},
        {label = "one reference-valued intermediate",
         implicit_source =
           "\<llangle>automatic_read_reference_leaf_value\<rrangle>." ^
           "automatic_read_reference_value_field",
         explicit_source =
           "\<llangle>automatic_read_reference_leaf_value\<rrangle>." ^
           "automatic_read_reference_value_field",
         reads = 0, indices = 0, dynamic_indices = 0},
        {label = "reference-valued intermediate followed by field",
         implicit_source =
           "\<llangle>automatic_read_reference_branch_value\<rrangle>." ^
           "automatic_read_reference_leaf_field." ^
           "automatic_read_reference_value_field",
         explicit_source =
           "*(\<llangle>automatic_read_reference_branch_value\<rrangle>." ^
           "automatic_read_reference_leaf_field." ^
           "automatic_read_reference_value_field)",
         reads = 1, indices = 0, dynamic_indices = 0}
      ]

    val _ = List.app check_row rows
  in
    val _ = ()
  end
\<close>

no_adhoc_overloading index_const \<rightleftharpoons> parser_reference_array_index_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

end
