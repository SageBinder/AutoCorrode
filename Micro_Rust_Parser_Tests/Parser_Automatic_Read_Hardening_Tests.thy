theory Parser_Automatic_Read_Hardening_Tests
  imports
    Parser_Automatic_Read_Tests
begin

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

end
