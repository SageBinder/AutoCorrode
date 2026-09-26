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

section\<open>Opaque interface policy\<close>

ML_val\<open>
  local
    structure D = URust_Auto_Deref
    val ctxt = \<^context>
    val adjustment_name =
      \<^const_name>\<open>urust_internal_read_adjustment\<close>
    val atom = Free ("automatic_read_policy_atom", dummyT)

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

    fun check_candidate label expression =
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

    val _ = check_candidate "path candidate" path
    val _ = check_candidate "field candidate" field
    val _ = check_candidate "index candidate" index

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
      expect_error "group candidate"
        "transparent expression cannot create a candidate"
        (fn () => D.eligible grouped atom)
    val _ =
      expect_error "block candidate"
        "transparent expression cannot create a candidate"
        (fn () => D.eligible blocked atom)
    val _ =
      expect_error "literal candidate"
        "ineligible expression cannot create a candidate"
        (fn () => D.eligible literal atom)

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

end
