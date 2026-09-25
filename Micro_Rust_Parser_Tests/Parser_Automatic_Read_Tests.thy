theory Parser_Automatic_Read_Tests
  imports
    Parser_Expression_Tests
begin

section\<open>Automatic reads of core places\<close>

text\<open>
Mutable scalar bindings and projections through core references are storage places. In value
contexts the parser reads those places exactly once unless the surrounding type requires the
reference itself. The adjustment is internal to checking, so implicit and explicit source forms
have alpha-equivalent checked HOL terms.
\<close>

datatype_record automatic_read_record =
  automatic_read_field :: \<open>32 word\<close>
micro_rust_record automatic_read_record

definition automatic_read_record_value :: automatic_read_record where
  \<open> automatic_read_record_value \<equiv> make_automatic_read_record 7 \<close>

definition automatic_read_reference_value ::
  \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  where \<open> automatic_read_reference_value \<equiv> undefined \<close>

definition automatic_read_array_value :: \<open>(32 word, 4) array\<close> where
  \<open>
    automatic_read_array_value \<equiv>
      array_of_list [1, 2, 3, 4]
  \<close>

definition automatic_read_value_call ::
  \<open>32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body\<close>
  where \<open> automatic_read_value_call \<equiv> lift_fun1 id \<close>

definition automatic_read_reference_call ::
  \<open>
    (unit, unit, 32 word) Global_Store.ref \<Rightarrow>
    (unit, (unit, unit, 32 word) Global_Store.ref, unit, unit, unit) function_body
  \<close>
  where \<open> automatic_read_reference_call \<equiv> lift_fun1 id \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture
adhoc_overloading index_const \<rightleftharpoons> parser_reference_array_index_fixture

urust_expr automatic_read_expected_reference ::
  \<open>
    (unit, (unit, unit, 32 word) Global_Store.ref, unit, unit, unit) function_body
  \<close>
  \<open>
    let mut value = \<llangle>0 :: 32 word\<rrangle>;
    value
  \<close>

urust_expr automatic_read_reference_parameter ::
  \<open>
    (unit, unit, 32 word) Global_Store.ref \<Rightarrow>
    (unit, (unit, unit, 32 word) Global_Store.ref, unit, unit, unit) function_body
  \<close>
  (reference)
  \<open> reference \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("automatic read audit: " ^ message)

    fun checked source =
      Parser_Test_Report_Lock.run (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source source))
      |> Term_Position.strip_positions

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val dereference_name =
      \<^const_name>\<open>parser_dereference_fixture\<close>

    fun dereference_count term =
      count_constant dereference_name term

    fun equivalent label implicit_source explicit_source =
      let
        val implicit = checked implicit_source
        val explicit = checked explicit_source
      in
        audit_assert
          (label ^ " did not match its explicit-dereference form\n" ^
           "implicit: " ^ Syntax.string_of_term ctxt implicit ^ "\n" ^
           "explicit: " ^ Syntax.string_of_term ctxt explicit)
          (Term.aconv (implicit, explicit))
      end

    fun definition_rhs name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals
      |> snd
      |> Term_Position.strip_positions

    val scalar_implicit =
      checked
        "let mut value = \<llangle>1 :: 32 word\<rrangle>; value"

    val nested_implicit =
      checked
        ("let mut value = \<llangle>automatic_read_reference_value\<rrangle>; " ^
         "value")

    val explicit_once =
      checked
        "let mut value = \<llangle>1 :: 32 word\<rrangle>; *value"

    val reference_expected =
      definition_rhs "automatic_read_expected_reference"

    val reference_parameter =
      definition_rhs "automatic_read_reference_parameter"

    val immutable_reference =
      checked
        ("let reference = \<llangle>automatic_read_reference_value\<rrangle>; " ^
         "reference")

    val borrowed_reference =
      checked
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let reference = &value; reference")

    val reference_call =
      checked
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "automatic_read_reference_call(value)")

    val propagated_reference =
      checked
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let references = [value]; *(references[0_usize])")

    val assignment =
      checked
        ("let mut target = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut source = \<llangle>2 :: 32 word\<rrangle>; " ^
         "target = source; target")

    val _ =
      equivalent "mutable scalar"
        "let mut value = \<llangle>1 :: 32 word\<rrangle>; value"
        "let mut value = \<llangle>1 :: 32 word\<rrangle>; *value"

    val _ =
      equivalent "field projection"
        ("let mut value = \<llangle>automatic_read_record_value\<rrangle>; " ^
         "value.automatic_read_field")
        ("let mut value = \<llangle>automatic_read_record_value\<rrangle>; " ^
         "*(value.automatic_read_field)")

    val _ =
      equivalent "index projection"
        ("let mut values = \<llangle>automatic_read_array_value\<rrangle>; " ^
         "values[0_usize]")
        ("let mut values = \<llangle>automatic_read_array_value\<rrangle>; " ^
         "*(values[0_usize])")

    val _ =
      equivalent "initializer"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let copy = value; copy")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let copy = *value; copy")

    val _ =
      equivalent "call argument"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "automatic_read_value_call(value)")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "automatic_read_value_call(*value)")

    val _ =
      equivalent "return operand"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; return value;")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; return *value;")

    val _ =
      equivalent "operator operand"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; value + 1_u32")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; *value + 1_u32")

    val _ =
      equivalent "condition"
        ("let mut flag = \<llangle>True\<rrangle>; " ^
         "if flag { 1_u32 } else { 0_u32 }")
        ("let mut flag = \<llangle>True\<rrangle>; " ^
         "if *flag { 1_u32 } else { 0_u32 }")

    val _ =
      equivalent "match scrutinee"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "match_switch value { 0 \<Rightarrow> false, _ \<Rightarrow> true }")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "match_switch *value { 0 \<Rightarrow> false, _ \<Rightarrow> true }")

    val _ =
      equivalent "tuple aggregate"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "(value, 2_u32)")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "(*value, 2_u32)")

    val _ =
      equivalent "array aggregate"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; [value]")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; [*value]")

    val _ =
      equivalent "cast operand"
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; value as u64")
        ("let mut value = \<llangle>1 :: 32 word\<rrangle>; *value as u64")

    val _ =
      equivalent "iterable"
        ("let mut values = \<llangle>automatic_read_array_value\<rrangle>; " ^
         "for value in values { () }")
        ("let mut values = \<llangle>automatic_read_array_value\<rrangle>; " ^
         "for value in *values { () }")

    val _ =
      equivalent "assignment right-hand side"
        ("let mut target = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut source = \<llangle>2 :: 32 word\<rrangle>; " ^
         "target = source; target")
        ("let mut target = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut source = \<llangle>2 :: 32 word\<rrangle>; " ^
         "target = *source; *target")

    val _ =
      audit_assert "an unconstrained scalar place was not read once"
        (dereference_count scalar_implicit = 1)

    val _ =
      audit_assert "a nested reference place was not read exactly once"
        (dereference_count nested_implicit = 1)

    val _ =
      audit_assert "an explicit dereference was adjusted a second time"
        (dereference_count explicit_once = 1)

    val _ =
      audit_assert "a reference-typed result did not retain its place"
        (dereference_count reference_expected = 0)

    val _ =
      audit_assert "a reference parameter was automatically read"
        (dereference_count reference_parameter = 0)

    val _ =
      audit_assert "an immutable reference value was automatically read"
        (dereference_count immutable_reference = 0)

    val _ =
      audit_assert "a borrow result was automatically read"
        (dereference_count borrowed_reference = 0)

    val _ =
      audit_assert "a reference-typed call argument was automatically read"
        (dereference_count reference_call = 0)

    val _ =
      audit_assert
        "a later reference expectation did not propagate through an aggregate"
        (dereference_count propagated_reference = 1)

    val _ =
      audit_assert
        "assignment added a read at its target or missed a value-side read"
        (dereference_count assignment = 2)
  in
    val _ = ()
  end
\<close>

no_adhoc_overloading index_const \<rightleftharpoons> parser_reference_array_index_fixture
no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

end
