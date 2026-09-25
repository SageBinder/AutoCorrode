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

urust_expr automatic_read_expression_parameter_shadow ::
  \<open>
    (unit, unit, 32 word) Global_Store.ref \<Rightarrow>
    (unit, (unit, unit, 32 word) Global_Store.ref, unit, unit, unit, unit) expression
  \<close>
  ("value")
  \<open> let mut value = value; value \<close>

urust_expr automatic_read_expression_parameter_shadow_explicit ::
  \<open>
    (unit, unit, 32 word) Global_Store.ref \<Rightarrow>
    (unit, (unit, unit, 32 word) Global_Store.ref, unit, unit, unit, unit) expression
  \<close>
  ("value")
  \<open> let mut value = value; *value \<close>

urust_fn automatic_read_function_parameter_shadow ::
  \<open>
    32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  ("value")
  \<open> let mut value = value; value \<close>

urust_fn automatic_read_function_parameter_shadow_explicit ::
  \<open>
    32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body
  \<close>
  ("value")
  \<open> let mut value = value; *value \<close>

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

section\<open>Shadowing and environment integrity\<close>

text\<open>
Every row below elaborates both an implicit-read source and an explicit control source. The checked
terms must be alpha-equivalent, contain exactly the expected selected dereferences and mutable
allocations, and contain no unresolved internal read-adjustment marker.
\<close>

ML\<open>
structure Automatic_Read_Shadowing_Audit =
struct
  val dereference_name =
    \<^const_name>\<open>parser_dereference_fixture\<close>
  val reference_name =
    \<^const_name>\<open>parser_reference_fixture\<close>
  val adjustment_name =
    \<^const_name>\<open>urust_internal_read_adjustment\<close>

  fun checked ctxt source =
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

  fun render ctxt term = Syntax.string_of_term ctxt term

  fun fail ctxt label reason
      expected_reads actual_implicit_reads actual_explicit_reads
      expected_allocations actual_implicit_allocations
      actual_explicit_allocations implicit explicit =
    error
      ("automatic read shadowing audit " ^ quote label ^ ": " ^ reason ^ "\n" ^
       "expected dereferences: " ^ string_of_int expected_reads ^ "\n" ^
       "actual implicit dereferences: " ^
         string_of_int actual_implicit_reads ^ "\n" ^
       "actual explicit dereferences: " ^
         string_of_int actual_explicit_reads ^ "\n" ^
       "expected allocations: " ^ string_of_int expected_allocations ^ "\n" ^
       "actual implicit allocations: " ^
         string_of_int actual_implicit_allocations ^ "\n" ^
       "actual explicit allocations: " ^
         string_of_int actual_explicit_allocations ^ "\n" ^
       "implicit term: " ^ render ctxt implicit ^ "\n" ^
       "explicit term: " ^ render ctxt explicit)

  fun check_row ctxt
      {label, implicit_source, explicit_source, reads, allocations} =
    let
      val implicit = checked ctxt implicit_source
      val explicit = checked ctxt explicit_source
      val implicit_reads = count_constant dereference_name implicit
      val explicit_reads = count_constant dereference_name explicit
      val implicit_allocations = count_constant reference_name implicit
      val explicit_allocations = count_constant reference_name explicit
      val implicit_adjustments = count_constant adjustment_name implicit
      val explicit_adjustments = count_constant adjustment_name explicit
      fun reject reason =
        fail ctxt label reason
          reads implicit_reads explicit_reads
          allocations implicit_allocations explicit_allocations
          implicit explicit
    in
      if not (Term.aconv (implicit, explicit)) then
        reject "implicit and explicit controls are not alpha-equivalent"
      else if implicit_reads <> reads orelse explicit_reads <> reads then
        reject "dereference count changed"
      else if implicit_allocations <> allocations orelse
          explicit_allocations <> allocations then
        reject "reference-allocation count changed"
      else if implicit_adjustments <> 0 orelse explicit_adjustments <> 0 then
        reject
          ("an internal read marker survived checking (implicit " ^
           string_of_int implicit_adjustments ^ ", explicit " ^
           string_of_int explicit_adjustments ^ ")")
      else ()
    end

  fun check_rows ctxt rows = List.app (check_row ctxt) rows

  fun definition_rhs ctxt name =
    Proof_Context.get_thm ctxt (name ^ "_def")
    |> Thm.prop_of
    |> Logic.dest_equals
    |> snd
    |> Term_Position.strip_positions

  fun check_definition_pair ctxt
      {label, implicit_name, explicit_name, reads, allocations} =
    let
      val implicit = definition_rhs ctxt implicit_name
      val explicit = definition_rhs ctxt explicit_name
      val implicit_reads = count_constant dereference_name implicit
      val explicit_reads = count_constant dereference_name explicit
      val implicit_allocations = count_constant reference_name implicit
      val explicit_allocations = count_constant reference_name explicit
      val implicit_adjustments = count_constant adjustment_name implicit
      val explicit_adjustments = count_constant adjustment_name explicit
      fun reject reason =
        fail ctxt label reason
          reads implicit_reads explicit_reads
          allocations implicit_allocations explicit_allocations
          implicit explicit
    in
      if not (Term.aconv (implicit, explicit)) then
        reject "implicit and explicit declaration bodies are not alpha-equivalent"
      else if implicit_reads <> reads orelse explicit_reads <> reads then
        reject "declaration dereference count changed"
      else if implicit_allocations <> allocations orelse
          explicit_allocations <> allocations then
        reject "declaration reference-allocation count changed"
      else if implicit_adjustments <> 0 orelse explicit_adjustments <> 0 then
        reject
          ("an internal read marker survived declaration checking (implicit " ^
           string_of_int implicit_adjustments ^ ", explicit " ^
           string_of_int explicit_adjustments ^ ")")
      else ()
    end
end
\<close>

ML_val\<open>
  Automatic_Read_Shadowing_Audit.check_rows \<^context>
    [
      {label = "ordinary value to mutable scalar",
       implicit_source =
         "let value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut value = value; value",
       explicit_source =
         "let value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut value = value; *value",
       reads = 1, allocations = 1},
      {label = "immutable reference value to mutable scalar",
       implicit_source =
         "let value = \<llangle>automatic_read_reference_value\<rrangle>; " ^
         "let mut value = value; value",
       explicit_source =
         "let value = \<llangle>automatic_read_reference_value\<rrangle>; " ^
         "let mut value = value; *value",
       reads = 1, allocations = 1},
      {label = "mutable scalar to ordinary immutable value",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let value = value; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let value = *value; value",
       reads = 1, allocations = 1},
      {label = "mutable scalar to immutable reference value",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let value = &value; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let value = &value; value",
       reads = 0, allocations = 1},
      {label = "mutable scalar to mutable scalar",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut value = value; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut value = *value; *value",
       reads = 2, allocations = 2},
      {label = "mutable reference payload reads one level",
       implicit_source =
         "let mut value = \<llangle>automatic_read_reference_value\<rrangle>; value",
       explicit_source =
         "let mut value = \<llangle>automatic_read_reference_value\<rrangle>; *value",
       reads = 1, allocations = 1},
      {label = "storage reference storage alternation",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let outer = { " ^
           "let value = value; " ^
           "let inner = { let mut value = value; value }; " ^
           "value " ^
         "}; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let outer = { " ^
           "let value = *value; " ^
           "let inner = { let mut value = value; *value }; " ^
           "value " ^
         "}; *value",
       reads = 3, allocations = 2},
      {label = "successive initializer and body ownership",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let value = value; let mut value = value; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let value = *value; let mut value = value; *value",
       reads = 2, allocations = 2},
      {label = "const shadows storage",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "const value = value; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "const value = *value; value",
       reads = 1, allocations = 1},
      {label = "block restores outer storage",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let inner = { let value = value; value }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let inner = { let value = *value; value }; *value",
       reads = 2, allocations = 1},
      {label = "block restores outer reference value",
       implicit_source =
         "let value = \<llangle>automatic_read_reference_value\<rrangle>; " ^
         "let inner = { let mut value = value; value }; value",
       explicit_source =
         "let value = \<llangle>automatic_read_reference_value\<rrangle>; " ^
         "let inner = { let mut value = value; *value }; value",
       reads = 1, allocations = 1},
      {label = "if branches isolate categories",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let branch = if true { let value = value; value } " ^
         "else { let mut value = value; value }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let branch = if true { let value = *value; value } " ^
         "else { let mut value = *value; *value }; *value",
       reads = 4, allocations = 2},
      {label = "ordinary tuple destructuring",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let (value, other) = (value, \<llangle>2 :: 32 word\<rrangle>); value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let (value, other) = (*value, \<llangle>2 :: 32 word\<rrangle>); value",
       reads = 1, allocations = 1},
      {label = "nested tuple destructuring",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let (other, (value, retained)) = " ^
           "(\<llangle>2 :: 32 word\<rrangle>, " ^
            "(value, \<llangle>3 :: 32 word\<rrangle>)); value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let (other, (value, retained)) = " ^
           "(\<llangle>2 :: 32 word\<rrangle>, " ^
            "(*value, \<llangle>3 :: 32 word\<rrangle>)); value",
       reads = 1, allocations = 1},
      {label = "mutable tuple preserves plain rhs behavior",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut (value, other) = " ^
           "(value, \<llangle>2 :: 32 word\<rrangle>); value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut (value, other) = " ^
           "(*value, \<llangle>2 :: 32 word\<rrangle>); value",
       reads = 1, allocations = 1},
      {label = "direct match arm restoration",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let selected = match Some(value) { " ^
           "Some(value) \<Rightarrow> value, None \<Rightarrow> value }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let selected = match Some(*value) { " ^
           "Some(value) \<Rightarrow> value, None \<Rightarrow> *value }; *value",
       reads = 3, allocations = 1},
      {label = "explicit match case arm restoration",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let selected = match_case Some(value) { " ^
           "Some(value) \<Rightarrow> value, None \<Rightarrow> value }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let selected = match_case Some(*value) { " ^
           "Some(value) \<Rightarrow> value, None \<Rightarrow> *value }; *value",
       reads = 3, allocations = 1},
      {label = "same-spelled sibling match arm binders",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let selected = match Ok(value) { " ^
           "Ok(value) \<Rightarrow> value, Err(value) \<Rightarrow> value }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let selected = match Ok(*value) { " ^
           "Ok(value) \<Rightarrow> value, Err(value) \<Rightarrow> value }; *value",
       reads = 2, allocations = 1},
      {label = "alias binder shadows storage",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "match Some(value) { " ^
           "whole @ Some(value) \<Rightarrow> value, _ \<Rightarrow> value }",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "match Some(*value) { " ^
           "whole @ Some(value) \<Rightarrow> value, _ \<Rightarrow> *value }",
       reads = 2, allocations = 1},
      {label = "or pattern shares one non-storage binder",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "match Ok(value) { " ^
           "Ok(value) | Err(value) " ^
             "\<Rightarrow> value }",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "match Ok(*value) { " ^
           "Ok(value) | Err(value) " ^
             "\<Rightarrow> value }",
       reads = 1, allocations = 1},
      {label = "if let success and fallback isolation",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "if let Some(value) = Some(value) { value } else { value }",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "if let Some(value) = Some(*value) { value } else { *value }",
       reads = 2, allocations = 1},
      {label = "while let body and outer restoration",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] " ^
           "while let Some(value) = Some(value) { " ^
             "let observed = value; () }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] " ^
           "while let Some(value) = Some(*value) { " ^
             "let observed = value; () }; *value",
       reads = 2, allocations = 1},
      {label = "let else continuation and fallback isolation",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let Some(value) = Some(value) else { return value; }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let Some(value) = Some(*value) else { return *value; }; value",
       reads = 2, allocations = 1},
      {label = "for binder restores outer storage",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "for value in \<llangle>[2 :: 32 word]\<rrangle> { " ^
           "let observed = value; () }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "for value in \<llangle>[2 :: 32 word]\<rrangle> { " ^
           "let observed = value; () }; *value",
       reads = 1, allocations = 1},
      {label = "closure duplicate formal last wins",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let closure = |value, value| \<llangle>value :: 32 word\<rrangle>; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let closure = |value, value| \<llangle>value :: 32 word\<rrangle>; *value",
       reads = 1, allocations = 1},
      {label = "ordinary wildcard preserves outer storage",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let _ = value; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let _ = *value; *value",
       reads = 2, allocations = 1},
      {label = "mutable wildcard preserves outer storage",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut _ = value; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let mut _ = *value; *value",
       reads = 2, allocations = 2},
      {label = "tuple wildcard preserves neighboring storage",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let (_, other) = (value, \<llangle>2 :: 32 word\<rrangle>); value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let (_, other) = (*value, \<llangle>2 :: 32 word\<rrangle>); *value",
       reads = 2, allocations = 1},
      {label = "assignment target is not read",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let inner = { " ^
           "let mut value = \<llangle>2 :: 32 word\<rrangle>; " ^
           "value = value; () }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let inner = { " ^
           "let mut value = \<llangle>2 :: 32 word\<rrangle>; " ^
           "value = *value; () }; *value",
       reads = 2, allocations = 2},
      {label = "borrow preserves selected inner place",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let reference = { let mut value = value; &value }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let reference = { let mut value = *value; &value }; *value",
       reads = 2, allocations = 2},
      {label = "reference call expectation suppresses inner read",
       implicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let result = { " ^
           "let mut value = \<llangle>2 :: 32 word\<rrangle>; " ^
           "automatic_read_reference_call(value) }; value",
       explicit_source =
         "let mut value = \<llangle>1 :: 32 word\<rrangle>; " ^
         "let result = { " ^
           "let mut value = \<llangle>2 :: 32 word\<rrangle>; " ^
           "automatic_read_reference_call(value) }; *value",
       reads = 1, allocations = 2},
      {label = "registered notation shadowed by mutable local",
       implicit_source =
         "let mut myReg = myReg; myReg",
       explicit_source =
         "let mut myReg = myReg; *myReg",
       reads = 1, allocations = 1}
    ]
\<close>

ML_val\<open>
  Automatic_Read_Shadowing_Audit.check_definition_pair \<^context>
    {label = "typed urust_expr parameter shadow",
     implicit_name = "automatic_read_expression_parameter_shadow",
     explicit_name = "automatic_read_expression_parameter_shadow_explicit",
     reads = 1, allocations = 1};
  Automatic_Read_Shadowing_Audit.check_definition_pair \<^context>
    {label = "typed urust_fn parameter shadow",
     implicit_name = "automatic_read_function_parameter_shadow",
     explicit_name = "automatic_read_function_parameter_shadow_explicit",
     reads = 1, allocations = 1}
\<close>

context fixes automatic_read_fix :: \<open>32 word\<close>
begin

ML_val\<open>
  Automatic_Read_Shadowing_Audit.check_rows \<^context>
    [
      {label = "HOL context fix shadowed by mutable local",
       implicit_source =
         "let mut automatic_read_fix = automatic_read_fix; automatic_read_fix",
       explicit_source =
         "let mut automatic_read_fix = automatic_read_fix; *automatic_read_fix",
       reads = 1, allocations = 1}
    ]
\<close>

end

no_adhoc_overloading index_const \<rightleftharpoons> parser_reference_array_index_fixture
no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

end
