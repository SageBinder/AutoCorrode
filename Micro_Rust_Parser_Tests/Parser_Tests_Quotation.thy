(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Tests_Quotation
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Term_Hook
begin

section\<open>Closed explicit-capture quotation\<close>

text\<open>
This is the complete test suite for the opt-in quotation. Tests are grouped by observable contract
rather than by whether a case succeeds or fails: public syntax and capture semantics, exact
dependency resolution, fail-closed preflight, parser-pipeline behavior, delayed conformance, markup,
diagnostics, and removal of internal markers.
\<close>

subsection\<open>Public forms and captures\<close>

lemma omitted_capture_is_empty:
  "\<mu>\<open> 1 \<close> = \<mu>()\<open> 1 \<close>"
  by (rule refl)

lemma public_layout:
  "\<mu>(x := 1, y := 2,)\<open>
      (x, y)
    \<close> =
   \<mu>(x := 1, y := 2)\<open> (x, y) \<close>"
  by (rule refl)

lemma capture_rhs_tuple_and_type_constraint:
  "\<mu>(captured := ((1 :: nat), True))\<open> captured \<close> =
   Core_Expression.literal ((1 :: nat), True)"
  by (rule refl)

context
  fixes x y :: nat
begin

lemma capture_under_outer_lambda:
  "(\<lambda>x. \<mu>(captured := x)\<open> captured \<close>) =
   (\<lambda>x. Core_Expression.literal x)"
  by (rule refl)

lemma capture_same_name_as_outer_lambda:
  "(\<lambda>x. \<mu>(x := x)\<open> x \<close>) =
   (\<lambda>x. Core_Expression.literal x)"
  by (rule refl)

lemma arbitrary_capture_rhs:
  "\<mu>(captured := (case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n))\<open>
      captured
    \<close> =
   Core_Expression.literal
     (case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n)"
  by (rule refl)

lemma simultaneous_capture_rhs:
  "\<mu>(left := y, right := x)\<open> (left, right) \<close> =
   \<mu>(first := y, second := x)\<open> (first, second) \<close>"
  by (rule refl)

lemma simultaneous_captures_do_not_scope_over_rhs:
  "(\<lambda>x y.
      \<mu>(x := y, y := x)\<open> (x, y) \<close>) =
   (\<lambda>x y.
      \<mu>(first := y, second := x)\<open>
        (first, second)
      \<close>)"
  by (rule refl)

lemma capture_under_outer_let:
  "(let z = x + y in \<mu>(captured := z)\<open> captured \<close>) =
   (let z = x + y in Core_Expression.literal z)"
  by (rule refl)

lemma capture_under_outer_case:
  "(case Some x of
      None \<Rightarrow> \<mu>\<open> 0 \<close>
    | Some z \<Rightarrow> \<mu>(captured := z)\<open> captured \<close>) =
   (case Some x of
      None \<Rightarrow> Core_Expression.literal 0
    | Some z \<Rightarrow> Core_Expression.literal z)"
  by (rule refl)

lemma lexical_shadowing:
  "\<mu>(captured := x, inner := y)\<open>
      let saved = captured;
      let captured = inner;
      (saved, captured)
    \<close> =
   \<mu>(outer := x, inner := y)\<open>
      let saved = outer;
      let outer = inner;
      (saved, outer)
    \<close>"
  by (rule refl)

end

context
  fixes contextual :: nat
begin

lemma context_fix_capture:
  "\<mu>(captured := contextual)\<open> captured \<close> =
   Core_Expression.literal contextual"
  by (rule refl)

end

lemma nested_quotation_capture_operand:
  "\<mu>(
      nested := (\<mu>(value := (1 :: nat))\<open> value \<close> ::
        (unit, nat, unit, unit, unit, unit) expression)
    )\<open>
      (nested, nested)
    \<close> =
   \<mu>(
      nested := (\<mu>(value := (1 :: nat))\<open> value \<close> ::
        (unit, nat, unit, unit, unit, unit) expression),
    )\<open>
      (nested, nested)
    \<close>"
  by (rule refl)

lemma captured_callable:
  "\<mu>(
      function := lift_fun1 Suc,
      argument := (1 :: nat)
    )\<open>
      function(argument)
    \<close> =
   \<mu>(
      callable := lift_fun1 Suc,
      value := (1 :: nat)
    )\<open>
      callable(value)
    \<close>"
  by (rule refl)

context
begin

private definition private_quotation_capture :: nat
  where
    "private_quotation_capture = 7"

lemma capture_operand_preserves_concealed_constant_identity:
  "(\<lambda>private_quotation_capture :: nat.
      \<mu>(captured := CONST private_quotation_capture)\<open>
        captured
      \<close>) =
   (\<lambda>private_quotation_capture :: nat.
      Core_Expression.literal
        (CONST private_quotation_capture))"
  by (rule refl)

end

subsection\<open>Declared dependency roles\<close>

datatype quotation_option =
    Quotation_Some nat
  | Quotation_None

datatype quotation_or =
    Quotation_Left nat
  | Quotation_Right nat

datatype_record quotation_record =
  quotation_record_value :: nat
micro_rust_record quotation_record

definition quotation_some_call ::
    "nat \<Rightarrow>
      (unit, quotation_option, unit, unit, unit) function_body"
  where
    "quotation_some_call \<equiv> lift_fun1 Quotation_Some"

definition quotation_increment ::
    "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
  where
    "quotation_increment \<equiv> lift_fun1 Suc"

definition quotation_left_call ::
    "nat \<Rightarrow> (unit, quotation_or, unit, unit, unit) function_body"
  where
    "quotation_left_call \<equiv> lift_fun1 Quotation_Left"

definition quotation_right_call ::
    "nat \<Rightarrow> (unit, quotation_or, unit, unit, unit) function_body"
  where
    "quotation_right_call \<equiv> lift_fun1 Quotation_Right"

definition quotation_identity_lens ::
    "(quotation_record, quotation_record) lens"
  where
    "quotation_identity_lens \<equiv> id\<^sub>L"

definition quotation_literal :: nat
  where
    "quotation_literal = 7"

definition quotation_record_call ::
    "nat \<Rightarrow>
      (unit, quotation_record, unit, unit, unit) function_body"
  where
    "quotation_record_call \<equiv> lift_fun1 make_quotation_record"

definition quotation_dual_call ::
    "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
  where
    "quotation_dual_call \<equiv> lift_fun1 Suc"

definition quotation_dual_literal :: nat
  where
    "quotation_dual_literal = 3"

definition quotation_call_only ::
    "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
  where
    "quotation_call_only \<equiv> lift_fun1 Suc"

definition quotation_call_only_literal_left :: nat
  where
    "quotation_call_only_literal_left = 4"

definition quotation_call_only_literal_right :: nat
  where
    "quotation_call_only_literal_right = 5"

definition quotation_literal_only :: nat
  where
    "quotation_literal_only = 6"

definition quotation_literal_only_call_left ::
    "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
  where
    "quotation_literal_only_call_left \<equiv> lift_fun1 Suc"

definition quotation_literal_only_call_right ::
    "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
  where
    "quotation_literal_only_call_right \<equiv> lift_fun1 (\<lambda>x. x + 2)"

micro_rust_notation (call)
  quotation_some_call ("Quotation::Some")
micro_rust_notation (literal)
  quotation_option.Quotation_Some ("Quotation::Some")
micro_rust_notation (literal)
  quotation_option.Quotation_None ("Quotation::None")
micro_rust_notation (literal)
  quotation_option.Quotation_None ("quotation_none")
micro_rust_notation (call)
  quotation_left_call ("Quotation::Left")
micro_rust_notation (literal)
  quotation_or.Quotation_Left ("Quotation::Left")
micro_rust_notation (call)
  quotation_right_call ("Quotation::Right")
micro_rust_notation (literal)
  quotation_or.Quotation_Right ("Quotation::Right")
micro_rust_notation (call)
  quotation_increment ("quotation_increment")
micro_rust_notation (call)
  quotation_increment ("quotation_method")
micro_rust_notation (field)
  quotation_identity_lens ("quotation_field")
micro_rust_notation (literal)
  quotation_literal ("Quotation::Seven")
micro_rust_notation (literal)
  quotation_literal ("quotation_seven")
micro_rust_notation (literal)
  quotation_literal ("quotation_collision")
micro_rust_notation (call)
  quotation_record_call ("Quotation::Record")
micro_rust_notation (call)
  quotation_dual_call ("quotation_dual")
micro_rust_notation (literal)
  quotation_dual_literal ("quotation_dual")
micro_rust_notation (call)
  quotation_call_only ("quotation_call_only")
micro_rust_notation (literal)
  quotation_call_only_literal_left ("quotation_call_only")
micro_rust_notation (literal)
  quotation_call_only_literal_right ("quotation_call_only")
micro_rust_notation (literal)
  quotation_literal_only ("quotation_literal_only")
micro_rust_notation (call)
  quotation_literal_only_call_left ("quotation_literal_only")
micro_rust_notation (call)
  quotation_literal_only_call_right ("quotation_literal_only")

lemma combined_modifier_layout:
  "\<mu>(x := (1 :: nat),)
      [using \<open>quotation_increment\<close>,]
      \<open> quotation_increment(x) \<close> =
   \<mu>(x := (1 :: nat))[using \<open>quotation_increment\<close>]\<open>
      quotation_increment(x)
    \<close>"
  by (rule refl)

lemma literal_dependency:
  "\<mu>[using \<open>Quotation::Seven\<close>]\<open>
      Quotation::Seven
    \<close> =
   \<mu>[using \<open>Quotation::Seven\<close>,]\<open>
      Quotation::Seven
    \<close>"
  by (rule refl)

lemma call_dependency:
  "\<mu>[using \<open>quotation_increment\<close>]\<open>
      quotation_increment(1)
    \<close> =
   \<mu>[using \<open>quotation_increment\<close>,]\<open>
      quotation_increment(1)
    \<close>"
  by (rule refl)

lemma dependency_is_selected_per_used_role:
  "\<mu>[using \<open>quotation_call_only\<close>]\<open>
      quotation_call_only(1)
    \<close> =
   \<lbrakk> quotation_call_only(1) \<rbrakk>"
  by (rule refl)

lemma unused_role_ambiguity_does_not_poison_literal_use:
  "\<mu>[using \<open>quotation_literal_only\<close>]\<open>
      quotation_literal_only
    \<close> =
   Core_Expression.literal quotation_literal_only"
  by (rule refl)

lemma one_dependency_can_supply_multiple_roles:
  "\<mu>[using \<open>quotation_dual\<close>]\<open>
      quotation_dual(quotation_dual)
    \<close> =
   \<lbrakk> quotation_dual(quotation_dual) \<rbrakk>"
  by (rule refl)

lemma repeated_dependency_use_needs_one_declaration:
  "\<mu>[using \<open>quotation_increment\<close>]\<open>
      (quotation_increment(1), quotation_increment(2))
    \<close> =
   \<lbrakk> (quotation_increment(1), quotation_increment(2)) \<rbrakk>"
  by (rule refl)

lemma method_dependency:
  "\<mu>(value := (1 :: nat))[using \<open>quotation_method\<close>]\<open>
      value.quotation_method()
    \<close> =
   \<mu>(value := (1 :: nat),)[using \<open>quotation_method\<close>,]\<open>
      value.quotation_method()
    \<close>"
  by (rule refl)

lemma field_dependency:
  "(\<mu>(value := make_quotation_record 1)[using \<open>quotation_field\<close>]\<open>
      value.quotation_field
    \<close> ::
      (unit, quotation_record, unit, unit, unit, unit) expression) =
   (\<mu>(value := make_quotation_record 1,)[using \<open>quotation_field\<close>,]\<open>
      value.quotation_field
    \<close> ::
      (unit, quotation_record, unit, unit, unit, unit) expression)"
  by (rule refl)

lemma struct_call_dependency:
  "\<mu>(value := (1 :: nat))[using \<open>Quotation::Record\<close>]\<open>
      Quotation::Record { value: value }
    \<close> =
   \<mu>(value := (1 :: nat))[using \<open>Quotation::Record\<close>]\<open>
      Quotation::Record(value)
    \<close>"
  by (rule refl)

lemma constructor_and_call_dependency:
  "(\<mu>(value := (1 :: nat))[using \<open>Quotation::Some\<close>, \<open>Quotation::None\<close>]\<open>
      match_case Quotation::Some(value) {
        Quotation::Some(result) \<Rightarrow> result,
        Quotation::None \<Rightarrow> 0
      }
    \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   (\<mu>(value := (1 :: nat))[using \<open>Quotation::Some\<close>, \<open>Quotation::None\<close>,]\<open>
      match_case Quotation::Some(value) {
        Quotation::Some(result) \<Rightarrow> result,
        Quotation::None \<Rightarrow> 0
      }
    \<close> ::
      (unit, nat, unit, unit, unit, unit) expression)"
  by (rule refl)

lemma explicit_switch_identifier_dependency:
  "(\<mu>(value := (7 :: nat))[using \<open>quotation_seven\<close>]\<open>
      match_switch value {
        quotation_seven \<Rightarrow> 1,
        _ \<Rightarrow> 0
      }
    \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   \<mu>(value := (7 :: nat))[using \<open>quotation_seven\<close>]\<open>
      match_switch value {
        quotation_seven \<Rightarrow> 1,
        _ \<Rightarrow> 0
      }
    \<close>"
  by (rule refl)

lemma automatic_numeric_match_dependency:
  "(\<mu>(value := (7 :: nat))[using \<open>quotation_seven\<close>]\<open>
      match value {
        quotation_seven \<Rightarrow> 1,
        0 \<Rightarrow> 2,
        _ \<Rightarrow> 0
      }
    \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   \<mu>(value := (7 :: nat))[using \<open>quotation_seven\<close>]\<open>
      match_switch value {
        quotation_seven \<Rightarrow> 1,
        0 \<Rightarrow> 2,
        _ \<Rightarrow> 0
      }
    \<close>"
  by (rule refl)

lemma case_constructor_identifier_dependency:
  "(\<mu>(value := Quotation_None)[using \<open>quotation_none\<close>]\<open>
      match_case value {
        quotation_none \<Rightarrow> 1,
        _ \<Rightarrow> 0
      }
    \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   \<mu>(value := Quotation_None)[using \<open>quotation_none\<close>]\<open>
      match_case value {
        quotation_none \<Rightarrow> 1,
        _ \<Rightarrow> 0
      }
    \<close>"
  by (rule refl)

lemma captured_name_shadows_registered_function:
  "\<mu>(
      quotation_increment := lift_fun1 (\<lambda>x :: nat. x + 2),
      value := (1 :: nat)
    )\<open>
      quotation_increment(value)
    \<close> =
   \<mu>(
      function := lift_fun1 (\<lambda>x :: nat. x + 2),
      value := (1 :: nat)
    )\<open>
      function(value)
    \<close>"
  by (rule refl)

subsection\<open>Lexical scope and intrinsic forms\<close>

lemma tuple_binders_are_lexical:
  "\<mu>(left := (1 :: nat), right := (2 :: nat))\<open>
      let (first, second) = (left, right);
      (first, second)
    \<close> =
   \<mu>(left := (1 :: nat), right := (2 :: nat))\<open>
      let (renamed_left, renamed_right) = (left, right);
      (renamed_left, renamed_right)
    \<close>"
  by (rule refl)

lemma log_data_accepts_capture_and_lexical_identifiers:
  "\<mu>(captured := (1 :: nat))\<open>
      let local = captured;
      l\<llangle>\"value=\", local\<rrangle>
    \<close> =
   \<mu>(captured := (1 :: nat))\<open>
      let renamed = captured;
      l\<llangle>\"value=\", renamed\<rrangle>
    \<close>"
  by (rule refl)

lemma conditional_binding_scope:
  "(\<mu>(value := Quotation_Some 1)
      [using \<open>Quotation::Some\<close>]
      \<open>
        if let Quotation::Some(result) = value {
          result
        } else {
          0
        }
      \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   (\<mu>(value := Quotation_Some 1)
      [using \<open>Quotation::Some\<close>, \<open>Quotation::None\<close>]
      \<open>
        match_case value {
          Quotation::Some(result) \<Rightarrow> result,
          Quotation::None \<Rightarrow> 0
        }
      \<close> ::
      (unit, nat, unit, unit, unit, unit) expression)"
  by (rule refl)

lemma let_else_continuation_scope:
  "(\<mu>(value := Quotation_Some 1)
      [using \<open>Quotation::Some\<close>]
      \<open>
        let Quotation::Some(result) = value else { 0 };
        result
      \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   (\<mu>(value := Quotation_Some 1)
      [using \<open>Quotation::Some\<close>]
      \<open>
        let Quotation::Some(renamed) = value else { 0 };
        renamed
      \<close> ::
      (unit, nat, unit, unit, unit, unit) expression)"
  by (rule refl)

lemma equal_binder_or_patterns_share_one_scope:
  "(\<mu>(value := Quotation_Left 1)
      [using \<open>Quotation::Left\<close>, \<open>Quotation::Right\<close>]
      \<open>
        match_case value {
          Quotation::Left(result) | Quotation::Right(result) \<Rightarrow> result
        }
      \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   (\<mu>(value := Quotation_Left 1)
      [using \<open>Quotation::Left\<close>, \<open>Quotation::Right\<close>]
      \<open>
        match_case value {
          Quotation::Left(renamed) | Quotation::Right(renamed) \<Rightarrow> renamed
        }
      \<close> ::
      (unit, nat, unit, unit, unit, unit) expression)"
  by (rule refl)

subsection\<open>Expected type and conformance\<close>

lemma expected_result_type:
  "(\<mu>\<open> 0 \<close> ::
      ('s, nat, 'r, 'abort, 'input, 'output) expression) =
   Core_Expression.literal 0"
  by (rule refl)

lemma expected_type_flows_into_polymorphic_capture:
  "(\<mu>(captured := None)\<open> captured \<close> ::
      ('s, nat option, 'r, 'abort, 'input, 'output) expression) =
   Core_Expression.literal (None :: nat option)"
  by (rule refl)

lemma callable_type_flows_into_unsuffixed_capture:
  "(\<mu>(captured := 1)[using \<open>quotation_increment\<close>]\<open>
      quotation_increment(captured)
    \<close> ::
      (unit, nat, unit, unit, unit, unit) expression) =
   \<lbrakk> quotation_increment(\<llangle>1 :: nat\<rrangle>) \<rbrakk>"
  by (rule refl)

declare [[urust_term_hook_conformance_check = true]]

lemma closed_conformance:
  "\<mu>\<open> 1 + 2 \<close> = \<lbrakk> 1 + 2 \<rbrakk>"
  by (rule refl)

lemma discarded_unsuffixed_numeral_conformance:
  "\<mu>\<open> let _ = 1; () \<close> =
   \<lbrakk> let _ = 1; () \<rbrakk>"
  by (rule refl)

lemma discarded_polymorphic_dependency_conformance:
  "\<mu>[using \<open>Quotation::None\<close>]\<open>
      let _ = Quotation::None;
      ()
    \<close> =
   \<lbrakk>
      let _ = Quotation::None;
      ()
    \<rbrakk>"
  by (rule refl)

context
  fixes x :: nat
begin

lemma capture_conformance:
  "\<mu>(captured := x)\<open> captured \<close> =
   \<lbrakk> x \<rbrakk>"
  by (rule refl)

lemma same_name_capture_conformance:
  "(\<lambda>x.
      \<mu>(x := x)\<open> x \<close>) =
   (\<lambda>x.
      \<lbrakk> x \<rbrakk>)"
  by (rule refl)

end

lemma cast_target_constraint_conformance:
  "(\<mu>(captured := (1 :: 32 word))\<open>
      captured as u64
    \<close> ::
      (unit, 64 word, unit, unit, unit, unit) expression) =
   (\<lbrakk> \<llangle>1 :: 32 word\<rrangle> as u64 \<rbrakk> ::
      (unit, 64 word, unit, unit, unit, unit) expression)"
  by (rule refl)

lemma dependency_conformance:
  "\<mu>[using \<open>quotation_increment\<close>]\<open>
      quotation_increment(1)
    \<close> =
   \<lbrakk> quotation_increment(1) \<rbrakk>"
  by (rule refl)

lemma closure_conformance:
  "\<mu>\<open> |x| x \<close> = \<lbrakk> |x| x \<rbrakk>"
  by (rule refl)

lemma yield_conformance:
  "\<mu>\<open> \<y>\<i>\<e>\<l>\<d>; () \<close> =
   \<lbrakk> \<y>\<i>\<e>\<l>\<d>; () \<rbrakk>"
  by (rule refl)

lemma nested_enabled_quotation_conformance:
  "(\<mu>(
      nested := (\<mu>(value := (1 :: nat))\<open> value \<close> ::
        (unit, nat, unit, unit, unit, unit) expression)
    )\<open>
      nested
    \<close> ::
      (unit,
       (unit, nat, unit, unit, unit, unit) expression,
       unit, unit, unit, unit) expression) =
   Core_Expression.literal
     (\<mu>(value := (1 :: nat))\<open> value \<close> ::
       (unit, nat, unit, unit, unit, unit) expression)"
  by (rule refl)

declare [[urust_term_hook_conformance_check = false]]

subsection\<open>Markup normalization\<close>

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("quotation markup normalization: " ^ message)

    val source_prefix =
      "\<mu>(captured := (1 :: nat))[using \<open>Quotation::Seven\<close>]"
    val body_text =
      "\<open> let _ = captured; let _ = 1; Quotation::Seven \<close>"
    val source_text = source_prefix ^ body_text
    val source_start =
      Position.make0 7 100 0 "" "urust-quotation-markup"
        "urust-quotation-markup"
    val source =
      Input.source false source_text
        (Position.range
          (source_start,
           Position.symbol_explode source_text source_start))

    fun capture enabled =
      let
        val captured =
          Synchronized.var
            ("urust_quotation_markup_" ^
              Bool.toString enabled)
            ([]: string list)
        fun capture_reports chunks =
          Synchronized.change captured (append chunks)
        val ctxt =
          Config.put urust_term_hook_conformance_check
            enabled \<^context>
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn
              capture_reports
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    ignore
                      (Syntax.parse_term ctxt
                        (Syntax.implode_input source))) ())
              ())
      in Synchronized.value captured end

    val disabled_reports = capture false
    val enabled_reports = capture true

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val disabled_markup =
      fold collect_markup
        (maps YXML.parse_body disabled_reports) []
    val enabled_markup =
      fold collect_markup
        (maps YXML.parse_body enabled_reports) []
    val markup = disabled_markup

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup

    fun has_entity kind position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties position)
        markup

    fun count_markup markup_name position reports =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          reports)

    fun count_entity kind position reports =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              has_position properties position)
          reports)

    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               ("quotation markup normalization: capture entity changed at" ^
                 Position.here position))
      end

    fun find_from needle offset =
      if offset + size needle > size source_text then
        error
          ("quotation markup normalization: missing " ^
            quote needle)
      else if
        String.substring
          (source_text, offset, size needle) = needle
      then offset
      else find_from needle (offset + 1)

    fun token_position needle offset =
      let
        val raw = find_from needle offset
        val start =
          Position.symbol_explode
            (String.substring (source_text, 0, raw)) source_start
      in
        (raw,
         Position.range_position
           (Position.range
             (start, Position.symbol_explode needle start)))
      end

    val cartouche_start =
      Position.symbol_explode source_prefix source_start
    val cartouche_pos =
      Position.range_position
        (Position.range
          (cartouche_start,
           Position.symbol_explode body_text cartouche_start))
    val (capture_definition_offset, capture_definition_pos) =
      token_position "captured" 0
    val (_, capture_reference_pos) =
      token_position "captured"
        (capture_definition_offset + size "captured")
    val (_, underscore_pos) =
      token_position "_" 0
    val (numeral_offset, numeral_pos) =
      token_position "1" (size source_prefix)
    val (_, constant_pos) =
      token_position "Seven" (numeral_offset + 1)

    val _ =
      assert "inner-syntax cartouche classification disappeared"
        (has_markup Markup.inner_cartoucheN cartouche_pos)
    val _ =
      assert "ordinary cartouche normalization has the wrong range"
        (has_markup Markup.cartoucheN cartouche_pos)
    val _ =
      assert "numeral markup was lost"
        (has_markup Markup.numeralN numeral_pos)
    val _ =
      assert "wildcard typing markup was lost"
        (has_markup Markup.typingN underscore_pos)
    val _ =
      assert "constant entity markup was lost"
        (has_entity Markup.constantN constant_pos)
    val _ =
      assert "capture definition lost bound markup"
        (has_markup Markup.boundN capture_definition_pos)
    val _ =
      assert "capture reference lost bound markup"
        (has_markup Markup.boundN capture_reference_pos)
    val _ =
      assert "capture navigation no longer joins clause and body"
        (entity_id Markup.defN capture_definition_pos =
          entity_id Markup.refN capture_reference_pos)
    val _ =
      assert "detached legacy parsing duplicated numeral reports"
        (count_markup Markup.numeralN numeral_pos enabled_markup =
          count_markup Markup.numeralN numeral_pos disabled_markup)
    val _ =
      assert "detached legacy parsing duplicated wildcard reports"
        (count_markup Markup.typingN underscore_pos enabled_markup =
          count_markup Markup.typingN underscore_pos disabled_markup)
    val _ =
      assert "detached legacy parsing duplicated constant reports"
        (count_entity Markup.constantN constant_pos enabled_markup =
          count_entity Markup.constantN constant_pos disabled_markup)
    val _ =
      assert "detached legacy parsing duplicated capture reports"
        (count_entity "urust_var" capture_reference_pos enabled_markup =
          count_entity "urust_var" capture_reference_pos disabled_markup)
  in
    val _ = writeln "Quotation markup normalization passed"
  end
\<close>

subsection\<open>Fail-closed diagnostics\<close>

definition quotation_ambiguous_left ::
    "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
  where
    "quotation_ambiguous_left \<equiv> lift_fun1 Suc"

definition quotation_ambiguous_right ::
    "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
  where
    "quotation_ambiguous_right \<equiv> lift_fun1 (\<lambda>x. x + 2)"

micro_rust_notation (call)
  quotation_ambiguous_left ("quotation_ambiguous")
micro_rust_notation (call)
  quotation_ambiguous_right ("quotation_ambiguous")

definition quotation_ambiguous_literal_left :: nat
  where
    "quotation_ambiguous_literal_left = 1"

definition quotation_ambiguous_literal_right :: nat
  where
    "quotation_ambiguous_literal_right = 2"

micro_rust_notation (literal)
  quotation_ambiguous_literal_left ("quotation_ambiguous_literal")
micro_rust_notation (literal)
  quotation_ambiguous_literal_right ("quotation_ambiguous_literal")

definition quotation_ambiguous_field_left ::
    "(quotation_record, quotation_record) lens"
  where
    "quotation_ambiguous_field_left \<equiv> id\<^sub>L"

definition quotation_ambiguous_field_right ::
    "(quotation_record, quotation_record) lens"
  where
    "quotation_ambiguous_field_right \<equiv> id\<^sub>L"

micro_rust_notation (field)
  quotation_ambiguous_field_left ("quotation_ambiguous_field")
micro_rust_notation (field)
  quotation_ambiguous_field_right ("quotation_ambiguous_field")

datatype quotation_unregistered_constructor =
  Quotation_Unregistered nat

ML_val\<open>
  local
    val ctxt = \<^context>

    fun plain_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))
        handle Fail _ => Runtime.exn_message exn

    fun expect_failure label expected text =
      (case Exn.result (Syntax.read_term ctxt) text of
         Exn.Res term =>
           error
             ("quotation negative test " ^ quote label ^
               " unexpectedly succeeded: " ^
               Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = plain_message exn in
               if expected = "" orelse
                   String.isSubstring expected message
               then ()
               else
                 error
                   ("quotation negative test " ^ quote label ^
                     " produced the wrong diagnostic:\n" ^ message)
             end)

    val failures =
      [("empty body",
        "urust term: empty expression",
        "\<mu>\<open>\<close>"),
       ("implicit outer literal reference",
        "undeclared literal dependency",
        "\<lambda>x :: nat. \<mu>\<open> x \<close>"),
       ("implicit outer function reference",
        "undeclared function dependency",
        "\<lambda>f :: unit \<Rightarrow> (unit, unit, unit, unit, unit) function_body. \<mu>\<open> f() \<close>"),
       ("implicit outer field reference",
        "undeclared field dependency",
        "\<mu>(value := make_quotation_record 1)\<open> value.missing_field \<close>"),
       ("omitted dependency",
        "undeclared function dependency",
        "\<mu>\<open> quotation_increment(1) \<close>"),
       ("syntactically empty using",
        "",
        "\<mu>[using ]\<open> 1 \<close>"),
       ("empty using cartouche",
        "a `using` entry must not be empty",
        "\<mu>[using \<open>\<close>]\<open> 1 \<close>"),
       ("non-path using entry",
        "must contain exactly one uRust path",
        "\<mu>[using \<open>quotation_increment(1)\<close>]\<open> 1 \<close>"),
       ("duplicate capture",
        "duplicate capture",
        "\<mu>(x := (1 :: nat), x := (2 :: nat))\<open> x \<close>"),
       ("underscore capture",
        "capture name cannot be `_`",
        "\<mu>(_ := (1 :: nat))\<open> 1 \<close>"),
       ("unused capture",
        "unused capture",
        "\<mu>(x := (1 :: nat))\<open> 1 \<close>"),
       ("capture shadowed before use",
        "unused capture",
        "\<mu>(x := (1 :: nat))\<open> let x = 2; x \<close>"),
       ("duplicate dependency",
        "duplicate dependency",
        "\<mu>[using \<open>Quotation::Seven\<close>, \<open>Quotation::Seven\<close>]\<open> Quotation::Seven \<close>"),
       ("unused dependency",
        "unused dependency",
        "\<mu>[using \<open>Quotation::Seven\<close>]\<open> 1 \<close>"),
       ("capture dependency overlap",
        "both a capture and a dependency",
        "\<mu>(quotation_increment := quotation_increment)[using \<open>quotation_increment\<close>]\<open> quotation_increment(1) \<close>"),
       ("lexical dependency collision",
        "collides with a declared dependency",
        "\<mu>[using \<open>quotation_collision\<close>]\<open> let quotation_collision = 1; quotation_collision \<close>"),
       ("registered lexical collision",
        "collides with registered function name resolution",
        "\<mu>\<open> let quotation_increment = 1; quotation_increment \<close>"),
       ("registered literal lexical collision",
        "collides with registered literal name resolution",
        "\<mu>\<open> let quotation_seven = 1; quotation_seven \<close>"),
       ("registered field lexical collision",
        "collides with registered field name resolution",
        "\<mu>\<open> let quotation_field = 1; quotation_field \<close>"),
       ("closure dependency collision",
        "collides with a declared dependency",
        "\<mu>[using \<open>quotation_increment\<close>]\<open> |quotation_increment| quotation_increment \<close>"),
       ("case registered value collision",
        "collides with a declared dependency",
        "\<mu>(value := (7 :: nat))[using \<open>quotation_seven\<close>]\<open> match_case value { quotation_seven \<Rightarrow> quotation_seven } \<close>"),
       ("undeclared switch key",
        "undeclared literal dependency",
        "\<mu>(value := (7 :: nat))\<open> match_switch value { missing_key \<Rightarrow> 1, _ \<Rightarrow> 0 } \<close>"),
       ("duplicate closure formal",
        "duplicate lexical binder",
        "\<mu>\<open> |x, x| x \<close>"),
       ("wildcard closure formal",
        "closure formal must be an identifier",
        "\<mu>\<open> |_| 1 \<close>"),
       ("tuple closure formal is rejected by the grammar",
        "Parse Error",
        "\<mu>\<open> |(x, y)| x \<close>"),
       ("let RHS cannot see its binder",
        "undeclared literal dependency",
        "\<mu>\<open> let x = x; x \<close>"),
       ("if-let binder does not leak into fallback",
        "undeclared literal dependency",
        "\<mu>(value := Quotation_Some 1)[using \<open>Quotation::Some\<close>]\<open> if let Quotation::Some(x) = value { x } else { x } \<close>"),
       ("match binder does not leak into sibling arm",
        "undeclared literal dependency",
        "\<mu>(value := Quotation_Some 1)[using \<open>Quotation::Some\<close>, \<open>Quotation::None\<close>]\<open> match_case value { Quotation::Some(x) \<Rightarrow> x, Quotation::None \<Rightarrow> x } \<close>"),
       ("unequal or-pattern binders",
        "or-pattern alternatives must bind the same names",
        "\<mu>(value := Quotation_Some 1)[using \<open>Quotation::Some\<close>, \<open>Quotation::None\<close>]\<open> match_case value { Quotation::Some(x) | Quotation::None \<Rightarrow> x } \<close>"),
       ("HOL fallback",
        "has no registered function backend",
        "\<mu>[using \<open>Suc\<close>]\<open> Suc(1) \<close>"),
       ("wrong dependency role",
        "has no registered function backend",
        "\<mu>[using \<open>quotation_seven\<close>]\<open> quotation_seven(1) \<close>"),
       ("opaque path fallback",
        "undeclared literal dependency",
        "\<mu>\<open> Missing::Path \<close>"),
       ("constructor metadata fallback",
        "has no registered literal backend",
        "\<mu>(value := Quotation_Unregistered 1)[using \<open>Quotation_Unregistered\<close>]\<open> match_case value { Quotation_Unregistered(x) \<Rightarrow> x } \<close>"),
       ("same-role ambiguity",
        "multiple registered function backends",
        "\<mu>[using \<open>quotation_ambiguous\<close>]\<open> quotation_ambiguous(1) \<close>"),
       ("literal ambiguity",
        "multiple registered literal backends",
        "\<mu>[using \<open>quotation_ambiguous_literal\<close>]\<open> quotation_ambiguous_literal \<close>"),
       ("field ambiguity",
        "multiple registered field backends",
        "\<mu>(value := make_quotation_record 1)[using \<open>quotation_ambiguous_field\<close>]\<open> value.quotation_ambiguous_field \<close>"),
       ("value antiquotation",
        "value antiquotations are not allowed",
        "\<mu>\<open> \<llangle>1 :: nat\<rrangle> \<close>"),
       ("value antiquotation pattern",
        "value antiquotations are not allowed",
        "\<mu>(value := (1 :: nat))\<open> match_case value { \<llangle>1 :: nat\<rrangle> \<Rightarrow> 1, _ \<Rightarrow> 0 } \<close>"),
       ("value antiquotation range endpoint",
        "value antiquotations are not allowed",
        "\<mu>(value := (1 :: nat))\<open> if let \<llangle>0 :: nat\<rrangle>..=2 = value { 1 } else { 0 } \<close>"),
       ("expression antiquotation",
        "expression antiquotations are not allowed",
        "\<mu>\<open> \<epsilon>\<open>Core_Expression.literal (1 :: nat)\<close> \<close>"),
       ("antiquotation callee",
        "antiquotation callees are not allowed",
        "\<mu>\<open> \<epsilon>\<open>quotation_increment\<close>(1) \<close>"),
       ("function literal",
        "HOL function literals are not allowed",
        "\<mu>\<open> \<llangle>\<lambda>x :: nat. x\<rrangle>\<^sub>1(1) \<close>"),
       ("generic arguments",
        "generic arguments are not allowed",
        "\<mu>[using \<open>quotation_increment\<close>]\<open> quotation_increment::<1>(1) \<close>"),
       ("generic method arguments",
        "generic arguments are not allowed",
        "\<mu>(value := (1 :: nat))[using \<open>quotation_method\<close>]\<open> value.quotation_method::<1>() \<close>"),
       ("generic literal path",
        "generic arguments are not allowed",
        "\<mu>[using \<open>quotation_seven::<1>\<close>]\<open> quotation_seven::<1> \<close>"),
       ("primitive log",
        "primitive log operands are embedded HOL",
        "\<mu>\<open> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[]\<rrangle> \<close>"),
       ("undeclared log-data identifier",
        "must be captured or lexical",
        "\<mu>\<open> l\<llangle>missing_log_value\<rrangle> \<close>"),
       ("fuelled while",
        "fuelled loops are not allowed",
        "\<mu>\<open> #[fuel(\<epsilon>\<open>1\<close>)] while (true) { () } \<close>"),
       ("fuelled loop",
        "fuelled loops are not allowed",
        "\<mu>\<open> #[fuel(\<epsilon>\<open>1\<close>)] loop { () } \<close>"),
       ("fuelled while let",
        "fuelled loops are not allowed",
        "\<mu>\<open> #[fuel(\<epsilon>\<open>1\<close>)] while let x = 1 { () } \<close>"),
       ("macro",
        "macros are not allowed",
        "\<mu>\<open> assert!(true) \<close>"),
       ("macro rejection precedes embedded body inspection",
        "macros are not allowed",
        "\<mu>\<open> assert!(\<llangle>True\<rrangle>) \<close>"),
       ("mixed numeral and constructor auto match",
        "mixed numeral and constructor patterns",
        "\<mu>(value := Quotation_Some 1)[using \<open>Quotation::Some\<close>]\<open> match value { 0 \<Rightarrow> 0, Quotation::Some(x) \<Rightarrow> x } \<close>"),
       ("guarded explicit switch",
        "guards are not supported in explicit `match_switch`",
        "\<mu>(value := (1 :: nat))\<open> match_switch value { 1 if true \<Rightarrow> 1, _ \<Rightarrow> 0 } \<close>"),
       ("antiquotation place",
        "expression antiquotations are not allowed",
        "\<mu>\<open> \<epsilon>\<open>undefined\<close> = 1 \<close>")]

    val _ =
      List.app
        (fn (label, expected, text) =>
          expect_failure label expected text)
        failures
  in
    val _ = writeln "Closed quotation negative diagnostics passed"
  end
\<close>

subsection\<open>Conformance gating and residual audit\<close>

ML_val\<open>
  local
    fun plain_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))
        handle Fail _ => Runtime.exn_message exn

    val disabled =
      Config.put urust_term_hook_conformance_check false
        \<^context>
    val enabled =
      Config.put urust_term_hook_conformance_check true
        \<^context>
    val source = "\<mu>\<open> () // legacy consumes its closing delimiter \<close>"
    val _ = ignore (Syntax.read_term disabled source)
    val _ =
      (case Exn.result (Syntax.read_term enabled) source of
         Exn.Res _ =>
           error "quotation conformance gate invoked no legacy failure"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else if String.isSubstring
               "legacy frontend rejected" (plain_message exn)
           then ()
           else
             error
               ("quotation conformance gate produced the wrong diagnostic:\n" ^
                 plain_message exn))

    val typed_source =
      "(\<mu>(captured := (1 :: nat))\
      \ [using \<open>quotation_increment\<close>]\
      \ \<open> quotation_increment(captured) \<close> ::\
      \ (unit, nat, unit, unit, unit, unit) expression)"
    val unchecked_disabled =
      Syntax.parse_term disabled typed_source
    val checked =
      Syntax.check_term disabled unchecked_disabled
    val checked_enabled =
      Syntax.read_term enabled typed_source

    fun forbidden
        (Const (name, _)) =
          name = \<^const_name>\<open>urust_dispatch\<close> orelse
          name = \<^syntax_const>\<open>_type_constraint_\<close> orelse
          String.isSuffix "urust_term_hook_conformance_marker" name
      | forbidden (Free (name, _)) =
          String.isPrefix "_urust_dispatch_payload___" name orelse
          String.isPrefix "_urust_term_hook_position___" name
      | forbidden _ = false

    fun conformance_marker
        (Const (name, _)) =
          String.isSuffix
            "urust_term_hook_conformance_marker" name
      | conformance_marker _ = false

    val _ =
      if Term.exists_subterm conformance_marker
          unchecked_disabled
      then
        error
          "quotation residual audit: disabled parsing created a conformance marker"
      else ()
    val _ =
      if Term.exists_subterm forbidden checked then
        error "quotation residual audit: internal marker survived checking"
      else ()
    val _ =
      if Term.aconv (checked, checked_enabled) then ()
      else
        error
          "quotation residual audit: enabled checking changed the final parser term"
    val _ =
      if null (Term.add_vars checked []) then ()
      else
        error "quotation residual audit: schematic term variable survived"

    val nested_source =
      "(\<mu>(nested :=\
      \   (\<mu>(value := (1 :: nat))\<open> value \<close> ::\
      \     (unit, nat, unit, unit, unit, unit) expression))\
      \ \<open> nested \<close> ::\
      \ (unit,\
      \  (unit, nat, unit, unit, unit, unit) expression,\
      \  unit, unit, unit, unit) expression)"
    val nested_checked =
      Syntax.read_term enabled nested_source
    val _ =
      if Term.exists_subterm forbidden nested_checked then
        error
          "quotation residual audit: nested marker or constraint survived checking"
      else ()
  in
    val _ =
      writeln
        "Quotation conformance gating and residual-term audit passed"
  end
\<close>

subsection\<open>Positioned delayed conformance\<close>

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("quotation delayed conformance: " ^ message)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int
          (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int
          (Position.end_offset_of position)

    fun has_diagnostic_position body position =
      fold collect_markup body []
      |> exists
          (fn (name, properties) =>
            name = Markup.positionN andalso
              has_position properties position)

    fun positioned_source text start =
      Input.source false text
        (Position.range
          (start, Position.symbol_explode text start))

    fun token_position text start needle =
      let
        fun find offset =
          if offset + size needle > size text then
            error
              ("quotation delayed conformance: missing " ^
                quote needle)
          else if
            String.substring (text, offset, size needle) = needle
          then offset
          else find (offset + 1)
        val raw = find 0
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (Position.range
            (token_start,
             Position.symbol_explode needle token_start))
      end

    fun cartouche_position text start =
      let
        val cartouche_text =
          String.extract (text, size "\<mu>", NONE)
        val cartouche_start =
          Position.symbol_explode "\<mu>" start
      in
        Position.range_position
          (Position.range
            (cartouche_start,
             Position.symbol_explode
               cartouche_text cartouche_start))
      end

    fun expect_positioned_failure
        label expected position action =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("quotation delayed conformance: " ^ label ^
              " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body =
                 YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
             in
               assert (label ^ " diagnostic changed")
                 (String.isSubstring expected message);
               assert (label ^ " diagnostic range changed")
                 (has_diagnostic_position body position)
             end)

    fun expect_failure label expected action =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("quotation delayed conformance: " ^ label ^
              " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             assert (label ^ " diagnostic changed")
               (String.isSubstring expected
                 (XML.content_of
                   (YXML.parse_body
                     (Runtime.exn_message exn)))))

    val disabled_ctxt =
      Config.put urust_term_hook_conformance_check
        false \<^context>
    val enabled_ctxt =
      Config.put urust_term_hook_conformance_check
        true \<^context>

    val shared_text = "\<mu>\<open> 1 \<close>"
    val shared_start =
      Position.make0 11 500 0 "" ""
        "quotation-shared-source"
    val shared_source =
      positioned_source shared_text shared_start
    val shared_input = Syntax.implode_input shared_source
    val shared_position =
      cartouche_position shared_text shared_start
    val unchecked_marker =
      Syntax.parse_term enabled_ctxt shared_input
    val checked_enabled =
      Syntax.check_term enabled_ctxt unchecked_marker
    val checked_disabled =
      Syntax.read_term disabled_ctxt shared_input
    val _ =
      assert "enabled checking changed the parser term"
        (Term.aconv (checked_enabled, checked_disabled))

    val (marker_head, marker_arguments) =
      Term.strip_comb unchecked_marker
    val marker_name =
      (case marker_head of
         Const (name, _) => name
       | _ =>
           error
             "quotation delayed conformance: missing marker head")
    val position_payload =
      (case marker_arguments of
         [_, _, payload] => payload
       | _ =>
           error
             "quotation delayed conformance: malformed generated marker")

    fun contains_marker
        (Const (name, _)) = name = marker_name
      | contains_marker (function $ argument) =
          contains_marker function orelse
            contains_marker argument
      | contains_marker (Abs (_, _, body)) =
          contains_marker body
      | contains_marker _ = false

    val _ =
      assert "a conformance marker survived checking"
        (not (contains_marker checked_enabled))

    val alpha_marker =
      Term.list_comb
        (marker_head,
         [Abs ("left", dummyT, Bound 0),
          Abs ("right", dummyT, Bound 0),
          position_payload])
    val alpha_checked =
      Syntax.check_term enabled_ctxt alpha_marker
    val _ =
      assert "alpha-equivalent binders were not accepted"
        (Term.aconv_untyped
          (alpha_checked, Abs ("expected", dummyT, Bound 0)))

    val checked_pair =
      Syntax.check_terms enabled_ctxt
        [unchecked_marker, unchecked_marker]
    val _ =
      assert "simultaneous term checking did not erase every marker"
        (List.all (not o contains_marker) checked_pair)

    val structural_mismatch =
      Term.list_comb
        (marker_head,
         [\<^term>\<open>True\<close>,
          \<^term>\<open>False\<close>,
          position_payload])
    val _ =
      expect_positioned_failure "structural mismatch"
        "different untyped terms" shared_position
        (fn () =>
          Syntax.check_term enabled_ctxt
            structural_mismatch)

    val type_mismatch =
      Term.list_comb
        (marker_head,
         [HOLogic.mk_eq
            (Abs ("x", \<^typ>\<open>nat\<close>,
               \<^term>\<open>True\<close>),
             Abs ("x", \<^typ>\<open>nat\<close>,
               \<^term>\<open>True\<close>)),
          HOLogic.mk_eq
            (Abs ("x", \<^typ>\<open>bool\<close>,
               \<^term>\<open>True\<close>),
             Abs ("x", \<^typ>\<open>bool\<close>,
               \<^term>\<open>True\<close>)),
          position_payload])
    val _ =
      expect_positioned_failure "type mismatch"
        "types do not agree" shared_position
        (fn () =>
          Syntax.check_term enabled_ctxt type_mismatch)

    val malformed_marker =
      marker_head $ \<^term>\<open>True\<close>
    val _ =
      expect_failure "malformed marker"
        "malformed internal marker"
        (fn () =>
          Syntax.check_term enabled_ctxt malformed_marker)

    val malformed_payload =
      Term.list_comb
        (marker_head,
         [\<^term>\<open>True\<close>,
          \<^term>\<open>True\<close>,
          Free ("not-a-position-payload", dummyT)])
    val _ =
      expect_failure "malformed marker payload"
        "malformed internal marker"
        (fn () =>
          Syntax.check_term enabled_ctxt malformed_payload)

    val rejected_text =
      "\<mu>\<open> () // legacy rejects this source \<close>"
    val rejected_start =
      Position.make0 13 700 0 "" ""
        "quotation-legacy-rejection"
    val rejected_source =
      positioned_source rejected_text rejected_start
    val rejected_position =
      cartouche_position rejected_text rejected_start
    val _ =
      expect_positioned_failure "legacy rejection"
        "legacy frontend rejected the source"
        rejected_position
        (fn () =>
          Syntax.read_term enabled_ctxt
            (Syntax.implode_input rejected_source))

    val undeclared_text = "\<mu>\<open> missing_name \<close>"
    val undeclared_start =
      Position.make0 17 900 0 "" ""
        "quotation-undeclared-dependency"
    val undeclared_source =
      positioned_source undeclared_text undeclared_start
    val undeclared_position =
      token_position undeclared_text undeclared_start
        "missing_name"
    val _ =
      expect_positioned_failure "undeclared dependency"
        "undeclared literal dependency"
        undeclared_position
        (fn () =>
          Syntax.read_term disabled_ctxt
            (Syntax.implode_input undeclared_source))

    val escaped_text =
      "\<mu>\<open> \<y>\<i>\<e>\<l>\<d>; escaped_missing \<close>"
    val escaped_start =
      Position.make0 19 1100 0 "" ""
        "quotation-symbol-position"
    val escaped_source =
      positioned_source escaped_text escaped_start
    val escaped_position =
      token_position escaped_text escaped_start
        "escaped_missing"
    val _ =
      expect_positioned_failure
        "Isabelle-symbol-counted dependency"
        "undeclared literal dependency"
        escaped_position
        (fn () =>
          Syntax.read_term disabled_ctxt
            (Syntax.implode_input escaped_source))
  in
    val _ =
      writeln "Quotation positioned diagnostics passed"
  end
\<close>

end
