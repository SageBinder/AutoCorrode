(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Tests_Hook_Conformance
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Term_Hook
begin

section\<open>Closed explicit-capture quotation\<close>

text\<open>
The quotation corpus is intentionally closed, antiquotation-free, and macro-free. It covers the
public syntax, simultaneous captures, lexical scope, exact registered dependencies, fail-closed
preflight, delayed conformance, and removal of internal markers.
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

context
  fixes x y :: nat
begin

lemma capture_under_outer_lambda:
  "(\<lambda>x. \<mu>(captured := x)\<open> captured \<close>) =
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

subsection\<open>Declared dependency roles\<close>

datatype quotation_option =
    Quotation_Some nat
  | Quotation_None

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

definition quotation_identity_lens ::
    "(quotation_record, quotation_record) lens"
  where
    "quotation_identity_lens \<equiv> id\<^sub>L"

definition quotation_literal :: nat
  where
    "quotation_literal = 7"

micro_rust_notation (call)
  quotation_some_call ("Quotation::Some")
micro_rust_notation (literal)
  quotation_option.Quotation_Some ("Quotation::Some")
micro_rust_notation (literal)
  quotation_option.Quotation_None ("Quotation::None")
micro_rust_notation (literal)
  quotation_option.Quotation_None ("quotation_none")
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

subsection\<open>Expected type and conformance\<close>

lemma expected_result_type:
  "(\<mu>\<open> 0 \<close> ::
      ('s, nat, 'r, 'abort, 'input, 'output) expression) =
   Core_Expression.literal 0"
  by (rule refl)

declare [[urust_term_hook_conformance_check = true]]

lemma closed_conformance:
  "\<mu>\<open> 1 + 2 \<close> = \<lbrakk> 1 + 2 \<rbrakk>"
  by (rule refl)

context
  fixes x :: nat
begin

lemma capture_conformance:
  "\<mu>(captured := x)\<open> captured \<close> =
   \<lbrakk> x \<rbrakk>"
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

declare [[urust_term_hook_conformance_check = false]]

subsection\<open>Markup normalization\<close>

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("quotation markup normalization: " ^ message)

    val source_prefix =
      "\<mu>[using \<open>Quotation::Seven\<close>]"
    val body_text =
      "\<open> let _ = 1; Quotation::Seven \<close>"
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
    val (_, underscore_pos) =
      token_position "_" 0
    val (numeral_offset, numeral_pos) =
      token_position "1" 0
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
      [("implicit outer reference",
        "undeclared literal dependency",
        "\<lambda>x :: nat. \<mu>\<open> x \<close>"),
       ("omitted dependency",
        "undeclared function dependency",
        "\<mu>\<open> quotation_increment(1) \<close>"),
       ("empty using",
        "",
        "\<mu>[using ]\<open> 1 \<close>"),
       ("duplicate capture",
        "duplicate capture",
        "\<mu>(x := (1 :: nat), x := (2 :: nat))\<open> x \<close>"),
       ("underscore capture",
        "capture name cannot be `_`",
        "\<mu>(_ := (1 :: nat))\<open> 1 \<close>"),
       ("unused capture",
        "unused capture",
        "\<mu>(x := (1 :: nat))\<open> 1 \<close>"),
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
       ("case registered value collision",
        "collides with a declared dependency",
        "\<mu>(value := (7 :: nat))[using \<open>quotation_seven\<close>]\<open> match_case value { quotation_seven \<Rightarrow> quotation_seven } \<close>"),
       ("undeclared switch key",
        "undeclared literal dependency",
        "\<mu>(value := (7 :: nat))\<open> match_switch value { missing_key \<Rightarrow> 1, _ \<Rightarrow> 0 } \<close>"),
       ("duplicate closure formal",
        "duplicate lexical binder",
        "\<mu>\<open> |x, x| x \<close>"),
       ("HOL fallback",
        "has no registered function backend",
        "\<mu>[using \<open>Suc\<close>]\<open> Suc(1) \<close>"),
       ("opaque path fallback",
        "undeclared literal dependency",
        "\<mu>\<open> Missing::Path \<close>"),
       ("constructor metadata fallback",
        "has no registered literal backend",
        "\<mu>(value := Quotation_Unregistered 1)[using \<open>Quotation_Unregistered\<close>]\<open> match_case value { Quotation_Unregistered(x) \<Rightarrow> x } \<close>"),
       ("same-role ambiguity",
        "multiple registered function backends",
        "\<mu>[using \<open>quotation_ambiguous\<close>]\<open> quotation_ambiguous(1) \<close>"),
       ("value antiquotation",
        "value antiquotations are not allowed",
        "\<mu>\<open> \<llangle>1 :: nat\<rrangle> \<close>"),
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
       ("primitive log",
        "primitive log operands are embedded HOL",
        "\<mu>\<open> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[]\<rrangle> \<close>"),
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

    val checked =
      Syntax.read_term disabled
        "(\<mu>(captured := (1 :: nat))\<open> captured \<close> ::\
        \ (unit, nat, unit, unit, unit, unit) expression)"
    fun forbidden
        (Const (name, _)) =
          name = \<^const_name>\<open>urust_dispatch\<close> orelse
          name = \<^syntax_const>\<open>_type_constraint_\<close> orelse
          String.isSuffix "urust_term_hook_conformance_marker" name
      | forbidden (Free (name, _)) =
          String.isPrefix "_urust_dispatch_payload___" name orelse
          String.isPrefix "_urust_term_hook_position___" name
      | forbidden _ = false
    val _ =
      if Term.exists_subterm forbidden checked then
        error "quotation residual audit: internal marker survived checking"
      else ()
    val _ =
      if null (Term.add_vars checked []) then ()
      else
        error "quotation residual audit: schematic term variable survived"
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
  in
    val _ =
      writeln "Quotation positioned diagnostics passed"
  end
\<close>

end
