theory Micro_Rust_Parser_Cycle_3_Audit
  imports Micro_Rust_Parser_Cycle_2_Audit
begin

section\<open> Cycle 3 integration audit \<close>

text\<open>
Cycle 3 keeps executable parser-generated fixtures, controlled-normalization stress cases,
source-position regressions, and deterministic large-pattern construction checks in one
session-ending audit theory.
\<close>

subsection\<open> Canonical source positions \<close>

ML_val\<open>
  local
    val context = \<^context>

    fun assert message condition =
      if condition then ()
      else error ("Cycle 3 source-position audit: " ^ message)

    fun expect_positioned_rejection
        label text start expected expected_position =
      let
        val source =
          Parser_Lex_Util.positioned_content_source
            text start
        val expected_here =
          XML.content_of
            (YXML.parse_body
              (Position.here expected_position))
      in
        (case Exn.result
            (fn () => elab_urust context source) () of
           Exn.Res _ =>
             error (label ^ " unexpectedly parsed")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let
                 val message =
                   XML.content_of
                     (YXML.parse_body (Runtime.exn_message exn))
               in
                 assert
                   (label ^ " changed diagnostic: expected " ^
                    quote expected ^ " in " ^ quote message)
                   (String.isSubstring expected message);
                 assert
                   (label ^ " changed position: expected " ^
                    quote expected_here ^ " in " ^ quote message)
                   (String.isSubstring expected_here message)
               end)
      end

    val operator_text = "1 + 2 ++ 3"
    val operator_start =
      Position.make0 1 1 0 "" "" ""
    val second_operator =
      Position.symbol_explode
        (String.substring (operator_text, 0, 7))
        operator_start
    val _ =
      assert "second operator was not at column 8"
        (Position.line_of second_operator = SOME 1 andalso
         Position.offset_of second_operator = SOME 8)
    val _ =
      expect_positioned_rejection
        "second operator"
        operator_text operator_start
        "Parse Error at line 1, column 8: syntax error found at +"
        second_operator

    val eof_text = "{ ()"
    val eof_start =
      Position.make0 3 12 0 "" "" ""
    val eof_stop =
      Position.symbol_explode eof_text eof_start
    val _ =
      expect_positioned_rejection
        "malformed EOF"
        eof_text eof_start
        "Parse Error at line 3, column 5: syntax error found at end of input"
        eof_stop
  in
    val _ = ()
  end
\<close>

subsection\<open> Pattern precedence and parse-only scaling \<close>

text\<open>
These checks concern syntax construction only. They do not extend the conservative coverage
classification used to lower the currently supported match and while-let forms.
\<close>

ML_val\<open>
  local
    open URust_AST

    val context = \<^context>

    fun assert message condition =
      if condition then ()
      else error ("Cycle 3 pattern grammar audit: " ^ message)

    fun parse text =
      (case Parser_Utils.with_parser_lock
          (fn () =>
            URust_Diagnostics.parse_source context
              (Parser_Lex_Util.text_source text)) of
         SOME expression => expression
       | NONE => error "Cycle 3 pattern grammar audit: empty parse")

    fun pattern_source pattern =
      "match_case \<llangle>undefined\<rrangle> { " ^ pattern ^
      " \<Rightarrow> \<llangle>undefined\<rrangle> }"

    fun parse_pattern pattern =
      (case parse (pattern_source pattern) of
         UE_Match (_, _, [UR_Arm (result, NONE, _)], _) =>
           result
       | _ =>
           error
             ("Cycle 3 pattern grammar audit: unexpected AST for " ^
              quote pattern))

    fun integer text (P_Literal (LP_Integer (actual, _))) =
          actual = text
      | integer _ _ = false

    fun range kind lower upper
        (P_Range (actual_kind, actual_lower, actual_upper, _)) =
          actual_kind = kind andalso
          integer lower actual_lower andalso
          integer upper actual_upper
      | range _ _ _ _ = false

    val _ =
      assert "exclusive range shape changed"
        (range RK_Exclusive "5" "7"
          (parse_pattern "5..7"))
    val _ =
      assert "inclusive range shape changed"
        (range RK_Inclusive "5" "7"
          (parse_pattern "5..=7"))

    val _ =
      (case parse_pattern "whole @ 5..=7" of
         P_Alias ("whole", _, inner, _) =>
           assert "alias did not bind the whole range"
             (range RK_Inclusive "5" "7" inner)
       | _ => error "Cycle 3 pattern grammar audit: range alias shape changed")

    val _ =
      (case parse_pattern "outer @ inner @ 5..7" of
         P_Alias ("outer", _,
           P_Alias ("inner", _, nested, _), _) =>
             assert "nested aliases lost right associativity"
               (range RK_Exclusive "5" "7" nested)
       | _ =>
           error
             "Cycle 3 pattern grammar audit: nested alias shape changed")

    val _ =
      (case parse_pattern "whole @ Some(5..=7)" of
         P_Alias ("whole", _,
           P_Constr ("Some", _, [nested]), _) =>
             assert "constructor alias lost its range argument"
               (range RK_Inclusive "5" "7" nested)
       | _ =>
           error
             "Cycle 3 pattern grammar audit: constructor alias shape changed")

    val _ =
      (case parse_pattern
          "whole @ Head { field: 5..7 }" of
         P_Alias ("whole", _,
           P_Struct ("Head", _,
             [SF_Field ("field", _, nested)]), _) =>
             assert "struct alias lost its range field"
               (range RK_Exclusive "5" "7" nested)
       | _ =>
           error
             "Cycle 3 pattern grammar audit: struct alias shape changed")

    val _ =
      (case parse_pattern
          "left @ 1..2 | right @ 3..=4" of
         P_Or
           ([P_Alias ("left", _, left, _),
             P_Alias ("right", _, right, _)], _) =>
             (assert "left or-pattern range changed"
                (range RK_Exclusive "1" "2" left);
              assert "right or-pattern range changed"
                (range RK_Inclusive "3" "4" right))
       | _ =>
           error
             "Cycle 3 pattern grammar audit: or/alias/range precedence changed")

    val chained_text =
      pattern_source "1..2..3"
    val chained_start =
      Position.make0 7 1 0 "" "" ""

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("Cycle 3 pattern grammar audit: missing " ^
           quote needle)
      else if
        String.substring (text, offset, size needle) =
          needle
      then offset
      else find_from text needle (offset + 1)

    val first_range =
      find_from chained_text ".." 0
    val second_range =
      find_from chained_text ".." (first_range + 2)
    val second_range_position =
      Position.symbol_explode
        (String.substring
          (chained_text, 0, second_range))
        chained_start
    val expected_here =
      XML.content_of
        (YXML.parse_body
          (Position.here second_range_position))
    val _ =
      (case Exn.result
          (fn () =>
            elab_urust context
              (Parser_Lex_Util.positioned_content_source
                chained_text chained_start)) () of
         Exn.Res _ =>
           error
             "Cycle 3 pattern grammar audit: chained range unexpectedly elaborated"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message =
                 XML.content_of
                   (YXML.parse_body
                     (Runtime.exn_message exn))
             in
               assert "chained range missed semantic validation"
                 (String.isSubstring
                   "range patterns are non-associative" message);
               assert "chained range diagnostic moved"
                 (String.isSubstring expected_here message)
             end)

    fun alternative_name index =
      "cycle3_alt_" ^ string_of_int index

    fun alternative_source count =
      pattern_source
        (space_implode " | "
          (map alternative_name (0 upto (count - 1))))

    fun audit_alternatives count source =
      (case parse source of
         UE_Match (_, _,
           [UR_Arm (P_Or (alternatives, _), NONE, _)], _) =>
             (assert
                ("or-pattern length changed at " ^
                 string_of_int count)
                (length alternatives = count);
              assert
                ("or-pattern first alternative changed at " ^
                 string_of_int count)
                (case hd alternatives of
                   P_Ident (name, _) =>
                     name = alternative_name 0
                 | _ => false);
              assert
                ("or-pattern final alternative changed at " ^
                 string_of_int count)
                (case List.last alternatives of
                   P_Ident (name, _) =>
                     name = alternative_name (count - 1)
                 | _ => false))
       | _ =>
           error
             ("Cycle 3 pattern grammar audit: large or-pattern AST changed at " ^
              string_of_int count))

    val small_count = 4096
    val large_count = 16384
    val small_source = alternative_source small_count
    val large_source = alternative_source large_count
    fun small () = audit_alternatives small_count small_source
    fun large () = audit_alternatives large_count large_source

    val _ = small ()
    val _ = large ()
  in
    val _ = writeln "Cycle 3 large or-pattern AST checks passed"
  end
\<close>

subsection\<open> Lazy matcher code generation \<close>

datatype cycle3_single = Cycle3_Single nat
datatype cycle3_bit = Cycle3_Zero | Cycle3_One

definition cycle3_some_seven :: \<open>nat option\<close>
where
  \<open> cycle3_some_seven = Some 7 \<close>

definition cycle3_none :: \<open>nat option\<close>
where
  \<open> cycle3_none = None \<close>

definition cycle3_some_three :: \<open>nat option\<close>
where
  \<open> cycle3_some_three = Some 3 \<close>

definition cycle3_single_nine :: cycle3_single
where
  \<open> cycle3_single_nine = Cycle3_Single 9 \<close>

definition cycle3_nested_bits ::
  \<open>cycle3_bit \<times> (cycle3_bit \<times> tnil)\<close>
where
  \<open>
    cycle3_nested_bits =
      (Cycle3_One, (Cycle3_Zero, TNil))
  \<close>

definition cycle3_some_nineteen :: \<open>nat option\<close>
where
  \<open> cycle3_some_nineteen = Some 19 \<close>

definition cycle3_some_seven_expression ::
  \<open>
    (unit, nat option, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_some_seven_expression = literal cycle3_some_seven \<close>

definition cycle3_none_expression ::
  \<open>
    (unit, nat option, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_none_expression = literal cycle3_none \<close>

definition cycle3_some_three_expression ::
  \<open>
    (unit, nat option, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_some_three_expression = literal cycle3_some_three \<close>

definition cycle3_single_nine_expression ::
  \<open>
    (unit, cycle3_single, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open>
    cycle3_single_nine_expression =
      literal cycle3_single_nine
  \<close>

definition cycle3_nested_bits_expression ::
  \<open>
    (unit, cycle3_bit \<times> (cycle3_bit \<times> tnil),
      nat, unit, unit prompt, unit prompt_output) expression
  \<close>
where
  \<open>
    cycle3_nested_bits_expression =
      literal cycle3_nested_bits
  \<close>

definition cycle3_some_nineteen_expression ::
  \<open>
    (unit, nat option, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open>
    cycle3_some_nineteen_expression =
      literal cycle3_some_nineteen
  \<close>

definition cycle3_false_expression ::
  \<open>
    (unit, bool, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_false_expression = literal False \<close>

urust_expr cycle3_code_constructor
  \<open>
    match \<epsilon>\<open>cycle3_some_seven_expression\<close> {
      Some(value) \<Rightarrow> value,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr cycle3_code_fallthrough
  \<open>
    match \<epsilon>\<open>cycle3_none_expression\<close> {
      Some(value) \<Rightarrow> value,
      None \<Rightarrow> 11
    }
  \<close>

urust_expr cycle3_code_false_guard
  \<open>
    match \<epsilon>\<open>cycle3_some_three_expression\<close> {
      Some(value) if \<epsilon>\<open>cycle3_false_expression\<close> \<Rightarrow> 100,
      Some(value) \<Rightarrow> value,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr cycle3_code_exhaustive
  \<open>
    match \<epsilon>\<open>cycle3_single_nine_expression\<close> {
      Cycle3_Single(value) \<Rightarrow> value
    }
  \<close>

urust_expr cycle3_code_nested_product_or
  \<open>
    match \<epsilon>\<open>cycle3_nested_bits_expression\<close> {
      (Cycle3_Zero | Cycle3_One, Cycle3_One | Cycle3_Zero) \<Rightarrow> 23
    }
  \<close>

urust_expr cycle3_code_lazy_undefined
  \<open>
    match \<epsilon>\<open>cycle3_some_nineteen_expression\<close> {
      Some(value) \<Rightarrow> value
    }
  \<close>

definition cycle3_code_constructor_closed ::
  \<open>
    (unit, nat, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_code_constructor_closed = cycle3_code_constructor \<close>

definition cycle3_code_fallthrough_closed ::
  \<open>
    (unit, nat, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_code_fallthrough_closed = cycle3_code_fallthrough \<close>

definition cycle3_code_false_guard_closed ::
  \<open>
    (unit, nat, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_code_false_guard_closed = cycle3_code_false_guard \<close>

definition cycle3_code_exhaustive_closed ::
  \<open>
    (unit, nat, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open> cycle3_code_exhaustive_closed = cycle3_code_exhaustive \<close>

definition cycle3_code_nested_product_or_closed ::
  \<open>
    (unit, nat, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open>
    cycle3_code_nested_product_or_closed =
      cycle3_code_nested_product_or
  \<close>

definition cycle3_code_lazy_undefined_closed ::
  \<open>
    (unit, nat, nat, unit,
      unit prompt, unit prompt_output) expression
  \<close>
where
  \<open>
    cycle3_code_lazy_undefined_closed =
      cycle3_code_lazy_undefined
  \<close>

lemma cycle3_code_constructor_result:
  \<open>
    (case evaluate cycle3_code_constructor_closed () of
       Success value _ \<Rightarrow> value
     | _ \<Rightarrow> 0) = 7
  \<close>
  by eval

lemma cycle3_code_fallthrough_result:
  \<open>
    (case evaluate cycle3_code_fallthrough_closed () of
       Success value _ \<Rightarrow> value
     | _ \<Rightarrow> 0) = 11
  \<close>
  by eval

lemma cycle3_code_false_guard_result:
  \<open>
    (case evaluate cycle3_code_false_guard_closed () of
       Success value _ \<Rightarrow> value
     | _ \<Rightarrow> 0) = 3
  \<close>
  by eval

lemma cycle3_code_exhaustive_result:
  \<open>
    (case evaluate cycle3_code_exhaustive_closed () of
       Success value _ \<Rightarrow> value
     | _ \<Rightarrow> 0) = 9
  \<close>
  by eval

lemma cycle3_code_nested_product_or_result:
  \<open>
    (case evaluate cycle3_code_nested_product_or_closed () of
       Success value _ \<Rightarrow> value
     | _ \<Rightarrow> 0) = 23
  \<close>
  by eval

lemma cycle3_code_lazy_undefined_result:
  \<open>
    (case evaluate cycle3_code_lazy_undefined_closed () of
       Success value _ \<Rightarrow> value
     | _ \<Rightarrow> 0) = 19
  \<close>
  by eval

value [code]
  \<open>
    case evaluate cycle3_code_constructor_closed () of
      Success value _ \<Rightarrow> value
    | _ \<Rightarrow> 0
  \<close>

value [code]
  \<open>
    case evaluate cycle3_code_fallthrough_closed () of
      Success value _ \<Rightarrow> value
    | _ \<Rightarrow> 0
  \<close>

value [code]
  \<open>
    case evaluate cycle3_code_false_guard_closed () of
      Success value _ \<Rightarrow> value
    | _ \<Rightarrow> 0
  \<close>

value [code]
  \<open>
    case evaluate cycle3_code_exhaustive_closed () of
      Success value _ \<Rightarrow> value
    | _ \<Rightarrow> 0
  \<close>

value [code]
  \<open>
    case evaluate cycle3_code_nested_product_or_closed () of
      Success value _ \<Rightarrow> value
    | _ \<Rightarrow> 0
  \<close>

value [code]
  \<open>
    case evaluate cycle3_code_lazy_undefined_closed () of
      Success value _ \<Rightarrow> value
    | _ \<Rightarrow> 0
  \<close>

subsection\<open> Controlled-normalization growth \<close>

ML_val\<open>
  local
    open Proofterm

    val context = \<^context>
    val expression_type =
      \<^typ>\<open>
        (unit, nat, nat, unit,
          unit, unit) expression
      \<close>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 3 normalization audit: " ^ message)

    fun proof_nodes MinProof = 1
      | proof_nodes (PBound _) = 1
      | proof_nodes (Abst (_, _, proof)) =
          1 + proof_nodes proof
      | proof_nodes (AbsP (_, _, proof)) =
          1 + proof_nodes proof
      | proof_nodes (proof % _) =
          1 + proof_nodes proof
      | proof_nodes (left %% right) =
          1 + proof_nodes left + proof_nodes right
      | proof_nodes (Hyp _) = 1
      | proof_nodes (PAxm _) = 1
      | proof_nodes (PClass _) = 1
      | proof_nodes (Oracle _) = 1
      | proof_nodes (PThm _) = 1

    fun with_recorded_proofs action =
      let
        val previous = !Proofterm.proofs
        val result =
          Exn.capture
            (fn () =>
              (Proofterm.proofs := 2;
               action ())) ()
        val _ = Proofterm.proofs := previous
      in
        Exn.release result
      end

    fun marker_name index =
      "cycle3_source_marker_" ^ string_of_int index

    fun marker index =
      Free (marker_name index, HOLogic.natT)

    fun alternative index =
      let
        val value = Free ("cycle3_match_value", HOLogic.natT)
        val predicate =
          Term.lambda value
            (URust_Elab_Terms.literal
              (HOLogic.mk_eq (value, marker index)))
      in
        URust_Elab_Terms.matcher_test predicate
      end

    fun choices [matcher] = matcher
      | choices (matcher :: matchers) =
          URust_Elab_Terms.matcher_choice
            matcher (choices matchers)
      | choices [] = raise Match

    fun source_term alternatives =
      let
        val subject =
          Free ("cycle3_normalization_subject", HOLogic.natT)
        val payload =
          Free ("cycle3_normalization_payload", HOLogic.natT)
        val success =
          Term.lambda payload
            (URust_Elab_Terms.literal payload)
        val failure =
          URust_Elab_Terms.literal
            (HOLogic.mk_number HOLogic.natT 0)
        val raw =
          URust_Elab_Terms.matcher_run_value
            (choices
              (map alternative (0 upto alternatives - 1)))
            subject success failure
      in
        Syntax.check_term context
          (Type.constraint expression_type raw)
      end

    fun occurrences name term =
      Term.fold_aterms
        (fn Free (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun check_markers alternatives term =
      List.app
        (fn index =>
          audit_assert
            ("source marker " ^ string_of_int index ^
              " does not occur exactly once")
            (occurrences (marker_name index) term = 1))
        (0 upto alternatives - 1)

    fun measure alternatives =
      let
        val source = source_term alternatives
        val target =
          Free ("cycle3_normalized_target", expression_type)
        val goal =
          HOLogic.mk_Trueprop
            (HOLogic.mk_eq (source, target))
        val _ = check_markers alternatives goal
        val equation =
          with_recorded_proofs
            (fn () =>
              URust_Matcher_Normalize.normalize_conversion
                context (Thm.cterm_of context goal))
        val normalized =
          Thm.term_of (Thm.rhs_of equation)
        val _ = check_markers alternatives normalized
      in
        {alternatives = alternatives,
         input = Term.size_of_term goal,
         normalized = Term.size_of_term normalized,
         proof = proof_nodes (Thm.proof_of equation)}
      end

    val measurements =
      map measure [32, 64, 128]

    fun within_three
        ({input = input_a, normalized = normalized_a,
          proof = proof_a, ...},
         {input = input_b, normalized = normalized_b,
          proof = proof_b, ...}) =
      input_b <= 3 * input_a andalso
      normalized_b <= 3 * normalized_a andalso
      proof_b <= 3 * proof_a

    val _ =
      audit_assert "32-to-64 growth exceeded 3x"
        (within_three
          (nth measurements 0, nth measurements 1))
    val _ =
      audit_assert "64-to-128 growth exceeded 3x"
        (within_three
          (nth measurements 1, nth measurements 2))

    fun report
        {alternatives, input, normalized, proof} =
      writeln
        ("Cycle 3 normalization " ^
          string_of_int alternatives ^
          ": input=" ^ string_of_int input ^
          ", normalized=" ^ string_of_int normalized ^
          ", proof=" ^ string_of_int proof)
  in
    val _ = List.app report measurements
  end
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 3 code audit: " ^ message)

    val generated =
      [\<^const_name>\<open>cycle3_code_constructor\<close>,
       \<^const_name>\<open>cycle3_code_fallthrough\<close>,
       \<^const_name>\<open>cycle3_code_false_guard\<close>,
       \<^const_name>\<open>cycle3_code_exhaustive\<close>,
       \<^const_name>\<open>cycle3_code_nested_product_or\<close>,
       \<^const_name>\<open>cycle3_code_lazy_undefined\<close>]

    fun definition_theorem constant =
      Proof_Context.get_thm ctxt
        (Long_Name.base_name constant ^ "_def")

    fun executable_equations constant =
      let
        val certificate = Code.get_cert ctxt [] constant
        val (_, equations) =
          Code.equations_of_cert thy certificate
      in
        map_filter
          (fn (_, (SOME theorem, _)) => SOME theorem
            | _ => NONE)
          (the equations)
      end

    fun check_generated constant =
      let
        val definition = definition_theorem constant
        val equations = executable_equations constant
        val code_equation = the_single equations
        val unoverloaded_definition =
          Axclass.unoverload ctxt definition
      in
        audit_assert
          ("expected one default equation for " ^ quote constant)
          (length equations = 1);
        audit_assert
          ("default equation differs from the definition for " ^
            quote constant ^
            "\ndefinition: " ^
            Thm.string_of_thm ctxt definition ^
            "\ncode:       " ^
            Thm.string_of_thm ctxt code_equation)
          (Thm.equiv_thm thy
            (code_equation, unoverloaded_definition))
      end

    val _ = List.app check_generated generated

  in
    val _ =
      writeln
        "Cycle 3 parser-generated default-code equations passed"
  end
\<close>

end
