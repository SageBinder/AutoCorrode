theory Parser_Name_Resolution_Tests
  imports Parser_Pattern_Matching_Tests
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open> Antiquotation markup under HOL shadowing \<close>

text\<open>
Antiquotation navigation follows the positioned term that Isabelle parsed. An inner HOL binder keeps
Isabelle's native \<open>bound\<close> entity, while a same-spelled occurrence outside that binder still
targets the enclosing micro-Rust local.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("antiquotation shadowing markup audit: " ^ message)

    val source_text =
      "let x = \<llangle>1 :: nat\<rrangle>; " ^
      "\<llangle>(\<lambda>x :: nat. x) x\<rrangle>"
    val source_start =
      Position.make0 37 300 2400 "" ""
        "antiquotation-shadowing-markup-audit"
    val source =
      Parser_Lex_Util.positioned_content_source source_text source_start

    val captured_reports =
      Synchronized.var "antiquotation_shadowing_markup_audit"
        ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val actual =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt source) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []

    fun find_from needle offset =
      if offset + size needle > size source_text then
        error
          ("antiquotation shadowing markup audit: missing " ^
            quote needle)
      else if
        String.substring (source_text, offset, size needle) = needle
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

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun entity_ids kind property position =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
               Properties.get properties Markup.kindN = SOME kind andalso
               has_position properties position
            then Properties.get properties property
            else NONE)
      |> distinct (op =)

    fun entity_id kind property position =
      (case entity_ids kind property position of
         [id] => id
       | ids =>
           error
             ("antiquotation shadowing markup audit: expected one " ^
               quote property ^ " entity at" ^
               Position.here position ^ ", found [" ^
               commas_quote ids ^ "]"))

    val (outer_offset, outer_definition) =
      token_position "x" 0
    val (hol_binder_offset, hol_binder) =
      token_position "x" (outer_offset + 1)
    val (hol_use_offset, hol_bound_use) =
      token_position "x" (hol_binder_offset + 1)
    val (_, outer_reference) =
      token_position "x" (hol_use_offset + 1)

    val outer_id =
      entity_id "urust_var" Markup.defN outer_definition
    val hol_binder_id =
      entity_id Markup.boundN Markup.defN hol_binder
    val hol_use_id =
      entity_id Markup.boundN Markup.refN hol_bound_use

    val _ =
      audit_assert "native HOL binder navigation changed"
        (hol_binder_id = hol_use_id)
    val _ =
      audit_assert "HOL lambda declaration received a urust_var entity"
        (null (entity_ids "urust_var" Markup.defN hol_binder) andalso
         null (entity_ids "urust_var" Markup.refN hol_binder))
    val _ =
      audit_assert "HOL bound use received a urust_var entity"
        (null (entity_ids "urust_var" Markup.defN hol_bound_use) andalso
         null (entity_ids "urust_var" Markup.refN hol_bound_use))
    val _ =
      audit_assert "outer micro-Rust reference lost navigation"
        (entity_id "urust_var" Markup.refN outer_reference = outer_id)
  in
    val _ =
      writeln
        "Antiquotation HOL-shadowing semantics and markup regressions passed"
  end
\<close>

section\<open> Expression-antiquotation callee audit \<close>

definition antiquotation_call_audit_direct ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open> antiquotation_call_audit_direct \<equiv> lift_fun2 (+) \<close>

definition antiquotation_call_audit_notation ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open> antiquotation_call_audit_notation \<equiv> lift_fun2 (+) \<close>

consts
  antiquotation_call_audit_first :: nat
  antiquotation_call_audit_second :: nat

micro_rust_notation (call) antiquotation_call_audit_notation
  ("antiquotation_call_audit_direct")

text\<open>
These checks pin the deliberately narrow callable-antiquotation boundary. The AST retains the exact
body source and the complete invocation span; lowering parses that source directly, bypasses call
notation and \<open>literal\<close>, preserves argument order, and retains binder navigation inside the
antiquotation.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("expression-antiquotation callee audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "expression-antiquotation callee audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun is_path name (UE_Path path) = render_path path = name
      | is_path _ _ = false

    val opener = "\<epsilon>\<open>"
    val body = "  antiquotation_call_audit_direct\n"
    val ast_text = opener ^ body ^ "\<close>(first, second)"
    val ast_start =
      Position.make0 7 30 300 "" "" "antiquotation-call-ast-audit"
    val body_start = Position.symbol_explode opener ast_start
    val body_stop = Position.symbol_explode (opener ^ body) ast_start
    val call_stop = Position.symbol_explode ast_text ast_start
    val ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          ast_text ast_start)
    val _ =
      (case ast of
         UE_Call
           (UC_Antiq source, [first, second], call_layout) =>
           (audit_assert "callee constructor changed"
              (is_path "first" first andalso is_path "second" second);
            audit_assert "retained body text changed"
              (Input.string_of source = body);
            audit_assert "retained body range start moved"
              (Position.offset_of (#1 (Input.range_of source)) =
                Position.offset_of body_start);
            audit_assert "retained body range end moved"
              (Position.offset_of (#2 (Input.range_of source)) =
                Position.offset_of body_stop);
            audit_assert "call span no longer starts at the antiquotation opener"
              (Position.offset_of (source_span call_layout) =
                Position.offset_of ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (Position.end_offset_of (source_span call_layout) =
                Position.offset_of call_stop);
            audit_assert "expression_position lost the complete call span"
              (Position.offset_of (expression_position ast) =
                 Position.offset_of (source_span call_layout) andalso
               Position.end_offset_of (expression_position ast) =
                 Position.end_offset_of (source_span call_layout)))
       | _ =>
           error "expression-antiquotation callee audit: call AST changed")

    val direct =
      checked
        ("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(" ^
         "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
         "\<llangle>antiquotation_call_audit_second\<rrangle>)")
      |> Term_Position.strip_positions
    val ordinary =
      checked
        ("antiquotation_call_audit_direct(" ^
         "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
         "\<llangle>antiquotation_call_audit_second\<rrangle>)")
      |> Term_Position.strip_positions
    val (direct_head, direct_arguments) = Term.strip_comb direct
    val _ =
      audit_assert "direct call did not use funcall2"
        (case direct_head of
           Const (name, _) => name = \<^const_name>\<open>funcall2\<close>
         | _ => false)
    val _ =
      (case direct_arguments of
         [Const (callee, _), first, second] =>
           let
             fun is_literal expected argument =
               (case Term_Position.strip_positions argument of
                  Const (literal_name, _) $ Const (actual, _) =>
                    literal_name = \<^const_name>\<open>literal\<close> andalso
                    actual = expected
                | _ => false)
           in
             audit_assert "embedded callee was not passed directly"
               (callee =
                 \<^const_name>\<open>antiquotation_call_audit_direct\<close>);
             audit_assert "first argument moved or changed"
               (is_literal
                 \<^const_name>\<open>antiquotation_call_audit_first\<close>
                 first);
             audit_assert "second argument moved or changed"
               (is_literal
                 \<^const_name>\<open>antiquotation_call_audit_second\<close>
                 second)
           end
       | _ =>
           error
             "expression-antiquotation callee audit: funcall2 argument shape changed")
    val _ =
      audit_assert "embedded callee was parsed more than once"
        (count_constant
          \<^const_name>\<open>antiquotation_call_audit_direct\<close>
          direct = 1)
    val _ =
      audit_assert "embedded callee received a literal wrapper"
        (count_constant \<^const_name>\<open>literal\<close> direct = 2)
    val _ =
      audit_assert "embedded callee entered notation dispatch"
        (count_constant
          \<^const_name>\<open>antiquotation_call_audit_notation\<close>
          direct = 0 andalso
         count_constant \<^const_name>\<open>urust_dispatch\<close> direct = 0)
    val _ =
      audit_assert "notation-collision fixture did not dispatch an ordinary call"
        (count_constant
          \<^const_name>\<open>antiquotation_call_audit_notation\<close>
          ordinary = 1)

    fun expect_rejection text expected =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error
             ("expression-antiquotation callee audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (Runtime.exn_message exn)))

    val malformed =
      [("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(, 1)",
        "syntax error"),
       ("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(1,, 2)",
        "syntax error"),
       ("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(1",
        "syntax error found at end of input")]
    val _ =
      List.app
        (fn (text, expected) =>
          (expect_rejection text expected;
           audit_assert "parser state leaked after malformed call"
             (case parse_text "()" of
                UE_Unit _ => true
              | _ => false)))
        malformed

    fun find_from text needle offset =
      if offset + size needle > size text
      then error
        ("expression-antiquotation callee audit: missing " ^ quote needle)
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
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    val markup_text =
      "let h = \<llangle>antiquotation_call_audit_direct\<rrangle>; " ^
      "\<epsilon>\<open>h\<close>(" ^
      "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
      "\<llangle>antiquotation_call_audit_second\<rrangle>)"
    val markup_start =
      Position.make0 11 50 500 "" "" "antiquotation-call-markup-audit"
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source
                      markup_text markup_start))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, tree)) result =
          fold collect_markup tree (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
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
               "expression-antiquotation callee audit: binder entity markup changed")
      end
    val (definition_offset, definition_position) =
      token_position markup_text markup_start "h" 0
    val (_, reference_position) =
      token_position markup_text markup_start "h"
        (definition_offset + size "h")
    val (_, opener_position) =
      token_position markup_text markup_start "\<epsilon>" 0
    val _ =
      audit_assert "antiquotation opener lost literal markup"
        (has_markup Markup.literalN opener_position)
    val _ =
      audit_assert "antiquotation callee binder definition lost bound markup"
        (has_markup Markup.boundN definition_position)
    val _ =
      audit_assert "antiquotation callee binder reference lost bound markup"
        (has_markup Markup.boundN reference_position)
    val _ =
      audit_assert "antiquotation callee binder navigation changed"
        (entity_id Markup.defN definition_position =
          entity_id Markup.refN reference_position)
  in
    val _ =
      writeln
        "Expression-antiquotation callee AST, lowering, recovery, and markup regressions passed"
  end
\<close>

section\<open> Arity-indexed function-literal callee audit \<close>

text\<open>
These checks pin the function-literal boundary directly: exact HOL and
suffix ranges, complete call spans, lift-before-parameter-before-call lowering, argument order,
dispatch/literal bypass, failure recovery, suffix token markup, and captured-binder navigation.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("function-literal callee audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "function-literal callee audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)
      |> Term_Position.strip_positions

    fun same_start actual expected =
      Position.offset_of actual = Position.offset_of expected

    fun same_stop actual expected =
      Position.end_offset_of actual = Position.offset_of expected

    fun is_path name (UE_Path path) = render_path path = name
      | is_path _ _ = false

    val opener = "\<llangle>"
    val body = "  (\<lambda>x. x)\n"
    val closer = "\<rrangle>"
    val suffix14 = "\<^sub>1\<^sub>4"
    val generic = "::<function_literal_parameter_a>"
    val arguments = "(first, second)"
    val ast_text =
      opener ^ body ^ closer ^ suffix14 ^ generic ^ arguments
    val ast_start =
      Position.make0 7 30 300 "" "" "function-literal-ast-audit"
    val body_start = Position.symbol_explode opener ast_start
    val body_stop = Position.symbol_explode (opener ^ body) ast_start
    val suffix_start =
      Position.symbol_explode (opener ^ body ^ closer) ast_start
    val suffix_stop =
      Position.symbol_explode
        (opener ^ body ^ closer ^ suffix14) ast_start
    val generic_start =
      Position.symbol_explode
        (opener ^ body ^ closer ^ suffix14 ^ "::<") ast_start
    val generic_stop =
      Position.symbol_explode
        (opener ^ body ^ closer ^ suffix14 ^
          "::<function_literal_parameter_a") ast_start
    val call_stop = Position.symbol_explode ast_text ast_start
    val ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          ast_text ast_start)
    val _ =
      (case ast of
         UE_Call
           (UC_FunLiteral
              (antiquotation, 14, suffix_pos,
               SOME
                 (Generic_Args
                   ([Generic_Arg (canonical, generic_source)], _))),
            [first, second], call_layout) =>
           let
             val source =
               value_antiquotation_source antiquotation
           in
             audit_assert "runtime argument order changed"
              (is_path "first" first andalso is_path "second" second);
            audit_assert "retained HOL body text changed"
              (Input.string_of source = body);
            audit_assert "retained HOL body range start moved"
              (same_start (#1 (Input.range_of source)) body_start);
            audit_assert "retained HOL body range end moved"
              (Position.offset_of (#2 (Input.range_of source)) =
                Position.offset_of body_stop);
            audit_assert "two-digit suffix range start moved"
              (same_start suffix_pos suffix_start);
            audit_assert "two-digit suffix range end moved"
              (same_stop suffix_pos suffix_stop);
            audit_assert "generic canonical fragment changed"
              (canonical = "function_literal_parameter_a");
            audit_assert "generic source range start moved"
              (same_start (#1 (Input.range_of generic_source)) generic_start);
            audit_assert "generic source range end moved"
              (Position.offset_of (#2 (Input.range_of generic_source)) =
                Position.offset_of generic_stop);
            audit_assert "call span no longer starts at the value opener"
              (same_start (source_span call_layout) ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (same_stop (source_span call_layout) call_stop);
            audit_assert "expression_position lost the complete call span"
              (same_start (expression_position ast) ast_start andalso
               same_stop (expression_position ast) call_stop)
           end
       | _ => error "function-literal callee audit: call AST changed")

    val suffix9_text = "\<llangle>id\<rrangle>\<^sub>9(0)"
    val suffix9_start =
      Position.make0 13 70 700 "" "" "function-literal-suffix9-audit"
    val suffix9_expected_start =
      Position.symbol_explode "\<llangle>id\<rrangle>" suffix9_start
    val suffix9_expected_stop =
      Position.symbol_explode
        "\<llangle>id\<rrangle>\<^sub>9" suffix9_start
    val _ =
      (case
         parse_source
           (Parser_Lex_Util.positioned_content_source
             suffix9_text suffix9_start) of
         UE_Call
           (UC_FunLiteral (_, 9, suffix_pos, NONE), [_], _) =>
           (audit_assert "one-digit suffix range start moved"
              (same_start suffix_pos suffix9_expected_start);
            audit_assert "one-digit suffix range end moved"
              (same_stop suffix_pos suffix9_expected_stop))
       | _ => error "function-literal callee audit: one-digit suffix AST changed")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun constant_name (Const (name, _)) = SOME name
      | constant_name _ = NONE

    fun literal_constant expected argument =
      (case argument of
         Const (literal_name, _) $ Const (actual, _) =>
           literal_name = \<^const_name>\<open>literal\<close> andalso
           actual = expected
       | _ => false)

    val direct =
      checked
        ("\<llangle>function_literal_collision\<rrangle>\<^sub>1(" ^
          "\<llangle>antiquotation_call_audit_first\<rrangle>)")
    val _ =
      (case Term.strip_comb direct of
         (Const (call_name, _), [lifted, runtime_argument]) =>
           (audit_assert "direct function literal did not use funcall1"
              (call_name = \<^const_name>\<open>funcall1\<close>);
            audit_assert "direct runtime argument changed"
              (literal_constant
                \<^const_name>\<open>antiquotation_call_audit_first\<close>
                runtime_argument);
            case Term.strip_comb lifted of
              (Const (lift_name, _), [Const (body_name, _)]) =>
                (audit_assert "direct function literal did not use lift_fun1"
                   (lift_name = \<^const_name>\<open>lift_fun1\<close>);
                 audit_assert "HOL body changed or gained a wrapper"
                   (body_name =
                     \<^const_name>\<open>function_literal_collision\<close>))
            | _ =>
                error
                  "function-literal callee audit: direct lifted term changed")
       | _ => error "function-literal callee audit: direct call term changed")
    val _ =
      audit_assert "HOL body was duplicated"
        (count_constant
          \<^const_name>\<open>function_literal_collision\<close> direct = 1)
    val _ =
      audit_assert "HOL body or lifted function received a literal wrapper"
        (count_constant \<^const_name>\<open>literal\<close> direct = 1)
    val _ =
      audit_assert "HOL body entered notation dispatch"
        (count_constant \<^const_name>\<open>urust_dispatch\<close> direct = 0)

    val parameterized =
      checked
        ("\<llangle>\<lambda>a b c. (a + b + c :: nat)\<rrangle>\<^sub>3" ^
         "::<function_literal_parameter_a>(" ^
         "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
         "\<llangle>antiquotation_call_audit_second\<rrangle>)")
    val _ =
      (case Term.strip_comb parameterized of
         (Const (call_name, _),
          [function, first_argument, second_argument]) =>
           let
             val (lift_head, lift_arguments) =
               Term.strip_comb function
           in
             audit_assert "parameterized function literal did not use funcall2"
               (call_name = \<^const_name>\<open>funcall2\<close>);
             audit_assert "generic parameter was not applied after lift_fun3"
               (constant_name lift_head =
                  SOME \<^const_name>\<open>lift_fun3\<close> andalso
                length lift_arguments = 2 andalso
                constant_name (List.last lift_arguments) =
                  SOME
                    \<^const_name>\<open>function_literal_parameter_a\<close>);
             audit_assert "parameterized runtime argument order changed"
               (literal_constant
                  \<^const_name>\<open>antiquotation_call_audit_first\<close>
                  first_argument andalso
                literal_constant
                  \<^const_name>\<open>antiquotation_call_audit_second\<close>
                  second_argument)
           end
       | _ =>
           error
             "function-literal callee audit: parameterized call term changed")

    fun expect_rejection text expected =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error
             ("function-literal callee audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (Runtime.exn_message exn)))

    val malformed =
      [("\<llangle>id\<rrangle>\<^sub>0()", "unexpected input"),
       ("\<llangle>id\<rrangle>\<^sub>1(,0)", "syntax error"),
       ("\<llangle>id\<rrangle>\<^sub>1::<-1>()", "unexpected input"),
       ("\<llangle>id\<rrangle>\<^sub>1::<1(0)", "unterminated turbofish"),
       ("\<llangle>\<lambda>x. x\<rrangle>\<^sub>1()",
        "Type unification failed")]
    val _ =
      List.app
        (fn (text, expected) =>
          (expect_rejection text expected;
           audit_assert "parser state leaked after failed function literal"
             (case parse "()" of
                UE_Unit _ => true
              | _ => false)))
        malformed

    fun find_from text needle offset =
      if offset + size needle > size text
      then error
        ("function-literal callee audit: missing " ^ quote needle)
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
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    val markup_text =
      "let captured = \<llangle>1 :: nat\<rrangle>; " ^
      "\<llangle>\<lambda>x. x + captured\<rrangle>\<^sub>1(0)"
    val markup_start =
      Position.make0 11 50 500 "" "" "function-literal-markup-audit"
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source
                      markup_text markup_start))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, tree)) result =
          fold collect_markup tree (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
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
               "function-literal callee audit: binder entity markup changed")
      end
    val (definition_offset, definition_position) =
      token_position markup_text markup_start "captured" 0
    val (_, reference_position) =
      token_position markup_text markup_start "captured"
        (definition_offset + size "captured")
    val (_, suffix_position) =
      token_position markup_text markup_start "\<^sub>1" 0
    val _ =
      audit_assert "function-literal suffix lost delimiter markup"
        (has_markup Markup.delimiterN suffix_position)
    val _ =
      audit_assert "function-literal suffix lost typing markup"
        (has_markup Markup.typingN suffix_position)
    val _ =
      audit_assert "captured binder definition lost bound markup"
        (has_markup Markup.boundN definition_position)
    val _ =
      audit_assert "function-literal body reference lost bound markup"
        (has_markup Markup.boundN reference_position)
    val _ =
      audit_assert "function-literal binder navigation changed"
        (entity_id Markup.defN definition_position =
          entity_id Markup.refN reference_position)
  in
    val _ =
      writeln
        "Function-literal AST, lowering, recovery, and markup regressions passed"
  end
\<close>

section\<open> Method resolution boundary audit \<close>

definition method_audit_pure :: \<open>nat option \<Rightarrow> bool\<close>
  where \<open> method_audit_pure \<equiv> Option.is_none \<close>

definition method_audit_registered ::
  \<open>nat option \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where \<open> method_audit_registered \<equiv> lift_fun1 Option.is_none \<close>

definition method_audit_shallow ::
  \<open>nat option \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where \<open> method_audit_shallow \<equiv> lift_fun1 Option.is_none \<close>

micro_rust_notation (literal) method_audit_pure ("is_none")
micro_rust_notation (call) method_audit_registered ("method_registered")

text\<open>
Method parsing retains the receiver, method identifier, and call span before resolution. Method
resolution rejects an unresolved call spelling at the exact method range; a literal-only registration
does not alter that call-role boundary. The general positioned call-head constraint also rejects a
known pure HOL constant whose terminal result cannot be a shallow \<open>function_body\<close>. Registered,
ordinary shallow-HOL, direct-call, and unit expressions then elaborate normally.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("method resolution boundary audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("method resolution boundary audit: missing " ^ quote needle)
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
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "method resolution boundary audit: empty parse")

    val unregistered_ctxt =
      ctxt
      |> Context.Proof
      |> Micro_Rust_Names.Data.map
          (Symtab.delete_safe
            (Micro_Rust_Names.mk_key
              Micro_Rust_Names.NFunction "is_none"))
      |> Context.proof_of
    val _ =
      audit_assert "literal-only fixture lost its literal registration"
        (not (null
          (Micro_Rust_Names.lookups unregistered_ctxt
            Micro_Rust_Names.NLiteral "is_none")))
    val _ =
      audit_assert "isolated fixture retained a call registration"
        (null
          (Micro_Rust_Names.lookups unregistered_ctxt
            Micro_Rust_Names.NFunction "is_none"))

    val text =
      "assert!(!o.is_none())"
    val start =
      Position.make0 17 200 0 "" "" "method-resolution-boundary-audit"
    val source =
      Parser_Lex_Util.positioned_content_source text start
    val (call_offset, expected_call) =
      token_position text start "o.is_none()" 0
    val (_, expected_method) =
      token_position text start "is_none"
        (call_offset + size "o.")
    val ast = parse source
    val method_position =
      (case ast of
         UE_Macro
           (macro_path, MP_Arguments
             [UE_Unary
               (U_Not,
                UE_Call
                  (UC_Method
                    (UE_Path receiver_path,
                     Path_Segment
                       ("is_none", method_pos, NONE)),
                   [], call_layout),
                _)],
            _) =>
           (audit_assert "assert macro wrapper changed"
              (render_path macro_path = "assert");
            audit_assert "method receiver changed"
              (render_path receiver_path = "o");
            audit_assert "method identifier range moved"
              (same_range method_pos expected_method);
            audit_assert "method call span moved"
              (same_range
                (source_span call_layout) expected_call);
            method_pos)
       | _ => error "method resolution boundary audit: method AST changed")

    val captured_reports =
      Synchronized.var "method_resolution_boundary_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration elaboration_ctxt elaboration_source =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Exn.result
                  (fn () =>
                    Parser_Test_Elaboration.expression
                      elaboration_ctxt elaboration_source) ()) ())
          ())

    val unregistered_result =
      capture_elaboration unregistered_ctxt source
    val diagnostic_markup =
      (case unregistered_result of
         Exn.Res term =>
           error
             ("method resolution boundary audit: unresolved method unexpectedly " ^
              "elaborated to " ^ Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
             in
               audit_assert "unresolved method diagnostic changed"
                 (String.isSubstring "Type unification failed" message);
               body
             end)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val diagnostic_markup =
      fold collect_markup diagnostic_markup []
    val semantic_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_diagnostic_position_in markup position =
      exists (fn (_, properties) => has_position properties position)
        markup
    fun has_markup_in markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup
    fun has_entity_in markup kind identity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            Properties.get properties Markup.nameN = SOME identity andalso
            has_position properties position)
        markup
    fun urust_entity_id_in markup property position =
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
               ("method resolution boundary audit: receiver entity markup changed" ^
                 Position.here position))
      end

    val _ =
      audit_assert "method-resolution diagnostic lost the identifier range"
        (has_diagnostic_position_in diagnostic_markup method_position)
    val _ =
      audit_assert "unregistered method lost ordinary free-name styling"
        (has_markup_in semantic_markup Markup.freeN method_position)
    val _ =
      audit_assert "unregistered method acquired constant identity markup"
        (not
          (has_entity_in semantic_markup Markup.constantN
            \<^const_name>\<open>Option.is_none\<close> method_position))
    val _ =
      audit_assert "unregistered method acquired constant styling"
        (not (has_markup_in semantic_markup Markup.constN method_position))
    val _ =
      audit_assert "unregistered fallback lost typing markup"
        (has_markup_in semantic_markup Markup.typingN method_position)
    val _ =
      audit_assert "literal-only registration leaked call-notation markup"
        (not
          (has_entity_in semantic_markup
            Micro_Rust_Names.notationN "is_none" method_position))
    val _ =
      audit_assert "literal-only registration leaked registered-call styling"
        (not
          (has_markup_in semantic_markup Markup.keyword3N method_position))

    val pure_text =
      "let o = \<llangle>None :: nat option\<rrangle>; " ^
      "o.method_audit_pure()"
    val pure_start =
      Position.make0 19 250 0 "" "" "method-pure-hol-boundary-audit"
    val pure_source =
      Parser_Lex_Util.positioned_content_source pure_text pure_start
    val (_, pure_method_position) =
      token_position pure_text pure_start "method_audit_pure" 0
    val pure_result =
      capture_elaboration ctxt pure_source
    val pure_diagnostic_markup =
      (case pure_result of
         Exn.Res term =>
           error
             ("method resolution boundary audit: known pure HOL method " ^
              "unexpectedly elaborated to " ^ Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
             in
               audit_assert "known pure HOL method diagnostic changed"
                 (String.isSubstring
                   "whose result is not a shallow function_body" message);
               body
             end)
      |> (fn body => fold collect_markup body [])
    val pure_semantic_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    val _ =
      audit_assert "pure HOL diagnostic lost the method identifier range"
        (has_diagnostic_position_in
          pure_diagnostic_markup pure_method_position)
    val _ =
      audit_assert "pure HOL method lost constant identity markup"
        (has_entity_in pure_semantic_markup Markup.constantN
          \<^const_name>\<open>method_audit_pure\<close> pure_method_position)
    val _ =
      audit_assert "pure HOL method lost constant styling"
        (has_markup_in pure_semantic_markup
          Markup.constN pure_method_position)
    val _ =
      audit_assert "pure HOL method lost typing markup"
        (has_markup_in pure_semantic_markup
          Markup.typingN pure_method_position)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val registered_text =
      "let o = \<llangle>None :: nat option\<rrangle>; " ^
      "assert!(!o.method_registered())"
    val registered_start =
      Position.make0 23 300 0 "" "" "method-registered-markup-audit"
    val registered_source =
      Parser_Lex_Util.positioned_content_source
        registered_text registered_start
    val (_, registered_method_position) =
      token_position registered_text registered_start
        "method_registered" 0
    val (_, registered_receiver_definition) =
      token_position registered_text registered_start "o" 0
    val (registered_call_offset, _) =
      token_position registered_text registered_start
        "o.method_registered()" 0
    val (_, registered_receiver_reference) =
      token_position registered_text registered_start
        "o" registered_call_offset
    val registered =
      (case capture_elaboration ctxt registered_source of
         Exn.Res term => term
       | Exn.Exn exn => Exn.reraise exn)
    val _ =
      audit_assert "registered lifted backend was not selected exactly once"
        (count_constant
          \<^const_name>\<open>method_audit_registered\<close> registered = 1)
    val _ =
      audit_assert "registered method duplicated or dropped its receiver"
        (count_constant \<^const_name>\<open>Option.None\<close> registered = 1)
    val semantic_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    val _ =
      audit_assert "registered method lost notation entity markup"
        (has_entity_in semantic_markup Micro_Rust_Names.notationN
          "method_registered" registered_method_position)
    val _ =
      audit_assert "registered method lost registered-call styling"
        (has_markup_in semantic_markup
          Markup.keyword3N registered_method_position)
    val _ =
      audit_assert "registered method lost typing markup"
        (has_markup_in semantic_markup
          Markup.typingN registered_method_position)
    val _ =
      audit_assert "receiver definition/reference navigation changed"
        (urust_entity_id_in semantic_markup
            Markup.defN registered_receiver_definition =
          urust_entity_id_in semantic_markup
            Markup.refN registered_receiver_reference)

    val ordinary =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          ("let o = \<llangle>None :: nat option\<rrangle>; " ^
           "o.method_audit_shallow()"))
    val _ =
      audit_assert "ordinary shallow HOL fallback was not selected once"
        (count_constant \<^const_name>\<open>method_audit_shallow\<close> ordinary = 1)
    val _ =
      audit_assert "ordinary shallow method duplicated or dropped its receiver"
        (count_constant \<^const_name>\<open>Option.None\<close> ordinary = 1)

    val direct_registered =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          ("let o = \<llangle>None :: nat option\<rrangle>; " ^
           "method_registered(o)"))
    val _ =
      audit_assert "direct registered call selected a different backend"
        (count_constant
          \<^const_name>\<open>method_audit_registered\<close>
          direct_registered = 1)
    val _ =
      audit_assert "direct registered call duplicated or dropped its argument"
        (count_constant \<^const_name>\<open>Option.None\<close>
          direct_registered = 1)

    val _ =
      (case Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source "()") of
         Const (\<^const_name>\<open>literal\<close>, _) $
             Const (\<^const_name>\<open>Product_Type.Unity\<close>, _) => ()
       | term =>
           error
             ("method resolution boundary audit: elaboration recovery failed: " ^
               Syntax.string_of_term ctxt term))
  in
    val _ =
      writeln
        "Method AST, exact diagnostic, semantic markup, resolution, and recovery regressions passed"
  end
\<close>



section\<open> Registered constructor qualifier markup audit \<close>

datatype constructor_qualifier_fixture =
    ConstructorQualifierVariant
  | ConstructorQualifierOther

micro_rust_notation (literal)
  constructor_qualifier_fixture.ConstructorQualifierVariant
  ("Type::Variant")
micro_rust_notation (literal)
  constructor_qualifier_fixture.ConstructorQualifierVariant
  ("Module::Type::Variant")

datatype constructor_qualifier_left =
  ConstructorQualifierLeft

datatype constructor_qualifier_right =
  ConstructorQualifierRight

micro_rust_notation (literal)
  constructor_qualifier_left.ConstructorQualifierLeft
  ("Families::Variant")
micro_rust_notation (literal)
  constructor_qualifier_right.ConstructorQualifierRight
  ("Families::Variant")

definition constructor_qualifier_value :: nat
  where \<open> constructor_qualifier_value = 17 \<close>

micro_rust_notation (literal)
  constructor_qualifier_value
  ("Module::Value::Item")

definition constructor_qualifier_call ::
    \<open>(unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      constructor_qualifier_call =
        FunctionBody (literal 23)
    \<close>

micro_rust_notation (call)
  constructor_qualifier_call
  ("Module::Call::invoke")

definition qualifier_struct_call ::
    \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      qualifier_struct_call =
        lift_fun1 (\<lambda>value. value)
    \<close>

micro_rust_notation (call)
  qualifier_struct_call
  ("StructModule::Builder::new")

definition qualifier_generic_call ::
    \<open>nat \<Rightarrow> nat \<Rightarrow>
      (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      qualifier_generic_call parameter =
        lift_fun1 (\<lambda>argument. parameter + argument)
    \<close>

micro_rust_notation (call)
  qualifier_generic_call
  ("GenericBase::invoke")

micro_rust_notation (call)
  constructor_qualifier_call
  ("GenericExact::<Token>::invoke")

definition qualifier_macro_call ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      qualifier_macro_call =
        lift_fun1 (\<lambda>value. value)
    \<close>

micro_rust_notation (call)
  qualifier_macro_call
  ("MacroModule::invoke!")
micro_rust_notation (call)
  qualifier_macro_call
  ("MacroGeneric::<Token>::invoke!")
micro_rust_notation (call)
  \<open>lift_fun1 (\<lambda>value :: bool. value)\<close>
  ("MacroModule::anonymous!")

definition qualifier_multi_nat :: nat
  where \<open> qualifier_multi_nat = 29 \<close>

definition qualifier_multi_bool :: bool
  where \<open> qualifier_multi_bool = True \<close>

micro_rust_notation (literal)
  qualifier_multi_nat
  ("Multi::Registered::Value")
micro_rust_notation (literal)
  qualifier_multi_bool
  ("Multi::Registered::Value")

micro_rust_notation (literal)
  qualifier_multi_nat
  ("Duplicate::Registered::Value")
micro_rust_notation (literal)
  qualifier_multi_nat
  ("Duplicate::Registered::Value")

micro_rust_notation (call)
  constructor_qualifier_call
  ("Wrong::Role::Item")

micro_rust_notation (literal)
  constructor_qualifier_left.ConstructorQualifierLeft
  ("Module::Families::Variant")
micro_rust_notation (literal)
  constructor_qualifier_right.ConstructorQualifierRight
  ("Module::Families::Variant")

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("registered constructor qualifier markup audit: " ^ message)

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
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_markup label start text declared_type =
      let
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val captured =
          Synchronized.var
            ("constructor_qualifier_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    ignore
                      (URust_Command.elaborate ctxt
                        {kind = URust_Command.Expression,
                         source = source,
                         arguments = [],
                         arguments_pos = #2 (Input.range_of source),
                         declared_type =
                           Option.map
                             (fn typ => (typ, Position.none))
                             declared_type})) ())
              ())
      in
        fold collect_markup
          (maps YXML.parse_body (Synchronized.value captured)) []
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun count_entity kind identity position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    fun count_entity_kind kind position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              has_position properties position)
          markup)

    fun type_name typ = fst (dest_Type typ)
    fun constant_name term =
      (case Term.head_of term of
         Const (name, _) => name
       | _ => error "expected constant")

    val fixture_type_name =
      type_name \<^typ>\<open>constructor_qualifier_fixture\<close>
    val fixture_constructor_name =
      constant_name \<^term>\<open>ConstructorQualifierVariant\<close>
    val left_type_name =
      type_name \<^typ>\<open>constructor_qualifier_left\<close>
    val right_type_name =
      type_name \<^typ>\<open>constructor_qualifier_right\<close>
    val left_constructor_name =
      constant_name \<^term>\<open>ConstructorQualifierLeft\<close>
    val right_constructor_name =
      constant_name \<^term>\<open>ConstructorQualifierRight\<close>
    val value_name =
      \<^const_name>\<open>constructor_qualifier_value\<close>
    val call_name =
      \<^const_name>\<open>constructor_qualifier_call\<close>

    fun assert_constructor_qualifier
        label notation expected_type expected_notations position markup =
      (audit_assert (label ^ " retained free markup")
         (count_markup Markup.freeN position markup = 0);
       audit_assert (label ^ " lost datatype navigation")
         (count_entity Markup.type_nameN expected_type position markup = 1);
       audit_assert (label ^ " lost constructor keyword3 styling")
         (count_markup Markup.keyword3N position markup = 1);
       audit_assert (label ^ " retained obsolete tconst styling")
         (count_markup Markup.tconstN position markup = 0);
       audit_assert (label ^ " acquired neutral typing markup")
         (count_markup Markup.typingN position markup = 0);
       audit_assert (label ^ " notation navigation count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = expected_notations);
       audit_assert (label ^ " acquired backend constant identity")
         (count_entity_kind Markup.constantN position markup = 0))

    fun assert_neutral_qualifier
        label notation expected_entities position markup =
      (audit_assert (label ^ " retained free markup")
         (count_markup Markup.freeN position markup = 0);
       audit_assert (label ^ " notation entity count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = expected_entities);
       audit_assert (label ^ " typing tooltip count changed")
         (count_markup Markup.typingN position markup = 1);
       audit_assert (label ^ " acquired keyword styling")
         (count_markup Markup.keyword3N position markup = 0);
       audit_assert (label ^ " acquired obsolete tconst styling")
         (count_markup Markup.tconstN position markup = 0);
       audit_assert (label ^ " acquired datatype identity")
         (count_entity_kind Markup.type_nameN position markup = 0);
       audit_assert (label ^ " acquired backend constant identity")
         (count_entity_kind Markup.constantN position markup = 0))

    fun assert_terminal label notation constructor position markup =
      (audit_assert (label ^ " notation entity count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = 1);
       audit_assert (label ^ " constructor entity count changed")
         (count_entity Markup.constantN constructor position markup = 1);
       audit_assert (label ^ " keyword3 styling count changed")
         (count_markup Markup.keyword3N position markup = 1);
       audit_assert (label ^ " acquired terminal free markup")
         (count_markup Markup.freeN position markup = 0))

    val direct_text =
      "match_case Type::Variant { " ^
      "Type::Variant \<Rightarrow> (), _ \<Rightarrow> () }"
    val direct_start =
      Position.make0 71 1400 0 "" ""
        "constructor-qualifier-direct-audit"
    val direct_markup =
      capture_markup "direct" direct_start direct_text NONE
    val (direct_value_raw, _) =
      token_position direct_text direct_start "Type::Variant" 0
    val (_, direct_value_qualifier) =
      token_position direct_text direct_start "Type" direct_value_raw
    val (_, direct_value_terminal) =
      token_position direct_text direct_start "Variant"
        (direct_value_raw + size "Type::")
    val (direct_pattern_raw, _) =
      token_position direct_text direct_start "Type::Variant"
        (direct_value_raw + size "Type::Variant")
    val (_, direct_pattern_qualifier) =
      token_position direct_text direct_start "Type" direct_pattern_raw
    val (_, direct_pattern_terminal) =
      token_position direct_text direct_start "Variant"
        (direct_pattern_raw + size "Type::")
    val _ =
      assert_constructor_qualifier "value qualifier"
        "Type::Variant" fixture_type_name 1
        direct_value_qualifier direct_markup
    val _ =
      assert_constructor_qualifier "pattern qualifier"
        "Type::Variant" fixture_type_name 1
        direct_pattern_qualifier direct_markup
    val _ =
      assert_terminal "value terminal" "Type::Variant"
        fixture_constructor_name direct_value_terminal direct_markup
    val _ =
      assert_terminal "pattern terminal" "Type::Variant"
        fixture_constructor_name direct_pattern_terminal direct_markup

    val module_text =
      "match_case Module::Type::Variant { " ^
      "Module::Type::Variant \<Rightarrow> (), _ \<Rightarrow> () }"
    val module_start =
      Position.make0 79 1800 0 "" ""
        "constructor-qualifier-module-audit"
    val module_markup =
      capture_markup "module" module_start module_text NONE
    val (module_value_raw, _) =
      token_position module_text module_start
        "Module::Type::Variant" 0
    val (_, module_value_outer) =
      token_position module_text module_start "Module" module_value_raw
    val (_, module_value_type) =
      token_position module_text module_start "Type"
        (module_value_raw + size "Module::")
    val (module_pattern_raw, _) =
      token_position module_text module_start
        "Module::Type::Variant"
        (module_value_raw + size "Module::Type::Variant")
    val (_, module_pattern_outer) =
      token_position module_text module_start "Module"
        module_pattern_raw
    val (_, module_pattern_type) =
      token_position module_text module_start "Type"
        (module_pattern_raw + size "Module::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral_qualifier label
            "Module::Type::Variant" 1
            position module_markup)
        [("value outer qualifier", module_value_outer),
         ("pattern outer qualifier", module_pattern_outer)]
    val _ =
      assert_constructor_qualifier "value nearest qualifier"
        "Module::Type::Variant" fixture_type_name 1
        module_value_type module_markup
    val _ =
      assert_constructor_qualifier "pattern nearest qualifier"
        "Module::Type::Variant" fixture_type_name 1
        module_pattern_type module_markup

    val value_text = "Module::Value::Item"
    val value_start =
      Position.make0 87 2200 0 "" ""
        "constructor-qualifier-value-audit"
    val value_markup =
      capture_markup "value" value_start value_text NONE
    val (value_raw, _) =
      token_position value_text value_start value_text 0
    val (_, value_outer) =
      token_position value_text value_start "Module" value_raw
    val (_, value_nearest) =
      token_position value_text value_start "Value"
        (value_raw + size "Module::")
    val (_, value_terminal) =
      token_position value_text value_start "Item"
        (value_raw + size "Module::Value::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral_qualifier label
            "Module::Value::Item" 1
            position value_markup)
        [("registered value outer qualifier", value_outer),
         ("registered value nearest qualifier", value_nearest)]
    val _ =
      assert_terminal "registered value terminal"
        "Module::Value::Item" value_name value_terminal value_markup

    val call_text = "Module::Call::invoke()"
    val call_start =
      Position.make0 95 2600 0 "" ""
        "constructor-qualifier-call-audit"
    val call_markup =
      capture_markup "call" call_start call_text NONE
    val (call_raw, _) =
      token_position call_text call_start call_text 0
    val (_, call_outer) =
      token_position call_text call_start "Module" call_raw
    val (_, call_nearest) =
      token_position call_text call_start "Call"
        (call_raw + size "Module::")
    val (_, call_terminal) =
      token_position call_text call_start "invoke"
        (call_raw + size "Module::Call::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral_qualifier label
            "Module::Call::invoke" 1
            position call_markup)
        [("registered call outer qualifier", call_outer),
         ("registered call nearest qualifier", call_nearest)]
    val _ =
      assert_terminal "registered call terminal"
        "Module::Call::invoke" call_name call_terminal call_markup

    val families_text = "Families::Variant"
    val families_start =
      Position.make0 103 3000 0 "" ""
        "constructor-qualifier-families-audit"
    val families_markup =
      capture_markup "families" families_start families_text
        (SOME
          "(unit, constructor_qualifier_left, unit, unit, unit, unit) expression")
    val (families_raw, _) =
      token_position families_text families_start families_text 0
    val (_, families_qualifier) =
      token_position families_text families_start "Families"
        families_raw
    val (_, families_terminal) =
      token_position families_text families_start "Variant"
        (families_raw + size "Families::")
    val _ =
      audit_assert "multi-backend qualifier retained free markup"
        (count_markup Markup.freeN families_qualifier
          families_markup = 0)
    val _ =
      audit_assert "left datatype family navigation count changed"
        (count_entity Markup.type_nameN left_type_name
          families_qualifier families_markup = 1)
    val _ =
      audit_assert "right datatype family navigation count changed"
        (count_entity Markup.type_nameN right_type_name
          families_qualifier families_markup = 1)
    val _ =
      audit_assert "multi-backend constructor styling did not cover both families"
        (count_markup Markup.keyword3N families_qualifier
          families_markup = 2)
    val _ =
      audit_assert "multi-backend qualifier retained obsolete tconst styling"
        (count_markup Markup.tconstN families_qualifier
          families_markup = 0)
    val _ =
      audit_assert "multi-backend qualifier notation count changed"
        (count_entity Micro_Rust_Names.notationN "Families::Variant"
          families_qualifier families_markup = 2)
    val _ =
      audit_assert "multi-backend notation entity count changed"
        (count_entity Micro_Rust_Names.notationN "Families::Variant"
          families_terminal families_markup = 2)
    val _ =
      audit_assert "multi-backend keyword3 count changed"
        (count_markup Markup.keyword3N families_terminal
          families_markup = 2)
    val _ =
      audit_assert "left constructor entity count changed"
        (count_entity Markup.constantN left_constructor_name
          families_terminal families_markup = 1)
    val _ =
      audit_assert "right constructor entity count changed"
        (count_entity Markup.constantN right_constructor_name
          families_terminal families_markup = 1)
  in
    val _ =
      writeln
        "Registered constructor qualifier datatype, module, value, call, and all-backend markup regressions passed"
  end
\<close>


section\<open> Neutral registered path qualifier markup audit \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>
    val color_ctxt =
      Proof_Context.init_global \<^theory>\<open>Parser_Expression_Tests\<close>

    fun audit_assert message condition =
      if condition then ()
      else error ("neutral registered path qualifier markup audit: " ^ message)

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
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture active_ctxt serial label text declared_type =
      let
        val start =
          Position.make0 (180 + serial) (40000 + serial * 500) 0 "" ""
            ("neutral-registered-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val captured =
          Synchronized.var
            ("neutral_registered_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        URust_Command.elaborate active_ctxt
                          {kind = URust_Command.Expression,
                           source = source,
                           arguments = [],
                           arguments_pos = #2 (Input.range_of source),
                           declared_type =
                             Option.map
                               (fn typ => (typ, Position.none))
                               declared_type}) ())
                  ())
              ())
        val trees =
          maps YXML.parse_body (Synchronized.value captured)
      in
        (start, result, trees, fold collect_markup trees [])
      end

    fun require_success label (Exn.Res term) = term
      | require_success label (Exn.Exn exn) =
          if Exn.is_interrupt exn then Exn.reraise exn
          else
            error
              ("neutral registered path qualifier markup audit: " ^
                label ^ " failed: " ^ Runtime.exn_message exn)

    fun require_failure label (Exn.Exn exn) =
          if Exn.is_interrupt exn then Exn.reraise exn else ()
      | require_failure label (Exn.Res term) =
          error
            ("neutral registered path qualifier markup audit: " ^
              label ^ " unexpectedly elaborated to " ^
              Syntax.string_of_term ctxt term)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun count_entity_kind kind position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              has_position properties position)
          markup)

    fun entity_refs kind notation position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN = SOME kind andalso
                Properties.get properties Markup.nameN = SOME notation andalso
                has_position properties position
            then Properties.get properties Markup.refN
            else NONE)
      |> sort_strings

    fun registration_refs active_ctxt kind notation =
      Micro_Rust_Names.lookups active_ctxt kind notation
      |> map
          (fn ({serial, ...} : Micro_Rust_Names.entry) =>
            Value.print_int serial)
      |> sort_strings

    fun typing_texts position trees =
      let
        fun collect (XML.Text _) result = result
          | collect (XML.Elem ((name, properties), body)) result =
              let
                val result' =
                  if name = Markup.typingN andalso
                      has_position properties position
                  then XML.content_of body :: result
                  else result
              in fold collect body result' end
      in rev (fold collect trees []) end

    fun assert_neutral active_ctxt label role kind notation
        position trees markup =
      let
        val expected_refs =
          registration_refs active_ctxt kind notation
        val expected_tooltip =
          "registered " ^ role ^ " path qualifier for " ^
            quote notation
      in
        audit_assert (label ^ " retained free markup")
          (count_markup Markup.freeN position markup = 0);
        audit_assert (label ^ " notation navigation changed")
          (entity_refs Micro_Rust_Names.notationN notation
             position markup = expected_refs andalso
           not (null expected_refs));
        audit_assert (label ^ " typing tooltip count changed")
          (count_markup Markup.typingN position markup = 1);
        audit_assert (label ^ " typing tooltip text changed")
          (typing_texts position trees = [expected_tooltip]);
        audit_assert (label ^ " acquired terminal styling")
          (count_markup Markup.keyword3N position markup = 0);
        audit_assert (label ^ " acquired type styling")
          (count_markup Markup.tconstN position markup = 0);
        audit_assert (label ^ " acquired datatype identity")
          (count_entity_kind Markup.type_nameN position markup = 0);
        audit_assert (label ^ " acquired backend constant identity")
          (count_entity_kind Markup.constantN position markup = 0)
      end

    fun assert_terminal active_ctxt label kind notation position markup =
      let
        val expected_refs =
          registration_refs active_ctxt kind notation
        val backend_count = length expected_refs
        val actual_refs =
          entity_refs Micro_Rust_Names.notationN notation
            position markup
        val reported_ranges =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Micro_Rust_Names.notationN andalso
                    Properties.get properties Markup.nameN =
                      SOME notation
                then
                  SOME
                    (the_default "?"
                       (Properties.get properties Markup.offsetN) ^
                     "-" ^
                     the_default "?"
                       (Properties.get properties Markup.end_offsetN))
                else NONE)
      in
        audit_assert
          (label ^ " notation navigation changed: expected refs " ^
            commas expected_refs ^ ", actual refs " ^
            commas actual_refs ^ ", reported ranges " ^
            commas reported_ranges ^ ", expected range " ^
            the_default "?"
              (Option.map Value.print_int
                (Position.offset_of position)) ^
            "-" ^
            the_default "?"
              (Option.map Value.print_int
                (Position.end_offset_of position)))
          (actual_refs = expected_refs);
        audit_assert (label ^ " keyword styling count changed")
          (count_markup Markup.keyword3N position markup =
            backend_count);
        audit_assert (label ^ " backend identity count changed")
          (count_entity_kind Markup.constantN position markup =
            backend_count);
        audit_assert (label ^ " acquired free markup")
          (count_markup Markup.freeN position markup = 0)
      end

    fun assert_no_semantic label position markup =
      (audit_assert (label ^ " acquired free markup")
         (count_markup Markup.freeN position markup = 0);
       audit_assert (label ^ " acquired typing markup")
         (count_markup Markup.typingN position markup = 0);
       audit_assert (label ^ " acquired notation identity")
         (count_entity_kind Micro_Rust_Names.notationN
           position markup = 0);
       audit_assert (label ^ " acquired backend identity")
         (count_entity_kind Markup.constantN position markup = 0);
       audit_assert (label ^ " acquired datatype identity")
         (count_entity_kind Markup.type_nameN position markup = 0);
       audit_assert (label ^ " acquired keyword styling")
         (count_markup Markup.keyword3N position markup = 0))

    val color_text =
      "match_switch Color::Red { Color::Red \<Rightarrow> 1, _ \<Rightarrow> 0 }"
    val (color_start, color_result, color_trees, color_markup) =
      capture color_ctxt 0 "color" color_text NONE
    val _ = ignore (require_success "Color::Red reproduction" color_result)
    val (color_value_raw, _) =
      token_position color_text color_start "Color::Red" 0
    val (_, color_value_qualifier) =
      token_position color_text color_start "Color" color_value_raw
    val (_, color_value_terminal) =
      token_position color_text color_start "Red"
        (color_value_raw + size "Color::")
    val (color_pattern_raw, _) =
      token_position color_text color_start "Color::Red"
        (color_value_raw + size "Color::Red")
    val (_, color_pattern_qualifier) =
      token_position color_text color_start "Color"
        color_pattern_raw
    val (_, color_pattern_terminal) =
      token_position color_text color_start "Red"
        (color_pattern_raw + size "Color::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral color_ctxt label "literal"
            Micro_Rust_Names.NLiteral "Color::Red"
            position color_trees color_markup)
        [("Color::Red scrutinee qualifier", color_value_qualifier),
         ("Color::Red pattern qualifier", color_pattern_qualifier)]
    val _ =
      List.app
        (fn (label, position) =>
          assert_terminal color_ctxt label
            Micro_Rust_Names.NLiteral "Color::Red"
            position color_markup)
        [("Color::Red scrutinee terminal", color_value_terminal),
         ("Color::Red pattern terminal", color_pattern_terminal)]

    val deep_text =
      "match_switch Module::Value::Item { " ^
      "Module::Value::Item \<Rightarrow> 1, _ \<Rightarrow> 0 }"
    val (deep_start, deep_result, deep_trees, deep_markup) =
      capture ctxt 1 "deep-literal" deep_text NONE
    val _ = ignore (require_success "deep literal path" deep_result)
    val (deep_value_raw, _) =
      token_position deep_text deep_start "Module::Value::Item" 0
    val (deep_value_module_raw, deep_value_module) =
      token_position deep_text deep_start "Module" deep_value_raw
    val (_, deep_value_value) =
      token_position deep_text deep_start "Value"
        (deep_value_module_raw + size "Module::")
    val (_, deep_value_terminal) =
      token_position deep_text deep_start "Item"
        (deep_value_raw + size "Module::Value::")
    val (deep_pattern_raw, _) =
      token_position deep_text deep_start "Module::Value::Item"
        (deep_value_raw + size "Module::Value::Item")
    val (deep_pattern_module_raw, deep_pattern_module) =
      token_position deep_text deep_start "Module" deep_pattern_raw
    val (_, deep_pattern_value) =
      token_position deep_text deep_start "Value"
        (deep_pattern_module_raw + size "Module::")
    val (_, deep_pattern_terminal) =
      token_position deep_text deep_start "Item"
        (deep_pattern_raw + size "Module::Value::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral ctxt label "literal"
            Micro_Rust_Names.NLiteral "Module::Value::Item"
            position deep_trees deep_markup)
        [("deep value outer qualifier", deep_value_module),
         ("deep value inner qualifier", deep_value_value),
         ("deep pattern outer qualifier", deep_pattern_module),
         ("deep pattern inner qualifier", deep_pattern_value)]
    val _ =
      List.app
        (fn (label, position) =>
          assert_terminal ctxt label
            Micro_Rust_Names.NLiteral "Module::Value::Item"
            position deep_markup)
        [("deep value terminal", deep_value_terminal),
         ("deep pattern terminal", deep_pattern_terminal)]

    fun audit_call serial label text notation terminal_name
        qualifier_spellings =
      let
        val (start, result, trees, markup) =
          capture ctxt serial label text NONE
        val _ = ignore (require_success label result)
        val _ =
          List.app
            (fn (spelling, offset) =>
              let
                val (_, position) =
                  token_position text start spelling offset
              in
                assert_neutral ctxt
                  (label ^ " qualifier " ^ quote spelling)
                  "call" Micro_Rust_Names.NFunction notation
                  position trees markup
              end)
            qualifier_spellings
        val terminal_offset =
          find_from text terminal_name 0
        val (_, terminal_position) =
          token_position text start terminal_name terminal_offset
        val _ =
          assert_terminal ctxt (label ^ " terminal")
            Micro_Rust_Names.NFunction notation
            terminal_position markup
      in () end

    val _ =
      audit_call 2 "qualified call"
        "Module::Call::invoke()" "Module::Call::invoke" "invoke"
        [("Module", 0), ("Call", size "Module::")]
    val _ =
      audit_call 3 "qualified struct head"
        "StructModule::Builder::new { value: 7 }"
        "StructModule::Builder::new" "new"
        [("StructModule", 0),
         ("Builder", size "StructModule::")]
    val _ =
      audit_call 4 "base registration with turbofish"
        "GenericBase::invoke::<1>(2)"
        "GenericBase::invoke" "invoke"
        [("GenericBase", 0)]
    val _ =
      audit_call 5 "exact generic registration"
        "GenericExact::<Token>::invoke()"
        "GenericExact::<Token>::invoke" "invoke"
        [("GenericExact", 0)]

    fun audit_macro serial label text notation qualifier terminal_name =
      let
        val (start, result, trees, markup) =
          capture ctxt serial label text NONE
        val _ = ignore (require_success label result)
        val (_, qualifier_position) =
          token_position text start qualifier 0
        val (_, terminal_position) =
          token_position text start terminal_name
            (find_from text terminal_name 0)
        val (_, bang_position) =
          token_position text start "!" 0
        val _ =
          assert_neutral ctxt (label ^ " qualifier") "call"
            Micro_Rust_Names.NFunction notation
            qualifier_position trees markup
        val _ =
          assert_terminal ctxt (label ^ " identifier terminal")
            Micro_Rust_Names.NFunction notation
            terminal_position markup
        val _ =
          audit_assert (label ^ " bang operator markup changed")
            (count_markup Markup.operatorN bang_position markup = 1)
        val _ =
          audit_assert (label ^ " bang acquired notation navigation")
            (count_entity_kind Micro_Rust_Names.notationN
              bang_position markup = 0)
        val _ =
          audit_assert (label ^ " bang selected-backend count changed")
            (count_entity_kind Markup.constantN
              bang_position markup = 1)
        val _ =
          audit_assert (label ^ " bang constant styling changed")
            (count_markup Markup.constN bang_position markup = 1)
      in () end

    val _ =
      audit_macro 6 "qualified macro"
        "MacroModule::invoke!(true)"
        "MacroModule::invoke!" "MacroModule" "invoke"
    val _ =
      audit_macro 7 "generic qualified macro"
        "MacroGeneric::<Token>::invoke!(true)"
        "MacroGeneric::<Token>::invoke!" "MacroGeneric" "invoke"

    val multi_text = "Multi::Registered::Value"
    val (multi_start, multi_result, multi_trees, multi_markup) =
      capture ctxt 8 "multi-backend" multi_text
        (SOME "(unit, nat, unit, unit, unit, unit) expression")
    val _ = ignore (require_success "multi-backend literal" multi_result)
    val (multi_outer_raw, multi_outer) =
      token_position multi_text multi_start "Multi" 0
    val (_, multi_inner) =
      token_position multi_text multi_start "Registered"
        (multi_outer_raw + size "Multi::")
    val (_, multi_terminal) =
      token_position multi_text multi_start "Value"
        (size "Multi::Registered::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral ctxt label "literal"
            Micro_Rust_Names.NLiteral "Multi::Registered::Value"
            position multi_trees multi_markup)
        [("multi-backend outer qualifier", multi_outer),
         ("multi-backend inner qualifier", multi_inner)]
    val _ =
      assert_terminal ctxt "multi-backend terminal"
        Micro_Rust_Names.NLiteral "Multi::Registered::Value"
        multi_terminal multi_markup
    val _ =
      audit_assert "multi-backend qualifier tooltip multiplied"
        (count_markup Markup.typingN multi_outer multi_markup = 1)

    val duplicate_text = "Duplicate::Registered::Value"
    val (duplicate_start, duplicate_result,
         duplicate_trees, duplicate_markup) =
      capture ctxt 9 "duplicate-registration" duplicate_text NONE
    val _ =
      ignore (require_success "duplicate registration" duplicate_result)
    val (duplicate_outer_raw, duplicate_outer) =
      token_position duplicate_text duplicate_start "Duplicate" 0
    val (_, duplicate_inner) =
      token_position duplicate_text duplicate_start "Registered"
        (duplicate_outer_raw + size "Duplicate::")
    val (_, duplicate_terminal) =
      token_position duplicate_text duplicate_start "Value"
        (size "Duplicate::Registered::")
    val _ =
      audit_assert "idempotent duplicate survived in registry"
        (length
          (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral
            "Duplicate::Registered::Value") = 1)
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral ctxt label "literal"
            Micro_Rust_Names.NLiteral
            "Duplicate::Registered::Value"
            position duplicate_trees duplicate_markup)
        [("duplicate outer qualifier", duplicate_outer),
         ("duplicate inner qualifier", duplicate_inner)]
    val _ =
      assert_terminal ctxt "duplicate terminal"
        Micro_Rust_Names.NLiteral "Duplicate::Registered::Value"
        duplicate_terminal duplicate_markup

    val families_text = "Module::Families::Variant"
    val (families_start, families_result,
         families_trees, families_markup) =
      capture ctxt 10 "constructor-families" families_text
        (SOME
          "(unit, constructor_qualifier_left, unit, unit, unit, unit) expression")
    val _ =
      ignore (require_success "constructor families" families_result)
    val (families_outer_raw, families_outer) =
      token_position families_text families_start "Module" 0
    val (_, families_nearest) =
      token_position families_text families_start "Families"
        (families_outer_raw + size "Module::")
    val (_, families_terminal) =
      token_position families_text families_start "Variant"
        (size "Module::Families::")
    val _ =
      assert_neutral ctxt "constructor outer module qualifier"
        "literal" Micro_Rust_Names.NLiteral
        "Module::Families::Variant"
        families_outer families_trees families_markup
    val _ =
      audit_assert "nearest constructor qualifier retained free markup"
        (count_markup Markup.freeN families_nearest families_markup = 0)
    val _ =
      audit_assert "nearest constructor qualifier lost family navigation"
        (count_entity_kind Markup.type_nameN
          families_nearest families_markup = 2)
    val _ =
      audit_assert "nearest constructor qualifier styling count changed"
        (count_markup Markup.keyword3N
          families_nearest families_markup = 2)
    val _ =
      audit_assert "nearest constructor qualifier notation count changed"
        (count_entity_kind Micro_Rust_Names.notationN
           families_nearest families_markup = 2)
    val _ =
      audit_assert "nearest constructor qualifier acquired neutral tooltip"
        (count_markup Markup.typingN
           families_nearest families_markup = 0)
    val _ =
      assert_terminal ctxt "multi-family constructor terminal"
        Micro_Rust_Names.NLiteral "Module::Families::Variant"
        families_terminal families_markup

    fun failure_case serial label text qualifier =
      let
        val (start, result, _, markup) =
          capture ctxt serial label text NONE
        val _ = require_failure label result
        val (_, qualifier_position) =
          token_position text start qualifier 0
        val _ =
          assert_no_semantic (label ^ " qualifier")
            qualifier_position markup
      in () end

    val _ =
      failure_case 11 "wrong role"
        "Wrong::Role::Item" "Wrong"
    val _ =
      failure_case 12 "unregistered path"
        "Missing::Path::Item" "Missing"
    val _ =
      failure_case 13 "nonadjacent registered macro"
        "MacroModule::invoke !(true)" "MacroModule"

    val malformed_text =
      "match_case Type::Variant { " ^
      "Type::Variant(value) \<Rightarrow> (), _ \<Rightarrow> () }"
    val (malformed_start, malformed_result, _, malformed_markup) =
      capture ctxt 14 "malformed-constructor" malformed_text NONE
    val _ =
      require_failure "malformed constructor pattern" malformed_result
    val first_variant =
      find_from malformed_text "Type::Variant" 0
    val second_variant =
      find_from malformed_text "Type::Variant"
        (first_variant + size "Type::Variant")
    val (_, malformed_qualifier) =
      token_position malformed_text malformed_start "Type"
        second_variant
    val (_, malformed_terminal) =
      token_position malformed_text malformed_start "Variant"
        (second_variant + size "Type::")
    val _ =
      assert_no_semantic "malformed constructor qualifier"
        malformed_qualifier malformed_markup
    val _ =
      assert_no_semantic "malformed constructor terminal"
        malformed_terminal malformed_markup

    val recovery_text = "Module::Value::Item"
    val (recovery_start, recovery_result,
         recovery_trees, recovery_markup) =
      capture ctxt 15 "recovery" recovery_text NONE
    val _ =
      ignore (require_success "post-failure recovery" recovery_result)
    val (_, recovery_qualifier) =
      token_position recovery_text recovery_start "Module" 0
    val _ =
      assert_neutral ctxt "post-failure recovery qualifier"
        "literal" Micro_Rust_Names.NLiteral
        "Module::Value::Item"
        recovery_qualifier recovery_trees recovery_markup

    val single_text = "registered_seven"
    val (single_start, single_result, _, single_markup) =
      capture ctxt 16 "single-segment" single_text NONE
    val _ =
      ignore (require_success "single-segment registration" single_result)
    val (_, single_position) =
      token_position single_text single_start single_text 0
    val _ =
      assert_terminal ctxt "single-segment registration"
        Micro_Rust_Names.NLiteral "registered_seven"
        single_position single_markup

    val unresolved_text = "actual_unresolved_identifier"
    val (unresolved_start, unresolved_result, _, unresolved_markup) =
      capture ctxt 17 "unresolved-control" unresolved_text NONE
    val _ =
      ignore (require_success "unresolved identifier control"
        unresolved_result)
    val (_, unresolved_position) =
      token_position unresolved_text unresolved_start unresolved_text 0
    val _ =
      audit_assert "genuine unresolved identifier lost free markup"
        (count_markup Markup.freeN
          unresolved_position unresolved_markup = 1)

    val lexical_text =
      "let lexical_control = 1; lexical_control"
    val (lexical_start, lexical_result, _, lexical_markup) =
      capture ctxt 18 "lexical-control" lexical_text NONE
    val _ =
      ignore (require_success "lexical binder control" lexical_result)
    val (lexical_definition_raw, lexical_definition) =
      token_position lexical_text lexical_start "lexical_control" 0
    val (_, lexical_reference) =
      token_position lexical_text lexical_start "lexical_control"
        (lexical_definition_raw + size "lexical_control")
    val _ =
      List.app
        (fn (label, position) =>
          (audit_assert (label ^ " lost bound markup")
             (count_markup Markup.boundN position lexical_markup = 1);
           audit_assert (label ^ " acquired free markup")
             (count_markup Markup.freeN position lexical_markup = 0)))
        [("lexical definition", lexical_definition),
         ("lexical reference", lexical_reference)]

    val (_, fixed_ctxt) =
      Proof_Context.add_fixes
        [(Binding.name "fixed_qualifier_control",
          SOME \<^typ>\<open>nat\<close>, NoSyn)]
        ctxt
    val fixed_text = "fixed_qualifier_control"
    val (fixed_start, fixed_result, _, fixed_markup) =
      capture fixed_ctxt 19 "fixed-control" fixed_text NONE
    val _ =
      ignore (require_success "fixed identifier control" fixed_result)
    val (_, fixed_position) =
      token_position fixed_text fixed_start fixed_text 0
    val _ =
      audit_assert "fixed parameter changed free-name markup"
        (count_markup Markup.freeN fixed_position fixed_markup = 1)
  in
    val _ =
      writeln
        "Neutral registered qualifier navigation, tooltip, styling, multiplicity, constructor, failure, recovery, and binder-boundary regressions passed"
  end
\<close>


section\<open> Lifted backend navigation audit \<close>

definition lifted_navigation_pure :: \<open>nat \<Rightarrow> nat\<close>
  where \<open> lifted_navigation_pure value = value + 1 \<close>

micro_rust_notation (call)
  \<open>lift_fun1 lifted_navigation_pure\<close>
  ("LiftedNavigation::named")

micro_rust_notation (call)
  \<open>lift_fun1 (\<lambda>value :: nat. value)\<close>
  ("LiftedNavigation::anonymous")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("lifted backend navigation audit: " ^ message)

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
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture serial label text declared_type =
      let
        val start =
          Position.make0 (240 + serial) (60000 + serial * 600) 0 "" ""
            ("lifted-navigation-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val ast =
          (case URust_Parser.parse_source ctxt source of
             SOME expression => expression
           | NONE => error (label ^ " parsed as empty input"))
        val captured =
          Synchronized.var
            ("lifted_navigation_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        URust_Command.elaborate ctxt
                          {kind = URust_Command.Expression,
                           source = source,
                           arguments = [],
                           arguments_pos = #2 (Input.range_of source),
                           declared_type =
                             Option.map
                               (fn typ => (typ, Position.none))
                               declared_type}) ())
                  ())
              ())
        val term =
          (case result of
             Exn.Res checked => checked
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 error
                   (label ^ " failed: " ^ Runtime.exn_message exn))
        val trees =
          maps YXML.parse_body (Synchronized.value captured)
      in
        (start, ast, term, fold collect_markup trees [])
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun entity_names kind position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN = SOME kind andalso
                has_position properties position
            then Properties.get properties Markup.nameN
            else NONE)

    fun count_entity kind name position markup =
      entity_names kind position markup
      |> filter (fn actual => actual = name)
      |> length

    fun distinct_entity_names kind position markup =
      entity_names kind position markup
      |> distinct (op =)
      |> sort_strings

    fun assert_registered_terminal
        label notation target position markup =
      (audit_assert (label ^ " notation navigation count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = 1);
       audit_assert (label ^ " lost keyword3 styling")
         (count_markup Markup.keyword3N position markup = 1);
       audit_assert (label ^ " did not link to wrapped target")
         (count_entity Markup.constantN target position markup >= 1);
       audit_assert (label ^ " retained lift_fun1 navigation")
         (count_entity Markup.constantN
           \<^const_name>\<open>lift_fun1\<close> position markup = 0);
       audit_assert (label ^ " linked to an unrelated constant")
         (distinct_entity_names Markup.constantN position markup =
           [target]))

    fun assert_pattern_terminal label target position markup =
      (audit_assert (label ^ " acquired notation navigation")
         (entity_names Micro_Rust_Names.notationN
           position markup = []);
       audit_assert (label ^ " acquired registered keyword styling")
         (count_markup Markup.keyword3N position markup = 0);
       audit_assert (label ^ " did not retain native constructor navigation")
         (distinct_entity_names Markup.constantN position markup =
           [target]);
       audit_assert (label ^ " linked to lift_fun1")
         (count_entity Markup.constantN
           \<^const_name>\<open>lift_fun1\<close> position markup = 0))

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun assert_call_ast label expected expected_arity ast =
      (case ast of
         UE_Call (UC_Path path, arguments, _) =>
           (audit_assert (label ^ " call path changed")
              (render_path path = expected);
            audit_assert (label ^ " call arity changed")
              (length arguments = expected_arity))
       | _ => error (label ^ " call AST changed"))

    fun assert_match_ast label value_name pattern_name ast =
      (case ast of
         UE_Match
           (_, UE_Call (UC_Path value_path, [_], _),
            UR_Arm
              (P_Constr (pattern_path, [_], _), _, _, _) :: _, _) =>
           (audit_assert (label ^ " value-call AST changed")
              (render_path value_path = value_name);
            audit_assert (label ^ " constructor-pattern AST changed")
              (render_path pattern_path = pattern_name))
       | _ => error (label ^ " match AST changed"))

    fun assert_wrapped_registration notation wrapped =
      (case
        Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction notation of
         [{hol_term, ...}] =>
           (case Term.strip_comb
               (Term_Position.strip_positions hol_term) of
              (Const (wrapper, _), [argument]) =>
                (audit_assert (notation ^ " registration wrapper changed")
                   (wrapper = \<^const_name>\<open>lift_fun1\<close>);
                 audit_assert (notation ^ " wrapped backend changed")
                   (wrapped argument))
            | _ => error (notation ^ " registration term shape changed"))
       | _ => error (notation ^ " registration multiplicity changed"))

    val some_text =
      "match_case Some(\<llangle>1 :: nat\<rrangle>) { " ^
      "Some(value) \<Rightarrow> value, None \<Rightarrow> 0 }"
    val (some_start, some_ast, some_term, some_markup) =
      capture 0 "some" some_text NONE
    val (some_value_raw, some_value_position) =
      token_position some_text some_start "Some" 0
    val (_, some_pattern_position) =
      token_position some_text some_start "Some"
        (some_value_raw + size "Some")
    val _ =
      assert_registered_terminal "Some value" "Some"
        \<^const_name>\<open>Option.Some\<close>
        some_value_position some_markup
    val _ =
      assert_pattern_terminal "Some pattern"
        \<^const_name>\<open>Option.Some\<close>
        some_pattern_position some_markup
    val _ =
      assert_match_ast "Some" "Some" "Some" some_ast
    val _ =
      audit_assert "Some checked term lost lift_fun1"
        (count_constant \<^const_name>\<open>lift_fun1\<close> some_term = 1)
    val _ =
      audit_assert "Some checked term lost Option.Some"
        (count_constant \<^const_name>\<open>Option.Some\<close> some_term = 1)

    val ok_text =
      "match_case Ok(\<llangle>1 :: nat\<rrangle>) { " ^
      "Ok(value) \<Rightarrow> value, Err(error) \<Rightarrow> error }"
    val (ok_start, ok_ast, ok_term, ok_markup) =
      capture 1 "ok" ok_text NONE
    val (ok_value_raw, ok_value_position) =
      token_position ok_text ok_start "Ok" 0
    val (_, ok_pattern_position) =
      token_position ok_text ok_start "Ok"
        (ok_value_raw + size "Ok")
    val (_, err_pattern_position) =
      token_position ok_text ok_start "Err" 0
    val _ =
      assert_registered_terminal "Ok value" "Ok"
        \<^const_name>\<open>Ok\<close> ok_value_position ok_markup
    val _ =
      assert_pattern_terminal "Ok pattern"
        \<^const_name>\<open>Ok\<close> ok_pattern_position ok_markup
    val _ =
      assert_pattern_terminal "Err pattern"
        \<^const_name>\<open>Err\<close> err_pattern_position ok_markup
    val _ =
      assert_match_ast "Ok" "Ok" "Ok" ok_ast
    val _ =
      audit_assert "Ok checked term lost lift_fun1"
        (count_constant \<^const_name>\<open>lift_fun1\<close> ok_term = 1)
    val _ =
      audit_assert "Ok checked term lost result constructors"
        (count_constant \<^const_name>\<open>Ok\<close> ok_term = 1)

    val err_text = "Err(\<llangle>1 :: nat\<rrangle>)"
    val (err_start, err_ast, err_term, err_markup) =
      capture 2 "err" err_text NONE
    val (_, err_value_position) =
      token_position err_text err_start "Err" 0
    val _ =
      assert_registered_terminal "Err value" "Err"
        \<^const_name>\<open>Err\<close> err_value_position err_markup
    val _ = assert_call_ast "Err" "Err" 1 err_ast
    val _ =
      audit_assert "Err checked term shape changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close> err_term = 1 andalso
         count_constant \<^const_name>\<open>Err\<close> err_term = 1)

    val named_text =
      "LiftedNavigation::named(\<llangle>4 :: nat\<rrangle>)"
    val (named_start, named_ast, named_term, named_markup) =
      capture 3 "named" named_text NONE
    val (named_outer_raw, named_qualifier) =
      token_position named_text named_start "LiftedNavigation" 0
    val (_, named_terminal) =
      token_position named_text named_start "named"
        (named_outer_raw + size "LiftedNavigation::")
    val _ =
      assert_registered_terminal "named lifted function"
        "LiftedNavigation::named"
        \<^const_name>\<open>lifted_navigation_pure\<close>
        named_terminal named_markup
    val _ =
      audit_assert "named lifted qualifier notation changed"
        (count_entity Micro_Rust_Names.notationN
           "LiftedNavigation::named"
           named_qualifier named_markup = 1)
    val _ =
      audit_assert "named lifted qualifier typing changed"
        (count_markup Markup.typingN
           named_qualifier named_markup = 1)
    val _ =
      audit_assert "named lifted qualifier acquired terminal identity"
        (entity_names Markup.constantN
           named_qualifier named_markup = [])
    val _ =
      assert_call_ast "named lifted function"
        "LiftedNavigation::named" 1 named_ast
    val _ =
      audit_assert "named lifted checked term changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close> named_term = 1 andalso
         count_constant \<^const_name>\<open>lifted_navigation_pure\<close>
           named_term = 1)

    val anonymous_text =
      "LiftedNavigation::anonymous(\<llangle>5 :: nat\<rrangle>)"
    val (anonymous_start, anonymous_ast,
         anonymous_term, anonymous_markup) =
      capture 4 "anonymous" anonymous_text NONE
    val (_, anonymous_terminal) =
      token_position anonymous_text anonymous_start "anonymous"
        (size "LiftedNavigation::")
    val _ =
      audit_assert "lifted lambda notation navigation changed"
        (count_entity Micro_Rust_Names.notationN
           "LiftedNavigation::anonymous"
           anonymous_terminal anonymous_markup = 1)
    val _ =
      audit_assert "lifted lambda lost keyword3 styling"
        (count_markup Markup.keyword3N
           anonymous_terminal anonymous_markup = 1)
    val _ =
      audit_assert "lifted lambda acquired a constant target"
        (entity_names Markup.constantN
           anonymous_terminal anonymous_markup = [])
    val _ =
      assert_call_ast "lifted lambda"
        "LiftedNavigation::anonymous" 1 anonymous_ast
    val _ =
      audit_assert "lifted lambda checked term lost its wrapper"
        (count_constant \<^const_name>\<open>lift_fun1\<close>
           anonymous_term = 1)

    val ordinary_text = "Module::Call::invoke()"
    val (ordinary_start, ordinary_ast,
         ordinary_term, ordinary_markup) =
      capture 5 "ordinary" ordinary_text NONE
    val (_, ordinary_terminal) =
      token_position ordinary_text ordinary_start "invoke"
        (size "Module::Call::")
    val _ =
      audit_assert "ordinary registration navigation changed"
        (distinct_entity_names Markup.constantN
           ordinary_terminal ordinary_markup =
           [\<^const_name>\<open>constructor_qualifier_call\<close>])
    val _ =
      audit_assert "ordinary registration styling changed"
        (count_markup Markup.keyword3N
           ordinary_terminal ordinary_markup = 1)
    val _ =
      assert_call_ast "ordinary registration"
        "Module::Call::invoke" 0 ordinary_ast
    val _ =
      audit_assert "ordinary checked term changed"
        (count_constant \<^const_name>\<open>constructor_qualifier_call\<close>
           ordinary_term = 1)

    val multi_text = "Multi::Registered::Value"
    val (multi_start, multi_ast, multi_term, multi_markup) =
      capture 6 "multiplicity" multi_text
        (SOME "(unit, nat, unit, unit, unit, unit) expression")
    val (multi_outer_raw, multi_outer) =
      token_position multi_text multi_start "Multi" 0
    val (_, multi_inner) =
      token_position multi_text multi_start "Registered"
        (multi_outer_raw + size "Multi::")
    val (_, multi_terminal) =
      token_position multi_text multi_start "Value"
        (size "Multi::Registered::")
    val _ =
      audit_assert "multi-backend registration count changed"
        (length
          (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral
            "Multi::Registered::Value") = 2)
    val _ =
      List.app
        (fn position =>
          (audit_assert "multi-backend qualifier notation changed"
             (count_entity Micro_Rust_Names.notationN
                "Multi::Registered::Value"
                position multi_markup = 2);
           audit_assert "multi-backend qualifier tooltip multiplied"
             (count_markup Markup.typingN position multi_markup = 1);
           audit_assert "multi-backend qualifier acquired constant identity"
             (entity_names Markup.constantN position multi_markup = [])))
        [multi_outer, multi_inner]
    val _ =
      audit_assert "multi-backend terminal notation count changed"
        (count_entity Micro_Rust_Names.notationN
           "Multi::Registered::Value"
           multi_terminal multi_markup = 2)
    val _ =
      audit_assert "multi-backend terminal targets changed"
        (distinct_entity_names Markup.constantN
           multi_terminal multi_markup =
           sort_strings
             [\<^const_name>\<open>qualifier_multi_nat\<close>,
              \<^const_name>\<open>qualifier_multi_bool\<close>])
    val _ =
      (case multi_ast of
         UE_Path path =>
           audit_assert "multi-backend value AST changed"
             (render_path path = "Multi::Registered::Value")
       | _ => error "multi-backend value AST changed")
    val _ =
      audit_assert "multi-backend checked term selected a different backend"
        (count_constant \<^const_name>\<open>qualifier_multi_nat\<close>
           multi_term = 1 andalso
         count_constant \<^const_name>\<open>qualifier_multi_bool\<close>
           multi_term = 0)

    val _ =
      assert_wrapped_registration "Some"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) => name = \<^const_name>\<open>Option.Some\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "Ok"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) => name = \<^const_name>\<open>Ok\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "Err"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) => name = \<^const_name>\<open>Err\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "LiftedNavigation::named"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) =>
               name = \<^const_name>\<open>lifted_navigation_pure\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "LiftedNavigation::anonymous"
        (fn Abs _ => true | _ => false)
  in
    val _ =
      writeln
        "Lifted constructor/function navigation, neutral patterns, wrapper-free lambdas, registration shape, AST, term, qualifier, and multiplicity regressions passed"
  end
\<close>


section\<open> Selected notation declaration navigation audit \<close>

definition selected_navigation_call_nat ::
    \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      selected_navigation_call_nat =
        lift_fun1 (\<lambda>value. value)
    \<close>

definition selected_navigation_call_bool ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      selected_navigation_call_bool =
        lift_fun1 (\<lambda>value. value)
    \<close>

micro_rust_notation (call)
  selected_navigation_call_nat
  ("Selected::Call::invoke")
micro_rust_notation (call)
  selected_navigation_call_bool
  ("Selected::Call::invoke")

datatype_record selected_navigation_record =
  selected_navigation_member :: nat

micro_rust_record selected_navigation_record
  (selected_navigation_member = "selected_navigation_field")

definition selected_navigation_record_value :: selected_navigation_record
  where
    \<open>
      selected_navigation_record_value =
        make_selected_navigation_record 7
    \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else
        error
          ("selected notation declaration navigation audit: " ^
            message)

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
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup_order (XML.Text _) = []
      | collect_markup_order (XML.Elem (markup, body)) =
          markup :: maps collect_markup_order body

    fun capture active_ctxt serial label text declared_type =
      let
        val start =
          Position.make0 (300 + serial) (80000 + serial * 800) 0 "" ""
            ("selected-notation-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val ast =
          (case URust_Parser.parse_source active_ctxt source of
             SOME expression => expression
           | NONE => error (label ^ " parsed as empty input"))
        val captured =
          Synchronized.var
            ("selected_notation_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured
            (fn current => current @ chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        URust_Command.elaborate active_ctxt
                          {kind = URust_Command.Expression,
                           source = source,
                           arguments = [],
                           arguments_pos = #2 (Input.range_of source),
                           declared_type =
                             Option.map
                               (fn typ => (typ, Position.none))
                               declared_type}) ())
                  ())
              ())
        val term =
          (case result of
             Exn.Res checked => checked
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 error
                   (label ^ " failed: " ^
                     Runtime.exn_message exn))
        val markup =
          Synchronized.value captured
          |> maps YXML.parse_body
          |> maps collect_markup_order
      in
        (start, ast, term, markup)
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun entity_events position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                has_position properties position
            then
              SOME
                (Properties.get properties Markup.kindN,
                 Properties.get properties Markup.nameN,
                 Properties.get properties Markup.refN)
            else NONE)

    fun notation_ref_order notation position markup =
      entity_events position markup
      |> map_filter
          (fn (SOME kind, SOME name, ref_id) =>
                if kind = Micro_Rust_Names.notationN andalso
                    name = notation
                then ref_id
                else NONE
            | _ => NONE)

    fun entry_ref ({serial, ...} : Micro_Rust_Names.entry) =
      Value.print_int serial

    fun selected_last_refs active_ctxt kind notation selected =
      let
        val entries = Micro_Rust_Names.lookups active_ctxt kind notation
      in
        entries
        |> filter
            (fn (entry : Micro_Rust_Names.entry) =>
              #serial entry <> #serial selected)
        |> map entry_ref
        |> (fn refs => refs @ [entry_ref selected])
      end

    fun backend_head_name ({hol_term, ...} : Micro_Rust_Names.entry) =
      (case Term.head_of (Term_Position.strip_positions hol_term) of
         Const (name, _) => SOME name
       | _ => NONE)

    fun entry_for_constant active_ctxt kind notation constant =
      (case
        Micro_Rust_Names.lookups active_ctxt kind notation
        |> filter
            (fn entry =>
              backend_head_name entry = SOME constant)
       of
         [entry] => entry
       | entries =>
           error
             ("expected one " ^ quote notation ^
               " registration for " ^ quote constant ^
               ", got " ^ string_of_int (length entries)))

    fun only_entry active_ctxt kind notation =
      (case Micro_Rust_Names.lookups active_ctxt kind notation of
         [entry] => entry
       | entries =>
           error
             ("expected one registration for " ^ quote notation ^
               ", got " ^ string_of_int (length entries)))

    fun is_backend_kind (SOME kind) =
          kind = Markup.constantN orelse kind = Markup.type_nameN
      | is_backend_kind NONE = false

    fun backend_entities_precede_notations events =
      let
        fun check _ [] = true
          | check seen_notation ((kind, _, _) :: rest) =
              if kind = SOME Micro_Rust_Names.notationN
              then check true rest
              else if seen_notation andalso is_backend_kind kind
              then false
              else check seen_notation rest
      in check false events end

    fun assert_selected_token active_ctxt label kind notation selected
        position markup =
      let
        val expected =
          selected_last_refs active_ctxt kind notation selected
        val actual =
          notation_ref_order notation position markup
        val events = entity_events position markup
        val final_event =
          if null events then NONE else SOME (List.last events)
      in
        audit_assert (label ^ " notation references changed")
          (actual = expected);
        audit_assert (label ^ " selected declaration was not final")
          (final_event =
            SOME
              (SOME Micro_Rust_Names.notationN,
               SOME notation,
               SOME (entry_ref selected)));
        audit_assert (label ^ " backend/type entity followed notation")
          (backend_entities_precede_notations events)
      end

    fun count_entity_kind kind position markup =
      entity_events position markup
      |> filter
          (fn (SOME actual, _, _) => actual = kind
            | _ => false)
      |> length

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun assert_path_ast label expected ast =
      (case ast of
         UE_Path path =>
           audit_assert (label ^ " path AST changed")
             (render_path path = expected)
       | _ => error (label ^ " path AST changed"))

    fun assert_call_ast label expected ast =
      (case ast of
         UE_Call (UC_Path path, _, _) =>
           audit_assert (label ^ " call AST changed")
             (render_path path = expected)
       | _ => error (label ^ " call AST changed"))

    val literal_text = "Multi::Registered::Value"
    val (literal_nat_start, literal_nat_ast,
         literal_nat_term, literal_nat_markup) =
      capture ctxt 0 "literal-nat" literal_text
        (SOME "(unit, nat, unit, unit, unit, unit) expression")
    val (literal_nat_outer_raw, literal_nat_outer) =
      token_position literal_text literal_nat_start "Multi" 0
    val (_, literal_nat_inner) =
      token_position literal_text literal_nat_start "Registered"
        (literal_nat_outer_raw + size "Multi::")
    val (_, literal_nat_terminal) =
      token_position literal_text literal_nat_start "Value"
        (size "Multi::Registered::")
    val literal_nat_entry =
      entry_for_constant ctxt Micro_Rust_Names.NLiteral
        literal_text \<^const_name>\<open>qualifier_multi_nat\<close>
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NLiteral literal_text
            literal_nat_entry position literal_nat_markup)
        [("nat literal outer qualifier", literal_nat_outer),
         ("nat literal inner qualifier", literal_nat_inner),
         ("nat literal terminal", literal_nat_terminal)]
    val _ = assert_path_ast "nat literal" literal_text literal_nat_ast
    val _ =
      audit_assert "nat literal selected backend term changed"
        (count_constant \<^const_name>\<open>qualifier_multi_nat\<close>
           literal_nat_term = 1 andalso
         count_constant \<^const_name>\<open>qualifier_multi_bool\<close>
           literal_nat_term = 0)

    val (literal_bool_start, literal_bool_ast,
         literal_bool_term, literal_bool_markup) =
      capture ctxt 1 "literal-bool" literal_text
        (SOME "(unit, bool, unit, unit, unit, unit) expression")
    val (literal_bool_outer_raw, literal_bool_outer) =
      token_position literal_text literal_bool_start "Multi" 0
    val (_, literal_bool_inner) =
      token_position literal_text literal_bool_start "Registered"
        (literal_bool_outer_raw + size "Multi::")
    val (_, literal_bool_terminal) =
      token_position literal_text literal_bool_start "Value"
        (size "Multi::Registered::")
    val literal_bool_entry =
      entry_for_constant ctxt Micro_Rust_Names.NLiteral
        literal_text \<^const_name>\<open>qualifier_multi_bool\<close>
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NLiteral literal_text
            literal_bool_entry position literal_bool_markup)
        [("bool literal outer qualifier", literal_bool_outer),
         ("bool literal inner qualifier", literal_bool_inner),
         ("bool literal terminal", literal_bool_terminal)]
    val _ = assert_path_ast "bool literal" literal_text literal_bool_ast
    val _ =
      audit_assert "bool literal selected backend term changed"
        (count_constant \<^const_name>\<open>qualifier_multi_bool\<close>
           literal_bool_term = 1 andalso
         count_constant \<^const_name>\<open>qualifier_multi_nat\<close>
           literal_bool_term = 0)

    fun audit_overloaded_call serial label argument selected_constant =
      let
        val notation = "Selected::Call::invoke"
        val text = notation ^ "(" ^ argument ^ ")"
        val (start, ast, term, markup) =
          capture ctxt serial label text NONE
        val (outer_raw, outer) =
          token_position text start "Selected" 0
        val (_, inner) =
          token_position text start "Call"
            (outer_raw + size "Selected::")
        val (_, terminal) =
          token_position text start "invoke"
            (size "Selected::Call::")
        val selected =
          entry_for_constant ctxt Micro_Rust_Names.NFunction
            notation selected_constant
        val _ =
          List.app
            (fn (token_label, position) =>
              assert_selected_token ctxt
                (label ^ " " ^ token_label)
                Micro_Rust_Names.NFunction notation
                selected position markup)
            [("outer qualifier", outer),
             ("inner qualifier", inner),
             ("terminal", terminal)]
        val _ = assert_call_ast label notation ast
        val _ =
          audit_assert (label ^ " selected backend term changed")
            (count_constant selected_constant term = 1)
      in () end

    val _ =
      audit_overloaded_call 2 "nat call"
        "\<llangle>7 :: nat\<rrangle>"
        \<^const_name>\<open>selected_navigation_call_nat\<close>
    val _ =
      audit_overloaded_call 3 "bool call"
        "true"
        \<^const_name>\<open>selected_navigation_call_bool\<close>

    val field_text =
      "\<llangle>selected_navigation_record_value\<rrangle>." ^
      "selected_navigation_field"
    val (field_start, _, field_term, field_markup) =
      capture ctxt 4 "field" field_text NONE
    val (_, field_position) =
      token_position field_text field_start
        "selected_navigation_field" 0
    val field_entry =
      only_entry ctxt Micro_Rust_Names.NField
        "selected_navigation_field"
    val field_backend =
      the (backend_head_name field_entry)
    val _ =
      assert_selected_token ctxt "field"
        Micro_Rust_Names.NField "selected_navigation_field"
        field_entry field_position field_markup
    val _ =
      audit_assert "field backend term changed"
        (count_constant field_backend field_term = 1)

    val constructor_text =
      "match_case \<llangle>ConstructorQualifierVariant\<rrangle> { " ^
      "Module::Type::Variant \<Rightarrow> (), _ \<Rightarrow> () }"
    val (constructor_start, _, _, constructor_markup) =
      capture ctxt 5 "constructor-pattern" constructor_text NONE
    val (constructor_path_raw, _) =
      token_position constructor_text constructor_start
        "Module::Type::Variant" 0
    val (constructor_outer_raw, constructor_outer) =
      token_position constructor_text constructor_start "Module"
        constructor_path_raw
    val (_, constructor_nearest) =
      token_position constructor_text constructor_start "Type"
        (constructor_outer_raw + size "Module::")
    val (_, constructor_terminal) =
      token_position constructor_text constructor_start "Variant"
        (constructor_path_raw + size "Module::Type::")
    val constructor_entry =
      only_entry ctxt Micro_Rust_Names.NLiteral
        "Module::Type::Variant"
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NLiteral
            "Module::Type::Variant"
            constructor_entry position constructor_markup)
        [("constructor outer qualifier", constructor_outer),
         ("constructor datatype qualifier", constructor_nearest),
         ("constructor terminal", constructor_terminal)]
    val _ =
      audit_assert "constructor datatype hover disappeared"
        (count_entity_kind Markup.type_nameN
           constructor_nearest constructor_markup = 1)
    val _ =
      audit_assert "constructor terminal backend hover disappeared"
        (count_entity_kind Markup.constantN
           constructor_terminal constructor_markup = 1)

    fun audit_registered_call serial label text notation qualifier
        terminal_name expected_backend =
      let
        val (start, ast, term, markup) =
          capture ctxt serial label text NONE
        val (_, qualifier_position) =
          token_position text start qualifier 0
        val terminal_position =
          #2
            (token_position text start terminal_name
              (find_from text terminal_name 0))
        val entry =
          only_entry ctxt Micro_Rust_Names.NFunction notation
        val _ =
          List.app
            (fn (token_label, position) =>
              assert_selected_token ctxt
                (label ^ " " ^ token_label)
                Micro_Rust_Names.NFunction notation entry
                position markup)
            [("qualifier", qualifier_position),
             ("terminal", terminal_position)]
        val _ =
          audit_assert (label ^ " backend hover disappeared")
            (count_entity_kind Markup.constantN
              terminal_position markup >= 1)
        val _ =
          audit_assert (label ^ " checked backend changed")
            (count_constant expected_backend term = 1)
        val _ =
          if String.isSuffix "!" notation then
            let
              val (_, bang_position) =
                token_position text start "!" 0
              val bang_events =
                entity_events bang_position markup
            in
              audit_assert
                (label ^ " bang acquired notation navigation")
                (notation_ref_order notation bang_position markup = []);
              audit_assert
                (label ^ " bang target changed")
                (map
                  (fn (kind, name, _) => (kind, name))
                  bang_events =
                  [(SOME Markup.constantN,
                    SOME expected_backend)]);
              audit_assert
                (label ^ " bang constant styling changed")
                (count_markup Markup.constN bang_position markup = 1)
            end
          else assert_call_ast label notation ast
      in () end

    val _ =
      audit_registered_call 6 "registered macro"
        "MacroModule::invoke!(true)"
        "MacroModule::invoke!" "MacroModule" "invoke"
        \<^const_name>\<open>qualifier_macro_call\<close>

    val anonymous_macro_text =
      "MacroModule::anonymous!(true)"
    val (anonymous_macro_start, _, anonymous_macro_term,
         anonymous_macro_markup) =
      capture ctxt 13 "anonymous-registered-macro"
        anonymous_macro_text NONE
    val (_, anonymous_macro_qualifier) =
      token_position anonymous_macro_text anonymous_macro_start
        "MacroModule" 0
    val (_, anonymous_macro_terminal) =
      token_position anonymous_macro_text anonymous_macro_start
        "anonymous" (size "MacroModule::")
    val (_, anonymous_macro_bang) =
      token_position anonymous_macro_text anonymous_macro_start "!" 0
    val anonymous_macro_entry =
      only_entry ctxt Micro_Rust_Names.NFunction
        "MacroModule::anonymous!"
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NFunction
            "MacroModule::anonymous!"
            anonymous_macro_entry position
            anonymous_macro_markup)
        [("anonymous macro qualifier", anonymous_macro_qualifier),
         ("anonymous macro terminal", anonymous_macro_terminal)]
    val _ =
      audit_assert "anonymous macro bang acquired notation navigation"
        (notation_ref_order "MacroModule::anonymous!"
          anonymous_macro_bang anonymous_macro_markup = [])
    val _ =
      audit_assert "anonymous macro bang acquired a false backend target"
        (entity_events anonymous_macro_bang anonymous_macro_markup = [])
    val _ =
      audit_assert "anonymous macro bang acquired constant styling"
        (count_markup Markup.constN
          anonymous_macro_bang anonymous_macro_markup = 0)
    val _ =
      audit_assert "anonymous macro checked term changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close>
          anonymous_macro_term = 1)
    val _ =
      audit_registered_call 7 "exact turbofish"
        "GenericExact::<Token>::invoke()"
        "GenericExact::<Token>::invoke"
        "GenericExact" "invoke"
        \<^const_name>\<open>constructor_qualifier_call\<close>
    val _ =
      audit_registered_call 8 "lifted named function"
        "LiftedNavigation::named(\<llangle>4 :: nat\<rrangle>)"
        "LiftedNavigation::named"
        "LiftedNavigation" "named"
        \<^const_name>\<open>lift_fun1\<close>

    val lifted_lambda_text =
      "LiftedNavigation::anonymous(\<llangle>5 :: nat\<rrangle>)"
    val (lifted_lambda_start, lifted_lambda_ast,
         lifted_lambda_term, lifted_lambda_markup) =
      capture ctxt 9 "lifted-lambda" lifted_lambda_text NONE
    val (_, lifted_lambda_qualifier) =
      token_position lifted_lambda_text lifted_lambda_start
        "LiftedNavigation" 0
    val (_, lifted_lambda_terminal) =
      token_position lifted_lambda_text lifted_lambda_start
        "anonymous" (size "LiftedNavigation::")
    val lifted_lambda_entry =
      only_entry ctxt Micro_Rust_Names.NFunction
        "LiftedNavigation::anonymous"
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NFunction
            "LiftedNavigation::anonymous"
            lifted_lambda_entry position lifted_lambda_markup)
        [("lifted lambda qualifier", lifted_lambda_qualifier),
         ("lifted lambda terminal", lifted_lambda_terminal)]
    val _ =
      audit_assert "lifted lambda gained a false backend entity"
        (count_entity_kind Markup.constantN
           lifted_lambda_terminal lifted_lambda_markup = 0)
    val _ =
      audit_assert "lifted lambda lost terminal styling"
        (count_markup Markup.keyword3N
           lifted_lambda_terminal lifted_lambda_markup = 1)
    val _ =
      assert_call_ast "lifted lambda"
        "LiftedNavigation::anonymous" lifted_lambda_ast
    val _ =
      audit_assert "lifted lambda checked term changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close>
           lifted_lambda_term = 1)

    val some_value_text = "Some(\<llangle>1 :: nat\<rrangle>)"
    val (some_value_start, _, _, some_value_markup) =
      capture ctxt 10 "some-value" some_value_text NONE
    val (_, some_value_position) =
      token_position some_value_text some_value_start "Some" 0
    val some_entry =
      only_entry ctxt Micro_Rust_Names.NFunction "Some"
    val _ =
      assert_selected_token ctxt "Some value"
        Micro_Rust_Names.NFunction "Some" some_entry
        some_value_position some_value_markup
    val _ =
      audit_assert "Some value lost constructor hover"
        (count_entity_kind Markup.constantN
           some_value_position some_value_markup = 1)

    val native_pattern_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { " ^
      "Some(value) \<Rightarrow> value, None \<Rightarrow> 0 }"
    val (native_pattern_start, _, _, native_pattern_markup) =
      capture ctxt 11 "native-pattern" native_pattern_text NONE
    val (native_pattern_raw, _) =
      token_position native_pattern_text native_pattern_start
        "Some" (size "match_case \<llangle>Some (1 :: nat)\<rrangle> { ")
    val (_, native_pattern_position) =
      token_position native_pattern_text native_pattern_start
        "Some" native_pattern_raw
    val _ =
      audit_assert "native Some pattern acquired notation navigation"
        (notation_ref_order "Some"
          native_pattern_position native_pattern_markup = [])
    val _ =
      audit_assert "native Some pattern lost constructor navigation"
        (count_entity_kind Markup.constantN
           native_pattern_position native_pattern_markup = 1)

    val synthetic_name = "Synthetic::Variant"
    val synthetic_constructor =
      \<^term>\<open>ConstructorQualifierVariant\<close>
    val low_serial = serial ()
    val high_serial = serial ()
    val low_entry : Micro_Rust_Names.entry =
      {hol_term = synthetic_constructor,
       source_const = SOME synthetic_constructor,
       reg_pos =
         Position.make0 390 93000 0 "" ""
           "synthetic-notation-low-declaration",
       serial = low_serial}
    val high_entry : Micro_Rust_Names.entry =
      {hol_term = synthetic_constructor,
       source_const = SOME synthetic_constructor,
       reg_pos =
         Position.make0 391 93100 0 "" ""
           "synthetic-notation-high-declaration",
       serial = high_serial}
    val synthetic_ctxt =
      Context.Proof ctxt
      |> Micro_Rust_Names.Data.map
          (Symtab.update
            (Micro_Rust_Names.mk_key
              Micro_Rust_Names.NLiteral synthetic_name,
             [low_entry, high_entry]))
      |> Context.proof_of
    val synthetic_text =
      "match_case \<llangle>ConstructorQualifierVariant\<rrangle> { " ^
      synthetic_name ^ " \<Rightarrow> (), _ \<Rightarrow> () }"
    val (synthetic_start, _, _, synthetic_markup) =
      capture synthetic_ctxt 12 "same-constructor" synthetic_text NONE
    val (synthetic_path_raw, _) =
      token_position synthetic_text synthetic_start synthetic_name 0
    val (_, synthetic_qualifier) =
      token_position synthetic_text synthetic_start "Synthetic"
        synthetic_path_raw
    val (_, synthetic_terminal) =
      token_position synthetic_text synthetic_start "Variant"
        (synthetic_path_raw + size "Synthetic::")
    val _ =
      audit_assert "synthetic serial order precondition changed"
        (low_serial < high_serial)
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token synthetic_ctxt label
            Micro_Rust_Names.NLiteral synthetic_name low_entry
            position synthetic_markup)
        [("same-constructor qualifier", synthetic_qualifier),
         ("same-constructor terminal", synthetic_terminal)]
    val _ =
      audit_assert "same-constructor references were not both preserved"
        (notation_ref_order synthetic_name synthetic_terminal
           synthetic_markup =
          [Value.print_int high_serial, Value.print_int low_serial])
  in
    val _ =
      writeln
        "Selected notation declarations are final on registered literal, call, field, constructor, macro, turbofish, lifted, and overloaded tokens while backend/type hover, native fallback, ASTs, terms, multiplicity, and deterministic constructor priority remain intact"
  end
\<close>


section\<open> Deferred semantic target navigation audit \<close>

ML_val\<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("deferred semantic target navigation audit: " ^ message)

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

    val source_text = "panic!()"
    val source_start =
      Position.make0 410 97000 0 "" ""
        "deferred-semantic-target-navigation-audit"
    val panic_position =
      token_position source_text source_start "panic" 0
    val bang_position =
      token_position source_text source_start "!" 0
    val source =
      Parser_Lex_Util.positioned_content_source
        source_text source_start

    val ((_, reports), during_markup) =
      capture_markup "capture" (fn () =>
        Navigation.capture (fn () =>
          (Navigation.defer_report ctxt bang_position Markup.keyword3;
           Parser_Test_Elaboration.expression ctxt source)))

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
              (ignore
                (Parser_Test_Elaboration.expression ctxt source);
               error "intentional semantic navigation failure")))
          ())
    val _ =
      (case failure_result of
         Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ()
       | Exn.Res _ =>
           error
             ("deferred semantic target navigation audit: " ^
              "intentional failure unexpectedly succeeded"))
    val _ =
      audit_assert "failed capture leaked semantic targets"
        (constant_targets panic_position failure_markup = [] andalso
         count_markup Markup.constN panic_position failure_markup = 0)
  in
    val _ =
      writeln
        "Deferred semantic navigation target order, exact ranges, stable deduplication, native entity/style markup, generic replay, and failure isolation passed"
  end
\<close>


chapter\<open>Turbofish\<close>

declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]

section\<open> Additive payload fixtures \<close>

definition generic_dimension_call ::
  \<open>nat \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_dimension_call _ \<equiv> cf0 \<close>

definition GENERIC_LIMIT_A :: nat where
  \<open> GENERIC_LIMIT_A = 11 \<close>

definition GENERIC_LIMIT_B :: nat where
  \<open> GENERIC_LIMIT_B = 13 \<close>

urust_expr generic_payload_01 \<open> generic_dimension_call::<1>() \<close>
urust_expr generic_payload_02 \<open> generic_dimension_call::<GENERIC_LIMIT_A>() \<close>
urust_expr generic_payload_03 \<open> generic_dimension_call::<1 + GENERIC_LIMIT_A>() \<close>
urust_expr generic_payload_04
  \<open> generic_dimension_call::<GENERIC_LIMIT_A + 3 + GENERIC_LIMIT_B>() \<close>

section\<open> Exact canonical names \<close>

urust_notation (call) cf0 ("GenericFactory::<TypeA>::make")
urust_notation (call) cf0 ("GenericContainer::<2>::make")

urust_expr generic_exact_type_a \<open> GenericFactory::<TypeA>::make() \<close>
urust_expr generic_exact_container_2 \<open> GenericContainer::<2>::make() \<close>

definition exact_fallback ::
  \<open>int \<Rightarrow> int \<Rightarrow>
    (unit, int, unit, unit, unit) function_body\<close>
  where \<open> exact_fallback parameter \<equiv>
      lift_fun1 (\<lambda>argument. parameter + argument) \<close>

micro_rust_notation (call) exact_fallback ("Exact::f")
urust_notation (call) cf0 ("Exact::f::<N>")

urust_expr exact_generic_wins \<open> Exact::f::<N>() \<close>
urust_expr exact_generic_fallback \<open> Exact::f::<1>(2) \<close>

section\<open> Structural and semantic audit \<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("restricted turbofish audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "restricted turbofish audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun generic_arguments text =
      (case parse text of
         UE_Call (UC_Path path, [], _) =>
           (case path_segments path of
              [Path_Segment
                ("f", _, SOME (Generic_Args (arguments, _)))] =>
                  arguments
            | _ =>
                error
                  ("restricted turbofish audit: path shape changed for " ^
                    quote text))
       | _ =>
           error ("restricted turbofish audit: call shape changed for " ^
             quote text))

    fun one_generic text =
      (case generic_arguments text of
         [Generic_Arg (canonical, source)] => (canonical, source)
       | _ =>
           error ("restricted turbofish audit: expected one argument for " ^
             quote text))

    val canonical_cases =
      [("f::<a + b + c>()", "a+b+c"),
       ("f::<(a + b) + c>()", "(a+b)+c"),
       ("f::<Module::Value>()", "Module::Value"),
       ("f::<42>()", "42"),
       ("f::<0x2a>()", "0x2a")]
    val _ =
      List.app
        (fn (source, expected) =>
          audit_assert ("canonical fragment changed for " ^ quote source)
            (#1 (one_generic source) = expected))
        canonical_cases

    val spaced_text = "f::\n <  a +\n b + c  ,  (d) >()"
    val spaced_start =
      Position.make0 11 40 400 "" "" "restricted-turbofish-source-audit"
    val spaced =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          spaced_text spaced_start)
    val _ =
      (case spaced of
         UE_Call (UC_Path path, [], _) =>
           (case path_segments path of
              [Path_Segment
                ("f", _,
                 SOME (Generic_Args
                   ([Generic_Arg (first_canonical, first_source),
                     Generic_Arg (second_canonical, second_source)],
                    generic_pos)))] =>
           let
             val expected_generic_start =
               Position.symbol_explode "f" spaced_start
             val first_start =
               Position.symbol_explode "f::\n <  " spaced_start
             val first_stop =
               Position.symbol_explode "f::\n <  a +\n b + c" spaced_start
             val second_start =
               Position.symbol_explode "f::\n <  a +\n b + c  ,  " spaced_start
             val second_stop =
               Position.symbol_explode "f::\n <  a +\n b + c  ,  (d)" spaced_start
           in
             audit_assert "canonical rendering retained trivia"
               (first_canonical = "a+b+c" andalso
                second_canonical = "(d)");
             audit_assert "first original source slice changed"
               (Input.string_of first_source = "a +\n b + c" andalso
                Position.offset_of (#1 (Input.range_of first_source)) =
                  Position.offset_of first_start andalso
                Position.offset_of (#2 (Input.range_of first_source)) =
                  Position.offset_of first_stop);
             audit_assert "second original source slice changed"
               (Input.string_of second_source = "(d)" andalso
                Position.offset_of (#1 (Input.range_of second_source)) =
                  Position.offset_of second_start andalso
                Position.offset_of (#2 (Input.range_of second_source)) =
                  Position.offset_of second_stop);
             audit_assert "generic span did not start at the path separator"
               (Position.offset_of generic_pos =
                  Position.offset_of expected_generic_start)
           end
            | _ =>
                error
                  "restricted turbofish audit: multiline path shape changed")
       | _ => error "restricted turbofish audit: multiline call shape changed")

    fun checked_generic_argument source =
      let
        val checked =
          Syntax.check_term ctxt
            (URust_Translate.mk_expression ctxt [] (parse source))
        val function =
          (case Term.strip_comb checked of
             (_, function :: _) => function
           | _ => error "restricted turbofish audit: checked call shape changed")
      in
        (case Term.strip_comb
            (Term_Position.strip_positions function) of
           (_, [argument]) => Term_Position.strip_positions argument
         | _ =>
             error "restricted turbofish audit: generic application shape changed")
      end

    fun check_semantic source expected =
      let
        val actual = checked_generic_argument source
        val wanted =
          Syntax.read_term ctxt expected
          |> Term_Position.strip_positions
      in
        audit_assert ("checked HOL shape changed for " ^ quote source)
          (actual aconv wanted)
      end

    val _ =
      List.app (fn (source, expected) => check_semantic source expected)
        [("turbofish_int_one::<1 + 2 + 3>(0)", "(1 + 2 + 3 :: int)"),
         ("turbofish_int_one::<(1 + 2) + 3>(0)", "((1 + 2) + 3 :: int)")]

    val exact_term =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "Exact::f::<N>()")
    val fallback_term =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "Exact::f::<1>(2)")
    val _ =
      audit_assert "complete exact registration did not win"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>cf0\<close>
            | _ => false)
          exact_term)
    val _ =
      audit_assert "final exact miss did not use semantic fallback"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>exact_fallback\<close>
            | _ => false)
          fallback_term)

    fun expect_rejection text expected =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error ("restricted turbofish audit: unexpectedly accepted " ^
             quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (Runtime.exn_message exn)))

    val _ =
      expect_rejection "GenericFactory::<Missing>::make()"
        "generic arguments on an intermediate path segment require an exact registration"
    val malformed =
      [("f::<>()", "syntax error"),
       ("f::<,1>()", "syntax error"),
       ("f::<1,,2>()", "syntax error"),
       ("f::<1,>()", "syntax error"),
       ("f::<1 a>()", "syntax error"),
       ("f::<1 +>()", "syntax error"),
       ("f::<-1>()", "unexpected input"),
       ("f::<1 - 2>()", "unexpected input"),
       ("f::<1 * 2>()", "unexpected input"),
       ("f::<1 / 2>()", "unexpected input"),
       ("f::<((1)>()", "syntax error"),
       ("f::<1)>()", "syntax error"),
       ("f::<1(", "unterminated turbofish"),
       ("f::<1>>()",
        "generic arguments on a bare value require an exact literal registration"),
       ("f::<1u8>()", "syntax error"),
       ("f::<Suc 4>()", "syntax error"),
       ("f::<a div b>()", "syntax error"),
       ("f::<a mod b>()", "syntax error"),
       ("f::<(1, 2)>()", "syntax error"),
       ("f::<[1, 2]>()", "unexpected input"),
       ("f::<\"text\">()", "unexpected input"),
       ("f::<STR ''text''>()", "unexpected input"),
       ("f::<1 :: nat>()", "syntax error"),
       ("f::<a < b>()", "unexpected input"),
       ("f::<a << b>()", "unexpected input"),
       ("f::<a & b>()", "unexpected input"),
       ("f::<a && b>()", "unexpected input"),
       ("f::<a % b>()", "unexpected input"),
       ("f::<a ^ b>()", "unexpected input"),
       ("f::<\<clubsuit>>()", "unexpected input"),
       ("f::<" ^ Symbol.open_ ^ "opaque" ^ Symbol.close ^ ">()",
        "unexpected input"),
       ("f::<\<epsilon>\<open>1\<close>>()", "unexpected input"),
       ("f::<1 // comment\n + 2>()", "unexpected input")]
    val _ =
      List.app
        (fn (source, expected) =>
          (expect_rejection source expected;
           case parse "cf0()" of
             UE_Call (UC_Path path, [], _) =>
               audit_assert "lexer state leaked after malformed generic input"
                 (render_path path = "cf0")
           | _ => error "restricted turbofish audit: recovery parse changed"))
        malformed
  in
    val _ = writeln "Restricted turbofish AST, semantics, lookup, and recovery passed"
  end
\<close>

section\<open> Markup and diagnostics \<close>

definition generic_markup_value :: int where
  \<open> generic_markup_value = 8 \<close>

definition generic_markup_call ::
  \<open>nat \<Rightarrow> int \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_markup_call _ _ \<equiv> cf1 \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("restricted turbofish markup audit: " ^ message)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_reports action =
      let
        val captured = Synchronized.var "parser_test_reports" ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
      in (result, markup) end

    fun source_position start prefix text =
      let
        val token_start = Position.symbol_explode prefix start
        val token_stop = Position.symbol_explode text token_start
      in Position.range_position (Position.range (token_start, token_stop)) end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup

    val text = "generic_markup_call::\n <(1+2), generic_markup_value+2+1>(0)"
    val start =
      Position.make0 31 80 800 "" "" "restricted-turbofish-markup"
    val (_, markup) =
      capture_reports
        (fn () =>
          ignore
            (Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.positioned_content_source text start)))
    val delimiters =
      [source_position start "generic_markup_call" "::",
       source_position start "generic_markup_call::\n " "<",
       source_position start "generic_markup_call::\n <" "(",
       source_position start "generic_markup_call::\n <(1+2" ")",
       source_position start "generic_markup_call::\n <(1+2)" ",",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2+1" ">"]
    val operators =
      [source_position start "generic_markup_call::\n <(1" "+",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value" "+",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2" "+"]
    val numerals =
      [source_position start "generic_markup_call::\n <(" "1",
       source_position start "generic_markup_call::\n <(1+" "2",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+" "2",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2+" "1"]
    val _ =
      List.app
        (fn position =>
          audit_assert "generic delimiter markup moved"
            (has_markup markup Markup.delimiterN position))
        delimiters
    val _ =
      List.app
        (fn position =>
          audit_assert "generic operator markup moved"
            (has_markup markup Markup.operatorN position))
        operators
    val _ =
      List.app
        (fn position =>
          audit_assert "generic numeral markup moved"
            (has_markup markup Markup.numeralN position))
        numerals

    val operator_text = "f::<1+2+3>()"
    val operator_start =
      Position.make0 37 100 1000 "" "" "restricted-turbofish-all-operators"
    val (_, operator_markup) =
      capture_reports
        (fn () =>
          ignore
            (URust_Parser.parse_source ctxt
              (Parser_Lex_Util.positioned_content_source
                operator_text operator_start)))
    val all_operators =
      [source_position operator_start "f::<1" "+",
       source_position operator_start "f::<1+2" "+"]
    val _ =
      List.app
        (fn position =>
          audit_assert "arithmetic operator markup moved"
            (has_markup operator_markup Markup.operatorN position))
        all_operators

    val malformed_text = "// \<clubsuit>\nf::<1 + %>()"
    val malformed_start =
      Position.make0 41 120 1200 "" "" "restricted-turbofish-symbol-offset"
    val expected_position =
      Position.symbol_explode "// \<clubsuit>\nf::<1 + " malformed_start
    val message =
      (case Exn.result
          (fn () =>
            URust_Parser.parse_source ctxt
              (Parser_Lex_Util.positioned_content_source
                malformed_text malformed_start)) () of
         Exn.Res _ => error "restricted turbofish markup audit: malformed input accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)
    val plain = XML.content_of (YXML.parse_body message)
    val message_markup =
      fold collect_markup (YXML.parse_body message) []
    val _ =
      audit_assert "smallest offending generic token changed"
        (String.isSubstring "unexpected input \"%\"" plain)
    val _ =
      audit_assert "Isabelle-symbol-counted diagnostic offset changed"
        (exists
          (fn (_, properties) =>
            Properties.get properties Markup.offsetN =
              Option.map Value.print_int
                (Position.offset_of expected_position))
          message_markup)
  in
    val _ = writeln "Restricted turbofish markup and diagnostics passed"
  end
\<close>

definition generic_navigation_call ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_navigation_call _ _ \<equiv> cf1 \<close>

context
  fixes generic_free :: nat
begin

ML_val\<open>
  local
    val ctxt = \<^context>
    val text =
      "let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
      "generic_navigation_call::<generic_free, generic_bound>(0)"
    val start =
      Position.make0 47 140 1400 "" "" "restricted-turbofish-identifier-markup"
    val captured = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture chunks =
      Synchronized.change captured (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source text start))) ()) ())
    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured)) []
    fun token_position prefix token =
      let
        val token_start = Position.symbol_explode prefix start
        val token_stop = Position.symbol_explode token token_start
      in Position.range_position (Position.range (token_start, token_stop)) end
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup
    val free_position =
      token_position
        ("let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
          "generic_navigation_call::<")
        "generic_free"
    val bound_position =
      token_position
        ("let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
          "generic_navigation_call::<generic_free, ")
        "generic_bound"
    val _ =
      if has_markup Markup.freeN free_position then ()
      else error "restricted turbofish markup audit: context fix lost free markup"
    val _ =
      if has_markup Markup.boundN bound_position then ()
      else error "restricted turbofish markup audit: generic binder lost bound markup"
  in end
\<close>

end

section\<open> Canonical exact-key regressions \<close>

urust_notation (call) cf0 ("AuditSpaced::<a + b>::new")
urust_notation cf0 ("AuditAuto::<a + b>::new")
urust_notation (call) cf0 ("AuditIdentifier::<div>::new")
urust_notation (call) cf0 ("AuditIdentifier::<mod>::new")
urust_notation (call) macro_shout ("AuditMacro::<a + b>::shout!")
urust_notation (config) [shadow_no_warn] "AuditConfig::<a + b>::new"

urust_expr audit_spaced_compact \<open> AuditSpaced::<a+b>::new() \<close>
urust_expr audit_spaced_spaced \<open> AuditSpaced::<a + b>::new() \<close>
urust_expr audit_spaced_multiline
  \<open>
    AuditSpaced::<
      a +
      b
    >::new()
  \<close>
urust_expr audit_auto \<open> AuditAuto::<a+b>::new() \<close>
urust_expr audit_div_identifier \<open> AuditIdentifier::<div>::new() \<close>
urust_expr audit_mod_identifier \<open> AuditIdentifier::<mod>::new() \<close>
urust_expr audit_macro \<open> AuditMacro::<a+b>::shout!(true) \<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun parse_path text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME (UE_Call (UC_Path path, [], _)) => path
       | _ => error ("canonical exact-key regression: unexpected AST for " ^ quote text))

    val identifier = render_path (parse_path "f::<adivb>()")
    val _ =
      if identifier = "f::<adivb>" then ()
      else error "canonical exact-key regression: identifier rendering changed"
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source
                "f::<a div b>()")) () of
         Exn.Res _ =>
           error "canonical exact-key regression: a div b was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else ())
    val {suppress_warning, ...} =
      Micro_Rust_Names.shadow_opts ctxt Micro_Rust_Names.NFunction
        "AuditConfig::<a+b>::new"
    val _ =
      if suppress_warning then ()
      else error "urust_notation configuration did not canonicalize its name"
  in end
\<close>


section\<open>Shared iterator zip registration audit\<close>

ML\<open>
local
  fun assert message condition =
    if condition then () else error message

  fun theorem_term name =
    Thm.prop_of (Proof_Context.get_thm \<^context> name)

  fun contains_const name =
    Term.exists_subterm
      (fn Const (actual, _) => actual = name | _ => false)

  val iterator_zip_name = \<^const_name>\<open>iterator_zip\<close>
  val hol_zip_name = \<^const_name>\<open>List.zip\<close>
  val funcall1_name = \<^const_name>\<open>funcall1\<close>
  val funcall2_name = \<^const_name>\<open>funcall2\<close>

  val direct_terms =
    map theorem_term
      ["iterator_zip_expr_direct_def", "iterator_zip_direct_def"]
  val method_terms =
    map theorem_term
      ["iterator_zip_expr_method_def", "iterator_zip_method_def"]
  val chained_terms =
    map theorem_term
      ["iterator_zip_expr_chained_def", "iterator_zip_chained_def"]

  val _ =
    List.app
      (fn term =>
        assert "direct zip did not resolve through iterator_zip notation"
          (contains_const iterator_zip_name term))
      direct_terms
  val _ =
    List.app
      (fn term =>
        (assert "method zip did not resolve through iterator_zip notation"
           (contains_const iterator_zip_name term);
         assert "method zip did not use receiver-prepended binary arity"
           (contains_const funcall2_name term);
         assert "pure HOL List.zip leaked into method uRust lowering"
           (not (contains_const hol_zip_name term))))
      method_terms
  val _ =
    List.app
      (fn term =>
        (assert "chained zip did not resolve through iterator_zip notation"
           (contains_const iterator_zip_name term);
         assert "chained zip lost ordinary into_iter lowering"
           (contains_const funcall1_name term);
         assert "chained zip did not use receiver-prepended binary arity"
           (contains_const funcall2_name term)))
      chained_terms

  val registrations =
    Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NFunction "zip"
  val _ =
    assert "zip notation is not registered to iterator_zip"
      (exists
        (fn {hol_term, ...} => contains_const iterator_zip_name hol_term)
        registrations)
in
end
\<close>



chapter\<open>Scoped cast-target aliases\<close>

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open>Imported bundles remain inactive\<close>

ML_val\<open>
  local
    fun plain_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))
        handle Fail _ => Runtime.exn_message exn

    fun expect_rejection ctxt text expected =
      (case
          Exn.result
            (Parser_Test_Elaboration.expression ctxt)
            (Parser_Lex_Util.text_source text) of
         Exn.Res term =>
           error
             ("cast-target alias unexpectedly active for " ^ quote text ^
               ": " ^ Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = plain_message exn in
               if String.isSubstring expected message then ()
               else
                 error
                   ("wrong cast-target alias diagnostic:\n" ^ message ^
                     "\nexpected: " ^ quote expected)
             end)
  in
    val _ =
      expect_rejection \<^context> "0_u64 as U8Alias"
        "unknown cast-target alias"
  end
\<close>

section\<open>Primitive equivalence and grammar composition\<close>

context includes module_cast_aliases
begin

context
  fixes cast_alias_word :: "64 word"
begin

urust_expr cast_alias_u8
  \<open> cast_alias_word as U8Alias \<close>

urust_expr cast_alias_u16
  \<open> cast_alias_word as types::U16Alias \<close>

urust_expr cast_alias_u32
  \<open> cast_alias_word as U32Alias \<close>

urust_expr cast_alias_u64
  \<open> cast_alias_word as U64Alias \<close>

urust_expr cast_alias_usize
  \<open> cast_alias_word as UsizeAlias \<close>

urust_expr cast_alias_i32
  \<open> cast_alias_word as I32Alias \<close>

urust_expr cast_alias_i64
  \<open> cast_alias_word as I64Alias \<close>

urust_expr cast_alias_chain
  \<open> cast_alias_word as U64Alias as U8Alias as I32Alias \<close>

urust_expr cast_alias_precedence
  \<open> cast_alias_word as U32Alias + 1_u32 \<close>

urust_expr cast_alias_no_struct
  \<open>
    if cast_alias_word as U32Alias ==
        cast_alias_word as U32Alias {
      cast_alias_word as types::U16Alias
    } else {
      cast_alias_word as types::U16Alias
    }
  \<close>

end

context
  fixes cast_alias_raw :: "('address, 'global) gref"
begin

urust_expr cast_alias_const_u8_pointer
  \<open> cast_alias_raw as ConstU8Pointer \<close>

urust_expr cast_alias_const_u16_pointer
  \<open> cast_alias_raw as ConstU16Pointer \<close>

urust_expr cast_alias_const_u32_pointer
  \<open> cast_alias_raw as ConstU32Pointer \<close>

urust_expr cast_alias_const_u64_pointer
  \<open> cast_alias_raw as ConstU64Pointer \<close>

urust_expr cast_alias_const_usize_pointer
  \<open> cast_alias_raw as ConstUsizePointer \<close>

urust_expr cast_alias_mut_u8_pointer
  \<open> cast_alias_raw as MutU8Pointer \<close>

urust_expr cast_alias_mut_u16_pointer
  \<open> cast_alias_raw as MutU16Pointer \<close>

urust_expr cast_alias_mut_u32_pointer
  \<open> cast_alias_raw as MutU32Pointer \<close>

urust_expr cast_alias_mut_u64_pointer
  \<open> cast_alias_raw as MutU64Pointer \<close>

urust_expr cast_alias_mut_usize_pointer
  \<open> cast_alias_raw as MutUsizePointer \<close>

end

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun parse text =
      (case
          URust_Parser.parse_source ctxt
            (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "cast-target alias audit: empty parse")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    fun assert message condition =
      if condition then ()
      else error ("cast-target alias audit: " ^ message)
  in
    val _ =
      (case parse "value as types::U16Alias" of
         UE_Cast
           (UE_Path _,
            SCT_Named path, _) =>
           assert "named cast target lost its exact qualified path"
             (render_path path = "types::U16Alias")
       | _ =>
           error
             "cast-target alias audit: named cast AST shape changed")
    val _ =
      assert "unchecked integral alias changed the generated term"
        (Term.aconv
          (unchecked "value as U8Alias",
           unchecked "value as u8"))
    val _ =
      assert "unchecked qualified alias changed the generated term"
        (Term.aconv
          (unchecked "value as types::U16Alias",
           unchecked "value as u16"))
    val _ =
      assert "unchecked pointer alias changed the generated term"
        (Term.aconv
          (unchecked "value as MutUsizePointer",
           unchecked "value as *mut usize"))
    val _ =
      assert "unchecked alias chain changed the generated term"
        (Term.aconv
          (unchecked "value as U64Alias as U8Alias as I32Alias",
           unchecked "value as u64 as u8 as i32"))
  end
\<close>

ML_val\<open>
  local
    fun plain_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))
        handle Fail _ => Runtime.exn_message exn

    fun expect_failure label action expected =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("cast-target alias " ^ label ^
               " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = plain_message exn in
               if String.isSubstring expected message then ()
               else
                 error
                   ("cast-target alias " ^ label ^
                     " produced the wrong diagnostic:\n" ^ message)
             end)

    val _ =
      expect_failure "generic use"
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source
              "0_u64 as U8Alias::<Width>"))
        "generic arguments are not allowed in cast-target aliases"
  in
    val _ = ()
  end
\<close>

end

section\<open>Confined direct and locale activation\<close>

experiment
begin

urust_cast_alias "ExperimentWidth" = "u32"

urust_expr cast_alias_direct_activation
  \<open> 0_u64 as ExperimentWidth \<close>

end

context cast_alias_scope opening module_cast_aliases
begin

urust_expr cast_alias_locale_use
  \<open> scope_word as types::U16Alias \<close>

end

context cast_alias_scope
begin

ML_val\<open>
  local
    val result =
      Exn.result
        (Parser_Test_Elaboration.expression \<^context>)
        (Parser_Lex_Util.text_source
          "scope_word as types::U16Alias")
  in
    val _ =
      (case result of
         Exn.Res term =>
           error
             ("cast-target alias permanently modified its locale: " ^
               Syntax.string_of_term \<^context> term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             if String.isSubstring "unknown cast-target alias"
                 (Runtime.exn_message exn)
             then ()
             else Exn.reraise exn)
  end
\<close>

end

ML_val\<open>
  local
    fun rejected text =
      (case
          Exn.result
            (Parser_Test_Elaboration.expression \<^context>)
            (Parser_Lex_Util.text_source text) of
         Exn.Res _ => false
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             String.isSubstring "unknown cast-target alias"
               (Runtime.exn_message exn))
  in
    val _ =
      if rejected "0_u64 as U8Alias" andalso
         rejected "0_u64 as ExperimentWidth"
      then ()
      else
        error
          "cast-target alias remained active after its confined context"
  end
\<close>

section\<open>Conflicts and idempotence\<close>

context includes conflict_u8_aliases
begin

urust_expr cast_alias_conflict_left_alone
  \<open> 0_u64 as SharedWidth \<close>

end

context includes conflict_u16_aliases
begin

urust_expr cast_alias_conflict_right_alone
  \<open> 0_u64 as SharedWidth \<close>

end

context includes idempotent_cast_aliases
begin

urust_expr cast_alias_idempotent_registration
  \<open> 0_u64 as StableWidth \<close>

end

ML_val\<open>
  local
    fun include_bundle ctxt name =
      Bundle.includes
        [(true, Bundle.check ctxt (name, Position.none))]
        ctxt

    fun collect_markup (XML.Text _) result = result
      | collect_markup
          (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    val conflict =
      Exn.result
        (fn () =>
          include_bundle
            (include_bundle \<^context> "conflict_u8_aliases")
            "conflict_u16_aliases")
        ()

    val _ =
      (case conflict of
         Exn.Res _ =>
           error "conflicting cast-target alias bundles were accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val raw_message = Runtime.exn_message exn
               val message =
                 XML.content_of (YXML.parse_body raw_message)
                   handle Fail _ => raw_message
               val positions =
                 maps YXML.parse_body [raw_message]
                 |> (fn trees => fold collect_markup trees [])
                 |> map_filter
                     (fn (name, properties) =>
                       if name = Markup.positionN
                       then SOME properties
                       else NONE)
                 |> distinct (op =)
             in
               if String.isSubstring
                    "conflicting active definitions for \"SharedWidth\""
                    message andalso
                  String.isSubstring "\"u8\"" message andalso
                  String.isSubstring "\"u16\"" message andalso
                  length positions = 2
               then ()
               else
                 error
                   ("conflicting cast-target alias diagnostic did not " ^
                     "report both declarations:\n" ^ message)
             end)

    val repeated_context =
      include_bundle
        (include_bundle \<^context> "idempotent_cast_aliases")
        "idempotent_cast_aliases"
    val _ =
      ignore
        (Parser_Test_Elaboration.expression repeated_context
          (Parser_Lex_Util.text_source
            "0_u64 as StableWidth"))
  in
    val _ = ()
  end
\<close>

section\<open>Declaration and use diagnostics\<close>

ML_val\<open>
  local
    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun assert_rejected source_name command_text expected =
      (case
          Exn.result
            (run_command source_name command_text) () of
         Exn.Res _ =>
           error
             ("invalid cast-target alias declaration was accepted" ^
               Position.here (Position.file source_name))
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               if String.isSubstring expected message andalso
                  String.isSubstring source_name message
               then ()
               else
                 error
                   ("wrong cast-target alias declaration diagnostic:\n" ^
                     message)
             end)

    val _ =
      assert_rejected "cast-alias-chain"
        "urust_cast_alias \"AliasChain\" = \"U8Alias\""
        "malformed primitive cast target"
    val _ =
      assert_rejected "cast-alias-malformed-target"
        "urust_cast_alias \"BrokenPointer\" = \"*const\""
        "malformed primitive cast target"
    val _ =
      assert_rejected "cast-alias-generic-name"
        "urust_cast_alias \"Types::Alias::<Width>\" = \"u16\""
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-empty-segment"
        "urust_cast_alias \"Types::\" = \"u16\""
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-reserved-segment"
        "urust_cast_alias \"Types::u16\" = \"u16\""
        "reserved segment"
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    val base_ctxt = \<^context>
    val ctxt =
      Bundle.includes
        [(true,
          Bundle.check base_ctxt
            ("module_cast_aliases", Position.none))]
        base_ctxt
    val text =
      "value as U8Alias; value as U8Alias; " ^
      "value as types::U16Alias"
    val start =
      Position.make0 17 4 0 "" ""
        "cast-target-alias-markup"
    val reports =
      Synchronized.var "cast_target_alias_reports" ([]: string list)

    fun capture chunks =
      Synchronized.change reports (append chunks)

    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                let
                  val source =
                    Parser_Lex_Util.positioned_content_source
                      text start
                  val expression =
                    (case URust_Parser.parse_source ctxt source of
                       SOME parsed => parsed
                     | NONE =>
                         error
                           "cast-target alias markup audit: empty parse")
                in
                  ignore
                    (URust_Translate.mk_expression ctxt [] expression)
                end)
              ())
          ())

    fun collect (XML.Text _) result = result
      | collect (XML.Elem (markup, body)) result =
          fold collect body (markup :: result)

    val markup =
      fold collect
        (maps YXML.parse_body (Synchronized.value reports)) []

    fun alias_references alias =
      map_filter
        (fn (name, properties) =>
          if name = Markup.entityN andalso
             Properties.get properties Markup.kindN =
               SOME "micro_rust_cast_alias" andalso
             Properties.get properties Markup.nameN = SOME alias
          then Properties.get properties Markup.refN
          else NONE)
        markup

    fun count_markup name =
      length (filter (fn (actual, _) => actual = name) markup)

    val u8_references = alias_references "U8Alias"
    val qualified_references =
      alias_references "types::U16Alias"
    val _ =
      if length u8_references = 2 andalso
         length (distinct (op =) u8_references) = 1
      then ()
      else
        error
          "cast-target alias uses did not retain one stable declaration identity"
    val _ =
      if length qualified_references = 1 then ()
      else
        error
          "qualified cast-target alias lost its declaration reference"
    val _ =
      if count_markup Markup.keyword3N >= 4 andalso
         count_markup Markup.typingN >= 4
      then ()
      else
        error
          "cast-target alias segments lost semantic or typing markup"
  in
    val _ =
      writeln
        "Scoped cast-target alias term, scope, diagnostic, and markup regressions passed"
  end
\<close>



section\<open>Primitive-type path heads\<close>

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]

definition primitive_head_u8_max :: \<open>8 word\<close>
  where \<open>primitive_head_u8_max = 7\<close>

definition primitive_head_u16_max :: \<open>16 word\<close>
  where \<open>primitive_head_u16_max = 17\<close>

definition primitive_head_u32_max :: \<open>32 word\<close>
  where \<open>primitive_head_u32_max = 37\<close>

definition primitive_head_u64_max :: \<open>64 word\<close>
  where \<open>primitive_head_u64_max = 67\<close>

definition primitive_head_usize_max :: \<open>64 word\<close>
  where \<open>primitive_head_usize_max = 3\<close>

definition primitive_head_i32_max :: \<open>32 word\<close>
  where \<open>primitive_head_i32_max = 47\<close>

definition primitive_head_i64_max :: \<open>64 word\<close>
  where \<open>primitive_head_i64_max = 79\<close>

definition primitive_head_u64_min :: \<open>64 word\<close>
  where \<open>primitive_head_u64_min = 0\<close>

definition primitive_head_flag :: bool
  where \<open>primitive_head_flag = True\<close>

definition primitive_head_option :: \<open>64 word option\<close>
  where \<open>primitive_head_option = Some 11\<close>

definition primitive_head_values :: \<open>64 word list\<close>
  where \<open>primitive_head_values = [13, 17]\<close>

definition primitive_head_pair :: \<open>64 word \<times> 64 word\<close>
  where \<open>primitive_head_pair = (19, 23)\<close>

datatype_record primitive_head_record =
  primitive_head_record_value :: \<open>64 word\<close>
micro_rust_record primitive_head_record

definition primitive_head_record_constant :: primitive_head_record
  where \<open>primitive_head_record_constant = make_primitive_head_record 29\<close>

definition primitive_head_zero ::
    \<open>(unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open>primitive_head_zero = lift_fun0 0\<close>

definition primitive_head_from ::
    \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open>primitive_head_from = lift_fun1 id\<close>

definition primitive_head_combine ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open>primitive_head_combine = lift_fun2 (+)\<close>

definition primitive_head_bump ::
    \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open>primitive_head_bump = lift_fun1 (\<lambda>x. x + 1)\<close>

definition primitive_head_dual_literal :: \<open>64 word\<close>
  where \<open>primitive_head_dual_literal = 31\<close>

definition primitive_head_dual_call ::
    \<open>(unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open>primitive_head_dual_call = lift_fun0 31\<close>

definition primitive_head_ambiguous_left :: \<open>64 word\<close>
  where \<open>primitive_head_ambiguous_left = 41\<close>

definition primitive_head_ambiguous_right :: \<open>64 word\<close>
  where \<open>primitive_head_ambiguous_right = 43\<close>

datatype primitive_head_constructor_backend =
  PrimitiveHeadConstructor

micro_rust_notation (literal) primitive_head_u8_max ("u8::MAX")
micro_rust_notation (literal) primitive_head_u16_max ("u16::MAX")
micro_rust_notation (literal) primitive_head_u32_max ("u32::MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u64::MAX")
micro_rust_notation (literal) primitive_head_usize_max ("usize::MAX")
micro_rust_notation (literal) primitive_head_i32_max ("i32::MAX")
micro_rust_notation (literal) primitive_head_i64_max ("i64::MAX")
micro_rust_notation (literal) primitive_head_u64_min ("u64::MIN")
micro_rust_notation (literal) primitive_head_flag ("u64::FLAG")
micro_rust_notation (literal) primitive_head_option ("u64::OPTION")
micro_rust_notation (literal) primitive_head_values ("u64::VALUES")
micro_rust_notation (literal) primitive_head_pair ("u64::PAIR")
micro_rust_notation (literal)
  primitive_head_record_constant ("u64::RECORD")
urust_notation (literal)
  primitive_head_u64_max ("u64::Nested::MAX")

micro_rust_notation (call) primitive_head_zero ("u64::zero")
micro_rust_notation (call) primitive_head_from ("u64::from")
micro_rust_notation (call) primitive_head_combine ("u64::combine")
micro_rust_notation (call)
  primitive_head_from ("u64::from::<PrimitiveParam>")
micro_rust_notation (call) primitive_head_bump ("primitive_head_bump")

micro_rust_notation (literal)
  primitive_head_dual_literal ("u64::DUAL")
micro_rust_notation (call)
  primitive_head_dual_call ("u64::DUAL")

micro_rust_notation (literal)
  primitive_head_ambiguous_left ("u64::AMBIGUOUS")
micro_rust_notation (literal)
  primitive_head_ambiguous_right ("u64::AMBIGUOUS")

micro_rust_notation (literal)
  PrimitiveHeadConstructor ("u64::CONSTRUCTOR_VALUE")

micro_rust_notation (literal)
  primitive_head_u8_max ("PrimitiveCompat::U8Max")
micro_rust_notation (literal)
  primitive_head_u16_max ("PrimitiveCompat::U16Max")
micro_rust_notation (literal)
  primitive_head_u32_max ("PrimitiveCompat::U32Max")
micro_rust_notation (literal)
  primitive_head_u64_max ("PrimitiveCompat::U64Max")
micro_rust_notation (literal)
  primitive_head_usize_max ("PrimitiveCompat::UsizeMax")
micro_rust_notation (literal)
  primitive_head_i32_max ("PrimitiveCompat::I32Max")
micro_rust_notation (literal)
  primitive_head_i64_max ("PrimitiveCompat::I64Max")
micro_rust_notation (literal)
  primitive_head_u64_min ("PrimitiveCompat::U64Min")
micro_rust_notation (call)
  primitive_head_zero ("PrimitiveCompat::zero")
micro_rust_notation (call)
  primitive_head_from ("PrimitiveCompat::convert")
micro_rust_notation (call)
  primitive_head_combine ("PrimitiveCompat::combine")
micro_rust_notation (call)
  primitive_head_from ("PrimitiveCompat::convert::<PrimitiveParam>")
micro_rust_notation (literal)
  primitive_head_dual_literal ("PrimitiveCompat::DUAL")
micro_rust_notation (call)
  primitive_head_dual_call ("PrimitiveCompat::DUAL")

micro_rust_notation (literal) primitive_head_u64_max ("u64_MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u64x::MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u64x'::MAX")
micro_rust_notation (literal) primitive_head_u64_max ("u128::MAX")

bundle primitive_path_cast_aliases begin
  urust_cast_alias "PrimitivePathAlias" = "u64"
end

subsection\<open>Exact literal and call resolution\<close>

urust_expr primitive_path_u8 \<open> u8::MAX \<close>

urust_expr primitive_path_u16 \<open> u16::MAX \<close>

urust_expr primitive_path_u32 \<open> u32::MAX \<close>

urust_expr primitive_path_u64 \<open> u64::MAX \<close>

urust_expr primitive_path_usize \<open> usize::MAX \<close>

urust_expr primitive_path_i32 \<open> i32::MAX \<close>

urust_expr primitive_path_i64 \<open> i64::MAX \<close>

urust_expr primitive_path_call_zero \<open> u64::zero() \<close>

urust_expr primitive_path_call_one \<open> u64::from(5u64) \<close>

urust_expr primitive_path_call_multiple
  \<open> u64::combine(5u64, 7u64) \<close>

urust_expr primitive_path_call_turbofish
  \<open> u64::from::<PrimitiveParam>(5u64) \<close>

urust_expr primitive_path_dual_literal \<open> u64::DUAL \<close>

urust_expr primitive_path_dual_call \<open> u64::DUAL() \<close>

subsection\<open>Layout and lexical boundaries\<close>

urust_expr primitive_path_spaces \<open> u64 :: MAX \<close>

urust_expr primitive_path_newlines
  \<open>
    u64
      ::
    MAX
  \<close>

urust_expr primitive_path_line_comment
  \<open>
    u64 // before separator
      :: // before item
    MAX
  \<close>

urust_expr primitive_path_block_comment
  \<open> u64 /* outer /* nested */ comment */ :: MAX \<close>

urust_expr primitive_path_formal_comment
  \<open>
    u64
      \<comment> \<open>formal layout with \<^term>\<open>True\<close>\<close>
      ::
      MAX
  \<close>

urust_expr primitive_path_identifier_boundary \<open> u64_MAX \<close>

urust_expr primitive_path_identifier_prefix \<open> u64x::MAX \<close>

urust_expr primitive_path_apostrophe \<open> u64x'::MAX \<close>

urust_expr primitive_path_unsupported_width \<open> u128::MAX \<close>

urust_expr_rejects \<open> u64 \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64:: \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64::::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64:::::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> u64::u8 \<close> \<open> syntax error \<close>
urust_expr_rejects \<open> Module::u64::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects
  \<open> u64::<PrimitiveParam>::MAX \<close> \<open> syntax error \<close>
urust_expr_rejects
  \<open> u64::from::<>() \<close> \<open> syntax error \<close>
urust_expr_rejects
  \<open> u64::from::<PrimitiveParam,>() \<close> \<open> syntax error \<close>

subsection\<open>Expression composition\<close>

urust_expr primitive_path_prefix \<open> !u64::MAX \<close>
urust_expr primitive_path_dereference \<open> *u64::MAX \<close>
urust_expr primitive_path_cast_u8 \<open> u64::MIN as u8 \<close>
urust_expr primitive_path_cast_u16 \<open> u64::MIN as u16 \<close>
urust_expr primitive_path_cast_u32 \<open> u64::MIN as u32 \<close>
urust_expr primitive_path_cast_u64 \<open> u8::MAX as u64 \<close>
urust_expr primitive_path_cast_usize \<open> u64::MIN as usize \<close>
urust_expr primitive_path_cast_i32 \<open> u64::MIN as i32 \<close>
urust_expr primitive_path_cast_i64 \<open> u64::MIN as i64 \<close>

context includes primitive_path_cast_aliases
begin

urust_expr primitive_path_named_cast_alias
  \<open> u8::MAX as PrimitivePathAlias \<close>

end

urust_expr primitive_path_binary \<open> u64::MAX + 1u64 \<close>
urust_expr primitive_path_comparison \<open> u64::MIN < u64::MAX \<close>
urust_expr primitive_path_range \<open> u64::MIN..u64::MAX \<close>
urust_expr primitive_path_group \<open> (u64::MAX) \<close>
urust_expr primitive_path_block \<open> { u64::MAX } \<close>
urust_expr primitive_path_unsafe \<open> unsafe { u64::MAX } \<close>
urust_expr primitive_path_propagate \<open> u64::OPTION? \<close>
urust_expr primitive_path_field
  \<open> u64::RECORD.primitive_head_record_value \<close>
urust_expr primitive_path_method
  \<open> u64::MAX.primitive_head_bump() \<close>
urust_expr primitive_path_index \<open> u64::VALUES[0_usize] \<close>
urust_expr primitive_path_projection \<open> u64::PAIR.0 \<close>
urust_expr primitive_path_array \<open> [u64::MIN, u64::MAX] \<close>
urust_expr primitive_path_repeat
  \<open> [u64::MAX; usize::MAX] \<close>
urust_expr primitive_path_repeat_arithmetic
  \<open> [u64::MAX; usize::MAX + 1] \<close>
urust_expr primitive_path_macro_argument
  \<open> assert!(u64::MIN < u64::MAX) \<close>

urust_expr primitive_path_let
  \<open> let value = u64::MAX; value \<close>

urust_expr primitive_path_let_mut
  \<open> let mut value = u64::MAX; *value \<close>

urust_expr primitive_path_const
  \<open> const value = u64::MAX; value \<close>

urust_expr primitive_path_sequence
  \<open> u64::MIN; u64::MAX \<close>

urust_expr primitive_path_closure
  \<open> |value| value + u64::MAX \<close>

urust_expr primitive_path_return
  \<open> return u64::MAX \<close>

urust_expr primitive_path_if
  \<open> if u64::FLAG { u64::MAX } else { u64::MIN } \<close>

urust_expr primitive_path_if_let
  \<open>
    if let Some(value) = u64::OPTION {
      value
    } else {
      u64::MIN
    }
  \<close>

urust_expr primitive_path_if_let_constant
  \<open>
    if let u64::MAX = u64::MAX {
      true
    } else {
      false
    }
  \<close>

urust_expr primitive_path_for
  \<open> for value in u64::VALUES { let _ = value; () } \<close>

urust_expr primitive_path_while
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)]
    while (u64::FLAG) { () }
  \<close>

urust_expr primitive_path_loop
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)]
    loop { let value = u64::MAX; let _ = value; () }
  \<close>

urust_expr primitive_path_while_let
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)]
    while let Some(value) = u64::OPTION {
      let _ = value;
      ()
    }
  \<close>

urust_expr primitive_path_while_let_constant
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)]
    while let u64::MAX = u64::MAX { () }
  \<close>

urust_expr primitive_path_match
  \<open>
    match u64::MAX {
      u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_match_case
  \<open>
    match_case Some(u64::MAX) {
      Some(u64::MAX) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_match_switch
  \<open>
    match_switch u64::MAX {
      u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_semicolon_free_control
  \<open>
    if u64::FLAG { () }
    u64::MAX
  \<close>

subsection\<open>Pattern roles and place rejection\<close>

urust_expr primitive_path_tuple_pattern
  \<open>
    match_case (u64::MAX, Some(u64::MAX)) {
      (u64::MAX, Some(u64::MAX)) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_slice_pattern
  \<open>
    match_case [u64::MAX, u64::MIN] {
      [u64::MAX, _] \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_range_pattern
  \<open>
    match_case u64::MAX {
      u64::MIN..=u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_alias_pattern
  \<open>
    match_case u64::MAX {
      whole @ u64::MAX \<Rightarrow> whole,
      _ \<Rightarrow> u64::MIN
    }
  \<close>

urust_expr primitive_path_or_pattern
  \<open>
    match_case u64::MAX {
      u64::MIN | u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_guarded_pattern
  \<open>
    match_case u64::MAX {
      u64::MAX if u64::FLAG \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_matches_pattern
  \<open> matches!(u64::MAX, u64::MAX) \<close>

urust_expr_rejects
  \<open> let u64::MAX = u64::MAX; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> for u64::MAX in u64::VALUES { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> |u64::MAX| () \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::MAX = u64::MIN \<close>
  \<open> primitive associated-item path is not an assignment target \<close>

urust_expr_rejects
  \<open> u64::MAX { field: u64::MIN } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> match_case u64::MAX { u64::MAX { field: _ } \<Rightarrow> true } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> PrimitiveRecord { u64: u64::MAX } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::MAX.u64() \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> &u64::MAX \<close> \<open> no backend matches the use-site type \<close>

urust_expr_rejects
  \<open> *u64::MAX + true \<close> \<open> Unresolved adhoc overloading \<close>

subsection\<open>Exact-registration failures\<close>

urust_expr_rejects
  \<open> u64::MISSING \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> u64::MISSING() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

urust_expr_rejects
  \<open> u64::zero \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> u64::MAX() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

urust_expr_rejects
  \<open> u64::AMBIGUOUS \<close>
  \<open> Ambiguous uRust notation \<close>

urust_expr_rejects
  \<open> u64::MAX as u64::MAX \<close> \<open> syntax error \<close>

ML_val\<open>
  local
    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    val source_name = "primitive-headed-cast-alias-declaration"
    val result =
      Exn.result
        (run_command source_name
          "urust_cast_alias \"u64::PrimitiveAlias\" = \"u64\"") ()
    val _ =
      (case result of
         Exn.Res _ =>
           error
             "primitive-headed cast-target alias declaration was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               if String.isSubstring "reserved segment" message andalso
                  String.isSubstring source_name message
               then ()
               else
                 error
                   ("wrong primitive-headed cast-target alias diagnostic:\n" ^
                     message)
             end)
  in
    val _ = ()
  end
\<close>

urust_expr primitive_path_recovery_after_rejections
  \<open> u64::MAX \<close>

subsection\<open>AST, positions, markup, and recovery\<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "primitive path AST audit: empty parse")

    fun assert message condition =
      if condition then ()
      else error ("primitive path AST audit: " ^ message)

    fun names path =
      map (#1 o segment_identifier) (path_segments path)

    val _ =
      (case parse "u64::Nested::MAX" of
         UE_Path path =>
           (case path_head path of
              Primitive_Head (Primitive_Unsigned UT_U64) => ()
            | _ => error "primitive path AST audit: wrong primitive head";
            assert "segment order changed"
              (names path = ["u64", "Nested", "MAX"]);
            assert "canonical rendering changed"
              (render_path path = "u64::Nested::MAX"))
       | _ => error "primitive path AST audit: primitive value shape changed")

    val _ =
      (case parse "u64::from::<PrimitiveParam>(5u64)" of
         UE_Call (UC_Path path, [_], _) =>
           (assert "call head kind changed" (is_primitive_path path);
            assert "call canonical rendering changed"
              (render_path path =
                "u64::from::<PrimitiveParam>"))
       | _ => error "primitive path AST audit: primitive call shape changed")

    val _ =
      (case parse "u128::MAX" of
         UE_Path path =>
           (case path_head path of
              Identifier_Head => ()
            | _ =>
                error
                  "primitive path AST audit: unsupported width stopped being an identifier")
       | _ => error "primitive path AST audit: identifier boundary changed")

    val constructor_path =
      (case parse "u64::CONSTRUCTOR_VALUE" of
         UE_Path path => path
       | _ => error "primitive path AST audit: constructor-backed value shape changed")
    val constructor_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (path_position constructor_path)
    val _ =
      assert "constructor-backed primitive literal was not classified as a value"
        (URust_Resolution.classify_registered_literal ctxt
          constructor_resolver constructor_path =
            URust_Resolution.Registered_Value_Literal)
    val _ =
      assert "constructor fallback remained enabled for a primitive path"
        (is_none
          (URust_Resolution.resolve_constructor ctxt
            constructor_resolver constructor_path))

    val source_start =
      Position.make0 31 1000 0 "" ""
        "primitive-path-position-audit"
    val source =
      Parser_Lex_Util.positioned_content_source
        "u64::Nested::MAX" source_start
    val path =
      (case URust_Parser.parse_source ctxt source of
         SOME (UE_Path parsed) => parsed
       | _ => error "primitive path AST audit: positioned parse changed")
    val terminal_pos = #2 (segment_identifier (final_segment path))
    val _ =
      assert "complete path start changed"
        (Position.offset_of (path_position path) =
          Position.offset_of source_start)
    val _ =
      assert "complete path end changed"
        (Position.end_offset_of (path_position path) =
          Position.end_offset_of terminal_pos)
  in
    val _ = writeln "Primitive path AST and position audits passed"
  end
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then ()
      else error ("primitive path markup audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("primitive path markup audit: missing " ^ quote needle)
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
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun count_markup name position markup =
      length
        (filter
          (fn (candidate, properties) =>
            candidate = name andalso has_position properties position)
          markup)

    fun count_entity kind identity position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val text = "\<y>\<i>\<e>\<l>\<d>; u64::Nested::MAX"
    val start =
      Position.make0 37 1400 0 "" ""
        "primitive-path-markup-audit"
    val source =
      Parser_Lex_Util.positioned_content_source text start
    val captured =
      Synchronized.var "primitive_path_markup_reports" ([]: string list)
    fun capture chunks =
      Synchronized.change captured (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt source)) ())
          ())
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured)) []
    val (_, primitive_pos) =
      token_position text start "u64" 0
    val (first_separator_raw, first_separator_pos) =
      token_position text start "::" 0
    val (_, second_separator_pos) =
      token_position text start "::" (first_separator_raw + 2)
    val (_, nested_pos) =
      token_position text start "Nested" 0
    val (_, terminal_pos) =
      token_position text start "MAX" 0

    val _ =
      assert "primitive head lost keyword markup"
        (count_markup Markup.keyword1N primitive_pos markup = 1)
    val _ =
      assert "primitive head lost typing report"
        (count_markup Markup.typingN primitive_pos markup = 1)
    val _ =
      assert "primitive head gained free markup"
        (count_markup Markup.freeN primitive_pos markup = 0)
    val _ =
      assert "primitive head gained bound markup"
        (count_markup Markup.boundN primitive_pos markup = 0)
    val _ =
      assert "primitive head gained constructor styling"
        (count_markup Markup.keyword3N primitive_pos markup = 0)
    val _ =
      assert "primitive head gained notation navigation"
        (count_entity Micro_Rust_Names.notationN
          "u64::Nested::MAX" primitive_pos markup = 0)
    val _ =
      assert "first separator lost delimiter markup"
        (count_markup Markup.delimiterN first_separator_pos markup = 1)
    val _ =
      assert "second separator lost delimiter markup"
        (count_markup Markup.delimiterN second_separator_pos markup = 1)
    val _ =
      assert "identifier continuation retained free markup"
        (count_markup Markup.freeN nested_pos markup = 0)
    val _ =
      assert "identifier continuation lost registered-path typing"
        (count_markup Markup.typingN nested_pos markup = 1)
    val _ =
      assert "identifier continuation lost notation navigation"
        (count_entity Micro_Rust_Names.notationN
          "u64::Nested::MAX" nested_pos markup = 1)
    val _ =
      assert "terminal lost notation navigation"
        (count_entity Micro_Rust_Names.notationN
          "u64::Nested::MAX" terminal_pos markup = 1)
    val _ =
      assert "terminal lost notation styling"
        (count_markup Markup.keyword3N terminal_pos markup = 1)

    fun checked source_text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source source_text)

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun range_of position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

    val failure_text =
      "\<y>\<i>\<e>\<l>\<d>; u64::UNREGISTERED"
    val failure_start =
      Position.make0 41 1800 0 "" ""
        "primitive-path-diagnostic-audit"
    val failure_source =
      Parser_Lex_Util.positioned_content_source
        failure_text failure_start
    val (_, failure_position) =
      token_position failure_text failure_start "UNREGISTERED" 0
    val failure =
      Exn.result
        (fn () =>
          Parser_Test_Elaboration.expression ctxt failure_source)
        ()
    val _ =
      (case failure of
         Exn.Res _ =>
           error "primitive path markup audit: missing registration unexpectedly succeeded"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
             in
               assert "missing-registration diagnostic changed"
                 (String.isSubstring
                   "requires an exact micro_rust_notation (literal) declaration"
                   (XML.content_of body));
               assert "missing-registration diagnostic range changed"
                 (diagnostic_ranges body =
                   [range_of failure_position])
             end)
    val recovered = checked "u64::MAX"
    val _ =
      assert "recovery after rejection changed"
        (Term.exists_subterm
          (fn Const (name, _) =>
                name = \<^const_name>\<open>primitive_head_u64_max\<close>
            | _ => false)
          recovered)
  in
    val _ =
      writeln "Primitive path markup and recovery audits passed"
  end
\<close>


end
