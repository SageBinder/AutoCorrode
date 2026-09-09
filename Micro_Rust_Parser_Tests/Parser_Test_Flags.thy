theory Parser_Test_Flags
  imports Parser_Test_Utils
begin

section\<open> Default settings \<close>

ML_val\<open>
  local
    val captured = Synchronized.var "urust_default_options" ([]: string list)
    fun capture chunks = Synchronized.change captured (append chunks)
    val _ =
      Unsynchronized.setmp Private_Output.writeln_fn capture
        (Attrib.print_options false) \<^context>
    val output =
      XML.content_of
        (YXML.parse_body (implode (Synchronized.value captured)))
    fun assert_default expected =
      if String.isSubstring expected output then ()
      else
        error
          ("missing expected uRust option default " ^ quote expected ^
            " in:\n" ^ output)
    val _ =
      List.app assert_default
        ["urust_conformance_check: bool = false",
         "urust_verbose: int = 0",
         "urust_abbrev: bool = false"]
  in
    val _ = ()
  end
\<close>

urust_expr default_expr_flags \<open> () \<close>

urust_fn default_fun_flags ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>


section\<open> Inline flag combinations \<close>

text\<open>
\<open>urust_expr\<close> exercises every Boolean flag combination and all three verbosity levels.
\<open>urust_fn\<close> exercises both conformance settings at every verbosity level. The option order is
deliberately varied.
\<close>

urust_expr
  [conformance_check = false, verbose = 0, abbrev = false]
  inline_expr_000 \<open> () \<close>
urust_expr
  [abbrev = true, conformance_check = false, verbose = 0]
  inline_expr_001 \<open> () \<close>
urust_expr
  [verbose = 1, abbrev = false, conformance_check = false]
  inline_expr_010 \<open> () \<close>
urust_expr
  [conformance_check = false, abbrev = true, verbose = 1]
  inline_expr_011 \<open> () \<close>
urust_expr
  [verbose = 0, conformance_check = true, abbrev = false]
  inline_expr_100 \<open> () \<close>
urust_expr
  [abbrev = true, verbose = 0, conformance_check = true]
  inline_expr_101 \<open> () \<close>
urust_expr
  [conformance_check = true, verbose = 2, abbrev = false]
  inline_expr_110 \<open> () \<close>
urust_expr
  [verbose = 2, abbrev = true, conformance_check = true]
  inline_expr_111 \<open> () \<close>

urust_fn
  [verbose = 0, conformance_check = false]
  inline_fun_00 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [conformance_check = false, verbose = 1]
  inline_fun_01 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [verbose = 2, conformance_check = false]
  inline_fun_02 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [conformance_check = true, verbose = 0]
  inline_fun_10 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [verbose = 1, conformance_check = true]
  inline_fun_11 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [conformance_check = true, verbose = 2]
  inline_fun_12 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>


section\<open> Scoped settings and overrides \<close>

declare [[urust_conformance_check = true]]
declare [[urust_verbose = 2]]
declare [[urust_abbrev = true]]

urust_expr scoped_all_true_expr \<open> () \<close>

urust_fn scoped_all_true_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

urust_expr
  [verbose = 0, abbrev = false, conformance_check = false]
  scoped_all_false_expr \<open> () \<close>

urust_fn
  [conformance_check = false, verbose = 0]
  scoped_all_false_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

urust_expr [abbrev = false]
  scoped_partial_definition_expr \<open> () \<close>

urust_fn [conformance_check = false]
  scoped_partial_definition_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]

urust_expr reset_expr_flags \<open> () \<close>

urust_fn reset_fun_flags ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>


section\<open> Contextual expressions \<close>

urust_expr [conformance_check = true]
  contextual_order
  (first, second)
  \<open> \<llangle>(first :: nat, second :: bool)\<rrangle> \<close>

urust_expr [conformance_check = true]
  contextual_antiquotation
  (left, right)
  \<open> \<llangle>(left :: nat) + right\<rrangle> \<close>

urust_expr [conformance_check = true]
  contextual_shadowing
  (item, outer)
  \<open> let item = true; \<llangle>(item, outer :: nat)\<rrangle> \<close>

urust_expr
  [abbrev = true, conformance_check = true, verbose = 2]
  nie_contextual_helper
  (address, size)
  \<open> \<llangle>(address :: nat) + size\<rrangle> \<close>

urust_expr contextual_definition_against
  (operand)
  \<open> operand + 1u32 \<close>
  against \<open> \<lbrakk> operand + 1_u32 \<rbrakk> \<close>

urust_expr [abbrev = true]
  contextual_abbrev_against
  (operand)
  \<open> operand + 2u32 \<close>
  against \<open> \<lbrakk> operand + 2_u32 \<rbrakk> \<close>

urust_fn fun_definition_against ::
  \<open>32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body\<close>
  (operand)
  \<open> operand + 3u32 \<close>
  against \<open> \<lbrakk> operand + 3_u32 \<rbrakk> \<close>

urust_fn
  fun_definition_against_2 ::
  \<open>32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body\<close>
  (operand)
  \<open> operand + 4u32 \<close>
  against \<open> \<lbrakk> operand + 4_u32 \<rbrakk> \<close>

locale contextual_flags_locale =
  fixes offset :: nat
begin

urust_expr [abbrev = true, conformance_check = true]
  contextual_locale_helper
  (operand)
  \<open> \<llangle>operand + offset\<rrangle> \<close>

end

ML_val\<open>
  local
    val ctxt = \<^context>
    val first_pos =
      Position.make0 11 100 0 "" "contextual-order-audit" ""
    val second_pos =
      Position.make0 11 110 0 "" "contextual-order-audit" ""
    val source =
      Parser_Lex_Util.positioned_content_source
        "\<llangle>(first :: nat, second :: bool)\<rrangle>"
        (Position.make0 13 200 0 "" "contextual-order-audit" "")
    val actual =
      Parser_Test_Elaboration.expression_with_arguments ctxt
        [("first", first_pos), ("second", second_pos)] source
    val expected =
      Syntax.check_term ctxt
        (Syntax.parse_term ctxt
          "(\<lambda>(first :: nat) (second :: bool). \
          \\<lbrakk> \<llangle>(first, second)\<rrangle> \<rbrakk>)")
    val (formals, _) = Term.strip_abs actual
    val function_body_count =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = \<^const_name>\<open>FunctionBody\<close>
              then Integer.add 1
              else I
          | _ => I)
        actual 0
    val _ =
      if map #2 formals = [HOLogic.natT, HOLogic.boolT] then ()
      else error "expression parameters: inferred argument types or source order changed"
    val _ =
      if Term.aconv (actual, expected) then ()
      else error "expression parameters: contextual abstraction shape changed"
    val _ =
      if function_body_count = 0 then ()
      else error "expression parameters: contextual expression gained a FunctionBody wrapper"
  in
    val _ = ()
  end
\<close>


section\<open> Declaration artifacts \<close>

definition expr_abbrev_client where
  \<open> expr_abbrev_client = inline_expr_001 \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val consts = Proof_Context.consts_of ctxt

    fun assert message condition =
      if condition then () else error ("uRust flag artifact audit: " ^ message)

    fun has_fact name = can (Proof_Context.get_thm ctxt) name

    fun constant_name name =
      Consts.intern consts name

    fun is_abbreviation name =
      can (Consts.the_abbreviation consts) (constant_name name)

    fun executable_equations name =
      let
        val constant = constant_name name
      in
        (case Exn.result (Code.get_cert ctxt []) constant of
           Exn.Res certificate =>
             let
               val (_, equations) =
                 Code.equations_of_cert thy certificate
             in
               map_filter
                 (fn (_, (SOME theorem, _)) => SOME theorem
                   | _ => NONE)
                 (the equations)
             end
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn else [])
      end

    val definitions =
      ["default_expr_flags", "default_fun_flags",
       "inline_expr_000", "inline_expr_010",
       "inline_expr_100", "inline_expr_110",
       "inline_fun_00", "inline_fun_01", "inline_fun_02",
       "inline_fun_10", "inline_fun_11", "inline_fun_12",
       "scoped_all_true_fun",
       "scoped_all_false_expr", "scoped_all_false_fun",
       "scoped_partial_definition_expr", "scoped_partial_definition_fun",
       "reset_expr_flags", "reset_fun_flags",
       "contextual_order", "contextual_antiquotation",
       "contextual_shadowing", "contextual_definition_against",
       "fun_definition_against", "fun_definition_against_2"]

    val abbreviations =
      ["inline_expr_001", "inline_expr_011",
       "inline_expr_101", "inline_expr_111",
       "scoped_all_true_expr", "nie_contextual_helper",
       "contextual_abbrev_against"]

    val conforming =
      ["inline_expr_100", "inline_expr_101",
       "inline_expr_110", "inline_expr_111",
       "inline_fun_10", "inline_fun_11", "inline_fun_12",
       "scoped_all_true_expr", "scoped_all_true_fun",
       "scoped_partial_definition_expr",
       "contextual_order", "contextual_antiquotation",
       "contextual_shadowing", "nie_contextual_helper",
       "contextual_definition_against", "contextual_abbrev_against",
       "fun_definition_against", "fun_definition_against_2"]

    val nonconforming =
      ["default_expr_flags", "default_fun_flags",
       "inline_expr_000", "inline_expr_001",
       "inline_expr_010", "inline_expr_011",
       "inline_fun_00", "inline_fun_01", "inline_fun_02",
       "scoped_all_false_expr", "scoped_all_false_fun",
       "scoped_partial_definition_fun",
       "reset_expr_flags", "reset_fun_flags"]

    fun check_definition name =
      (assert (quote name ^ " is missing its _def fact")
         (has_fact (name ^ "_def"));
       assert (quote name ^ " was registered as an abbreviation")
         (not (is_abbreviation name));
       assert (quote name ^ " does not have one code equation")
         (length (executable_equations name) = 1))

    fun check_abbreviation name =
      (assert (quote name ^ " unexpectedly has a _def fact")
         (not (has_fact (name ^ "_def")));
       assert (quote name ^ " is not registered as an abbreviation")
         (is_abbreviation name);
       assert (quote name ^ " unexpectedly has a code equation")
         (null (executable_equations name)))

    val _ = List.app check_definition definitions
    val _ = List.app check_abbreviation abbreviations
    val _ =
      List.app
        (fn name =>
          assert (quote name ^ " is missing _conformance")
            (has_fact (name ^ "_conformance")))
        conforming
    val _ =
      List.app
        (fn name =>
          assert (quote name ^ " unexpectedly has _conformance")
            (not (has_fact (name ^ "_conformance"))))
        nonconforming

    fun assert_expanded client abbreviation =
      let
        val proposition =
          Thm.prop_of (Proof_Context.get_thm ctxt (client ^ "_def"))
        val abbreviation_name = constant_name abbreviation
        val printed = Syntax.string_of_term ctxt proposition
      in
        assert
          (quote abbreviation ^ " survived in checked client term")
          (not
            (Term.exists_subterm
              (fn Const (name, _) => name = abbreviation_name
                | _ => false)
              proposition));
        assert
          (quote abbreviation ^ " was folded back during pretty printing")
          (not (String.isSubstring abbreviation printed))
      end

    val _ = assert_expanded "expr_abbrev_client" "inline_expr_001"
  in
    val _ = ()
  end
\<close>


section\<open> Invalid flags and argument lists \<close>

ML_val\<open>
  local
    val unit_source = Symbol.open_ ^ " () " ^ Symbol.close
    val body_type =
      Symbol.open_ ^
      "(unit, unit, unit, unit, unit) function_body" ^
      Symbol.close
    val unary_body_type =
      Symbol.open_ ^
      "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body" ^
      Symbol.close
    val serial = Unsynchronized.ref 0

    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
        val _ =
          if null transitions then error "expected at least one parsed uRust command"
          else ()
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun recovery () =
      let
        val index = !serial
        val _ = serial := index + 1
      in
        ignore
          (run_command ("flag-recovery-" ^ string_of_int index)
            ("urust_expr [abbrev = true] recovered_" ^
              string_of_int index ^ " " ^ unit_source) ())
      end

    fun assert_rejected source_name command_text expected =
      (case Exn.result (run_command source_name command_text) () of
         Exn.Res _ =>
           error
             ("invalid uRust command was unexpectedly accepted" ^
               Position.here (Position.file source_name))
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message = Runtime.exn_message exn
               val _ =
                 if String.isSubstring expected message andalso
                    String.isSubstring source_name message
                 then ()
                 else
                   error
                     ("unexpected uRust command diagnostic:\n" ^ message ^
                       "\nexpected: " ^ quote expected)
             in recovery () end)

    datatype command_kind = Expr | Fn

    fun command Expr options name suffix =
          "urust_expr " ^ options ^ " " ^ name ^ " " ^
            unit_source ^ suffix
      | command Fn options name suffix =
          "urust_fn " ^ options ^ " " ^ name ^ " :: " ^
            body_type ^ " () " ^ unit_source ^ suffix

    fun kind_label Expr = "expr"
      | kind_label Fn = "fn"

    fun case_label (kind, abbreviation) =
      kind_label kind ^
        (if abbreviation then "-abbrev" else "-definition")

    fun option_block kind abbreviation options =
      let
        val expression_options =
          (case kind of
             Expr =>
               ("abbrev = " ^ Bool.toString abbreviation) :: options
           | Fn => options)
      in
        "[" ^ commas expression_options ^ "]"
      end

    val expression_cases = [(Expr, false), (Expr, true)]
    val command_cases = expression_cases @ [(Fn, false)]

    fun test_unknown (case_ as (kind, abbreviation)) =
      let
        val label =
          "unknown-option-" ^ case_label case_
        val options =
          option_block kind abbreviation
            ["urust_future_flag = true"]
      in
        assert_rejected label
          (command kind options "unknown_flag" "")
          "unknown uRust command option \"urust_future_flag\""
      end

    fun test_prefixed prefixed (case_ as (kind, abbreviation)) =
      let
        val label =
          "prefixed-inline-" ^ prefixed ^ "-" ^ case_label case_
        val options =
          option_block kind abbreviation [prefixed ^ " = true"]
      in
        assert_rejected label
          (command kind options "legacy_flag" "")
          ("unknown uRust command option " ^ quote prefixed)
      end

    fun test_duplicate flag (case_ as (kind, abbreviation)) =
      let
        val label =
          "duplicate-" ^ flag ^ "-" ^ case_label case_
        val value = Bool.toString abbreviation
        val (first, second) =
          if flag = "verbose" then ("0", "1")
          else ("true", "false")
        val options =
          if flag = "abbrev" then
            "[" ^ flag ^ " = " ^ value ^ ", " ^
              flag ^ " = " ^ value ^ "]"
          else
            option_block kind abbreviation
              [flag ^ " = " ^ first, flag ^ " = " ^ second]
      in
        assert_rejected label
          (command kind options "duplicate_flag" "")
          ("duplicate uRust command option " ^ quote flag)
      end

    fun test_contradiction (case_ as (kind, abbreviation)) =
      let
        val label =
          "contradictory-" ^ case_label case_
        val options =
          option_block kind abbreviation
            ["conformance_check = false"]
        val suffix =
          " against " ^ Symbol.open_ ^ " \<lbrakk> () \<rbrakk> " ^ Symbol.close
      in
        assert_rejected label
          (command kind options "contradictory_flag" suffix)
          "[conformance_check = false] cannot be combined with `against`"
      end

    fun test_invalid_verbosity (case_ as (kind, abbreviation)) =
      let
        val label =
          "invalid-verbosity-" ^ case_label case_
        val options =
          option_block kind abbreviation ["verbose = 3"]
      in
        assert_rejected label
          (command kind options "invalid_verbosity" "")
          "must be 0, 1, or 2, but found 3"
      end

    fun test_wrong_option_type (case_ as (kind, abbreviation)) =
      let
        val label =
          "wrong-option-type-" ^ case_label case_
      in
        assert_rejected (label ^ "-verbosity")
          (command kind
            (option_block kind abbreviation ["verbose = true"])
            "Boolean_verbosity" "")
          "expects an integer from 0 to 2";
        assert_rejected (label ^ "-conformance")
          (command kind
            (option_block kind abbreviation
              ["conformance_check = 1"])
            "integer_conformance" "")
          "expects true or false"
      end

    val _ = List.app test_unknown command_cases
    val _ =
      List.app
        (fn prefixed =>
          List.app (test_prefixed prefixed) command_cases)
        ["urust_conformance_check", "urust_verbose", "urust_abbrev"]
    val _ =
      List.app
        (fn flag =>
          List.app (test_duplicate flag) command_cases)
        ["conformance_check", "verbose"]
    val _ =
      List.app (test_duplicate "abbrev") expression_cases
    val _ = List.app test_contradiction command_cases
    val _ = List.app test_invalid_verbosity command_cases
    val _ = List.app test_wrong_option_type command_cases
    val _ =
      assert_rejected "function-abbrev-option"
        (command Fn "[abbrev = true]" "function_abbrev" "")
        "unknown uRust command option \"abbrev\""
    val _ =
      assert_rejected "invalid-scoped-verbosity"
        ("declare [[urust_verbose = 3]]\n" ^
          "urust_expr invalid_scoped_verbosity " ^ unit_source)
        "must be 0, 1, or 2, but found 3"

    val _ =
      ignore
        (run_command "empty-expression-parameters"
          ("urust_expr empty_args () " ^ unit_source) ())
    val _ =
      ignore
        (run_command "trailing-comma-expression-parameters"
          ("urust_expr trailing_args (item,) " ^
            Symbol.open_ ^ " \<llangle>item :: nat\<rrangle> " ^ Symbol.close) ())
    val _ =
      ignore
        (run_command "omitted-function-parameters"
          ("urust_fn omitted_fun_args :: " ^ body_type ^ " " ^
            unit_source) ())
    val _ =
      ignore
        (run_command "trailing-comma-function-parameters"
          ("urust_fn trailing_fun_args :: " ^ unary_body_type ^
            " (item,) " ^ Symbol.open_ ^ " item " ^ Symbol.close) ())
    val _ =
      assert_rejected "missing-function-type"
        ("urust_fn missing_fun_type () " ^ unit_source)
        "function elaboration requires a declared type"
    val _ =
      assert_rejected "wildcard-expression-parameter"
        ("urust_expr wildcard_args (_) " ^ unit_source)
        "argument name `_` is not allowed"
    val _ =
      assert_rejected "duplicate-expression-parameters"
        ("urust_expr duplicate_args (item, item) " ^ unit_source)
        "duplicate argument \"item\""
    val _ =
      assert_rejected "legacy-with-args"
        ("urust_expr legacy_args " ^ unit_source ^ " with_args item")
        "command expected"
    val _ =
      assert_rejected "legacy-function-command"
        ("urust_fun legacy_function :: " ^ body_type ^ " () " ^ unit_source)
        "command expected"
    val _ =
      assert_rejected "legacy-declaration-command"
        ("decl_urust expr legacy_declaration " ^ unit_source)
        "command expected"
    val _ =
      assert_rejected "legacy-unified-command"
        ("urust expr legacy_unified " ^ unit_source)
        "command expected"
    val _ =
      assert_rejected "misplaced-expression-parameters"
        ("urust_expr misplaced_args " ^ unit_source ^
          " against " ^ Symbol.open_ ^ " \<lbrakk> () \<rbrakk> " ^ Symbol.close ^
          " (item)")
        "command expected"
  in
    val _ = ()
  end
\<close>


section\<open> Contextual binder markup \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val file = "urust-expression-parameter-markup-audit"
    val document_id = "urust-expression-parameter-markup-audit"
    val first_definition =
      Position.make0 11 100 0 "" file document_id
    val second_definition =
      Position.make0 11 110 0 "" file document_id
    val body_text =
      "\<llangle>(first :: nat, second :: bool, first)\<rrangle>"
    val body_start =
      Position.make0 13 200 0 "" file document_id
    val body_source =
      Parser_Lex_Util.positioned_content_source body_text body_start
    val captured =
      Synchronized.var "urust_expression_parameter_markup" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured (append chunks)

    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression_with_arguments ctxt
                  [("first", first_definition),
                   ("second", second_definition)]
                  body_source) ())
          ())

    fun collect (XML.Text _) result = result
      | collect (XML.Elem (markup, body)) result =
          fold collect body (markup :: result)
    val markup =
      fold collect
        (maps YXML.parse_body (Synchronized.value captured)) []

    fun find_from needle offset =
      if offset + size needle > size body_text then
        error ("expression parameter markup audit: missing " ^ quote needle)
      else if String.substring (body_text, offset, size needle) = needle then
        offset
      else find_from needle (offset + 1)

    fun token_position needle offset =
      let
        val raw = find_from needle offset
        val start =
          Position.symbol_explode
            (String.substring (body_text, 0, raw)) body_start
      in
        (raw,
         Position.range_position
           (Position.range (start, Position.symbol_explode needle start)))
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

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
               ("expression parameter markup audit: binder entity markup changed at" ^
                 Position.here position))
      end

    val (first_offset, first_reference_one) =
      token_position "first" 0
    val (second_offset, second_reference) =
      token_position "second" (first_offset + size "first")
    val (_, first_reference_two) =
      token_position "first" (second_offset + size "second")
    val first_id = entity_id Markup.defN first_definition
    val second_id = entity_id Markup.defN second_definition
    val _ =
      if first_id <> second_id then ()
      else error "expression parameter markup audit: arguments reused an entity ID"
    val _ =
      if entity_id Markup.refN first_reference_one = first_id andalso
         entity_id Markup.refN first_reference_two = first_id
      then ()
      else error "expression parameter markup audit: first references lost navigation"
    val _ =
      if entity_id Markup.refN second_reference = second_id then ()
      else error "expression parameter markup audit: second reference lost navigation"
  in
    val _ = ()
  end
\<close>

end
