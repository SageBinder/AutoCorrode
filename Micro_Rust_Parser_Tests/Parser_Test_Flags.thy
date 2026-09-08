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
    fun assert_default name =
      if String.isSubstring (name ^ ": bool = false") output then ()
      else
        error
          ("default value for " ^ quote name ^
            " is not false in:\n" ^ output)
    val _ =
      List.app assert_default
        ["urust_conformance_check", "urust_verbose", "urust_abbrev"]
  in
    val _ = ()
  end
\<close>

urust_expr default_expr_flags \<open> () \<close>

urust_fun default_fun_flags ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>


section\<open> Inline flag combinations \<close>

text\<open>
Each command form exercises all eight Boolean combinations. The option order is deliberately varied.
\<close>

urust_expr
  [urust_conformance_check = false, urust_verbose = false, urust_abbrev = false]
  inline_expr_000 \<open> () \<close>
urust_expr
  [urust_abbrev = true, urust_conformance_check = false, urust_verbose = false]
  inline_expr_001 \<open> () \<close>
urust_expr
  [urust_verbose = true, urust_abbrev = false, urust_conformance_check = false]
  inline_expr_010 \<open> () \<close>
urust_expr
  [urust_conformance_check = false, urust_abbrev = true, urust_verbose = true]
  inline_expr_011 \<open> () \<close>
urust_expr
  [urust_verbose = false, urust_conformance_check = true, urust_abbrev = false]
  inline_expr_100 \<open> () \<close>
urust_expr
  [urust_abbrev = true, urust_verbose = false, urust_conformance_check = true]
  inline_expr_101 \<open> () \<close>
urust_expr
  [urust_conformance_check = true, urust_verbose = true, urust_abbrev = false]
  inline_expr_110 \<open> () \<close>
urust_expr
  [urust_verbose = true, urust_abbrev = true, urust_conformance_check = true]
  inline_expr_111 \<open> () \<close>

urust_fun
  [urust_abbrev = false, urust_verbose = false, urust_conformance_check = false]
  inline_fun_000 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fun
  [urust_conformance_check = false, urust_abbrev = true, urust_verbose = false]
  inline_fun_001 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fun
  [urust_verbose = true, urust_conformance_check = false, urust_abbrev = false]
  inline_fun_010 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fun
  [urust_abbrev = true, urust_verbose = true, urust_conformance_check = false]
  inline_fun_011 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fun
  [urust_conformance_check = true, urust_abbrev = false, urust_verbose = false]
  inline_fun_100 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fun
  [urust_verbose = false, urust_conformance_check = true, urust_abbrev = true]
  inline_fun_101 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fun
  [urust_abbrev = false, urust_conformance_check = true, urust_verbose = true]
  inline_fun_110 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fun
  [urust_verbose = true, urust_conformance_check = true, urust_abbrev = true]
  inline_fun_111 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>


section\<open> Scoped settings and overrides \<close>

declare [[urust_conformance_check = true]]
declare [[urust_verbose = true]]
declare [[urust_abbrev = true]]

urust_expr scoped_all_true_expr \<open> () \<close>

urust_fun scoped_all_true_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

urust_expr
  [urust_verbose = false, urust_abbrev = false, urust_conformance_check = false]
  scoped_all_false_expr \<open> () \<close>

urust_fun
  [urust_conformance_check = false, urust_verbose = false, urust_abbrev = false]
  scoped_all_false_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

urust_expr [urust_abbrev = false]
  scoped_partial_definition_expr \<open> () \<close>

urust_fun [urust_conformance_check = false]
  scoped_partial_abbrev_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = false]]
declare [[urust_abbrev = false]]

urust_expr reset_expr_flags \<open> () \<close>

urust_fun reset_fun_flags ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>


section\<open> Contextual expressions \<close>

urust_expr [urust_conformance_check = true]
  contextual_order
  \<open> \<llangle>(first :: nat, second :: bool)\<rrangle> \<close>
  with_args first second

urust_expr [urust_conformance_check = true]
  contextual_antiquotation
  \<open> \<llangle>(left :: nat) + right\<rrangle> \<close>
  with_args left right

urust_expr [urust_conformance_check = true]
  contextual_shadowing
  \<open> let item = true; \<llangle>(item, outer :: nat)\<rrangle> \<close>
  with_args item outer

urust_expr
  [urust_abbrev = true, urust_conformance_check = true, urust_verbose = true]
  nie_contextual_helper
  \<open> \<llangle>(address :: nat) + size\<rrangle> \<close>
  with_args address size

urust_expr contextual_definition_against
  \<open> operand + 1u32 \<close>
  with_args operand
  against \<open> \<lbrakk> operand + 1_u32 \<rbrakk> \<close>

urust_expr [urust_abbrev = true]
  contextual_abbrev_against
  \<open> operand + 2u32 \<close>
  with_args operand
  against \<open> \<lbrakk> operand + 2_u32 \<rbrakk> \<close>

urust_fun fun_definition_against ::
  \<open>32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body\<close>
  (operand)
  \<open> operand + 3u32 \<close>
  against \<open> \<lbrakk> operand + 3_u32 \<rbrakk> \<close>

urust_fun [urust_abbrev = true]
  fun_abbrev_against ::
  \<open>32 word \<Rightarrow> (unit, 32 word, unit, unit, unit) function_body\<close>
  (operand)
  \<open> operand + 4u32 \<close>
  against \<open> \<lbrakk> operand + 4_u32 \<rbrakk> \<close>

locale contextual_flags_locale =
  fixes offset :: nat
begin

urust_expr [urust_abbrev = true, urust_conformance_check = true]
  contextual_locale_helper
  \<open> \<llangle>operand + offset\<rrangle> \<close>
  with_args operand

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
      Parser_Test_Elaboration.expression_with_args ctxt
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
      else error "with_args: inferred argument types or source order changed"
    val _ =
      if Term.aconv (actual, expected) then ()
      else error "with_args: contextual abstraction shape changed"
    val _ =
      if function_body_count = 0 then ()
      else error "with_args: contextual expression gained a FunctionBody wrapper"
  in
    val _ = ()
  end
\<close>


section\<open> Declaration artifacts \<close>

definition expr_abbrev_client where
  \<open> expr_abbrev_client = inline_expr_001 \<close>

definition fun_abbrev_client where
  \<open> fun_abbrev_client = inline_fun_001 \<close>

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
       "inline_fun_000", "inline_fun_010",
       "inline_fun_100", "inline_fun_110",
       "scoped_all_false_expr", "scoped_all_false_fun",
       "scoped_partial_definition_expr",
       "reset_expr_flags", "reset_fun_flags",
       "contextual_order", "contextual_antiquotation",
       "contextual_shadowing", "contextual_definition_against",
       "fun_definition_against"]

    val abbreviations =
      ["inline_expr_001", "inline_expr_011",
       "inline_expr_101", "inline_expr_111",
       "inline_fun_001", "inline_fun_011",
       "inline_fun_101", "inline_fun_111",
       "scoped_all_true_expr", "scoped_all_true_fun",
       "scoped_partial_abbrev_fun", "nie_contextual_helper",
       "contextual_abbrev_against", "fun_abbrev_against"]

    val conforming =
      ["inline_expr_100", "inline_expr_101",
       "inline_expr_110", "inline_expr_111",
       "inline_fun_100", "inline_fun_101",
       "inline_fun_110", "inline_fun_111",
       "scoped_all_true_expr", "scoped_all_true_fun",
       "scoped_partial_definition_expr",
       "contextual_order", "contextual_antiquotation",
       "contextual_shadowing", "nie_contextual_helper",
       "contextual_definition_against", "contextual_abbrev_against",
       "fun_definition_against", "fun_abbrev_against"]

    val nonconforming =
      ["default_expr_flags", "default_fun_flags",
       "inline_expr_000", "inline_expr_001",
       "inline_expr_010", "inline_expr_011",
       "inline_fun_000", "inline_fun_001",
       "inline_fun_010", "inline_fun_011",
       "scoped_all_false_expr", "scoped_all_false_fun",
       "scoped_partial_abbrev_fun",
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
      in
        assert
          (quote abbreviation ^ " survived in checked client term")
          (not
            (Term.exists_subterm
              (fn Const (name, _) => name = abbreviation_name
                | _ => false)
              proposition))
      end

    val _ = assert_expanded "expr_abbrev_client" "inline_expr_001"
    val _ = assert_expanded "fun_abbrev_client" "inline_fun_001"
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
    val serial = Unsynchronized.ref 0

    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
        val _ =
          if length transitions = 1 then ()
          else error "expected exactly one parsed uRust command"
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
            ("urust_expr [urust_abbrev = true] recovered_" ^
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

    datatype command_kind = Expr | Fun

    fun command Expr options name suffix =
          "urust_expr " ^ options ^ " " ^ name ^ " " ^
            unit_source ^ suffix
      | command Fun options name suffix =
          "urust_fun " ^ options ^ " " ^ name ^ " :: " ^
            body_type ^ " () " ^ unit_source ^ suffix

    fun mode_option false = "urust_abbrev = false"
      | mode_option true = "urust_abbrev = true"

    val kinds = [Expr, Fun]
    val modes = [false, true]

    fun test_unknown kind abbreviation =
      let
        val label =
          "unknown-option-" ^
          (case kind of Expr => "expr" | Fun => "fun") ^
          (if abbreviation then "-abbrev" else "-definition")
        val options =
          "[" ^ mode_option abbreviation ^
          ", urust_future_flag = true]"
      in
        assert_rejected label
          (command kind options "unknown_flag" "")
          "unknown uRust command option \"urust_future_flag\""
      end

    fun test_legacy legacy kind abbreviation =
      let
        val label =
          "legacy-" ^ legacy ^ "-" ^
          (case kind of Expr => "expr" | Fun => "fun") ^
          (if abbreviation then "-abbrev" else "-definition")
        val options =
          "[" ^ mode_option abbreviation ^ ", " ^ legacy ^ " = true]"
      in
        assert_rejected label
          (command kind options "legacy_flag" "")
          ("unknown uRust command option " ^ quote legacy)
      end

    fun test_duplicate flag kind abbreviation =
      let
        val label =
          "duplicate-" ^ flag ^ "-" ^
          (case kind of Expr => "expr" | Fun => "fun") ^
          (if abbreviation then "-abbrev" else "-definition")
        val value = Bool.toString abbreviation
        val options =
          if flag = "urust_abbrev" then
            "[" ^ flag ^ " = " ^ value ^ ", " ^
              flag ^ " = " ^ value ^ "]"
          else
            "[" ^ mode_option abbreviation ^ ", " ^
              flag ^ " = true, " ^ flag ^ " = false]"
      in
        assert_rejected label
          (command kind options "duplicate_flag" "")
          ("duplicate uRust command option " ^ quote flag)
      end

    fun test_contradiction kind abbreviation =
      let
        val label =
          "contradictory-" ^
          (case kind of Expr => "expr" | Fun => "fun") ^
          (if abbreviation then "-abbrev" else "-definition")
        val options =
          "[" ^ mode_option abbreviation ^
          ", urust_conformance_check = false]"
        val suffix =
          " against " ^ Symbol.open_ ^ " \<lbrakk> () \<rbrakk> " ^ Symbol.close
      in
        assert_rejected label
          (command kind options "contradictory_flag" suffix)
          "[urust_conformance_check = false] cannot be combined with `against`"
      end

    val _ = List.app (fn kind => List.app (test_unknown kind) modes) kinds
    val _ =
      List.app
        (fn legacy =>
          List.app
            (fn kind => List.app (test_legacy legacy kind) modes)
            kinds)
        ["conformance_check", "verbose", "abbrev"]
    val _ =
      List.app
        (fn flag =>
          List.app
            (fn kind => List.app (test_duplicate flag kind) modes)
            kinds)
        ["urust_conformance_check", "urust_verbose", "urust_abbrev"]
    val _ =
      List.app
        (fn kind => List.app (test_contradiction kind) modes)
        kinds

    val _ =
      assert_rejected "empty-with-args"
        ("urust_expr empty_args " ^ unit_source ^ " with_args")
        "`with_args` requires at least one argument"
    val _ =
      assert_rejected "wildcard-with-args"
        ("urust_expr wildcard_args " ^ unit_source ^ " with_args _")
        "argument name `_` is not allowed"
    val _ =
      assert_rejected "duplicate-with-args"
        ("urust_expr duplicate_args " ^ unit_source ^ " with_args item item")
        "duplicate argument \"item\""
    val _ =
      assert_rejected "misplaced-with-args"
        ("urust_expr misplaced_args " ^ unit_source ^
          " against " ^ Symbol.open_ ^ " \<lbrakk> () \<rbrakk> " ^ Symbol.close ^
          " with_args item")
        "command expected"
  in
    val _ = ()
  end
\<close>


section\<open> Contextual binder markup \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val file = "urust-with-args-markup-audit"
    val document_id = "urust-with-args-markup-audit"
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
      Synchronized.var "urust_with_args_markup" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured (append chunks)

    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression_with_args ctxt
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
        error ("with_args markup audit: missing " ^ quote needle)
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
               ("with_args markup audit: binder entity markup changed at" ^
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
      else error "with_args markup audit: arguments reused an entity ID"
    val _ =
      if entity_id Markup.refN first_reference_one = first_id andalso
         entity_id Markup.refN first_reference_two = first_id
      then ()
      else error "with_args markup audit: first references lost navigation"
    val _ =
      if entity_id Markup.refN second_reference = second_id then ()
      else error "with_args markup audit: second reference lost navigation"
  in
    val _ = ()
  end
\<close>

end
