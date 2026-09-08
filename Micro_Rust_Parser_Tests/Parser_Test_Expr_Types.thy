theory Parser_Test_Expr_Types
  imports Parser_Test_Utils
begin

section\<open> Common elaboration API \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val source_pos =
      Position.make0 11 100 0 "" "urust-common-api" ""
    val argument_pos =
      Position.make0 13 200 0 "" "urust-common-api" ""

    fun source text =
      Parser_Lex_Util.positioned_content_source text source_pos

    fun elaborate kind text arguments declared_type =
      URust_Command.elaborate ctxt
        {kind = kind,
         source = source text,
         arguments = arguments,
         arguments_pos = argument_pos,
         declared_type = declared_type}

    val untyped =
      elaborate URust_Command.Expression
        "\<llangle>1 :: nat\<rrangle>" [] NONE
    val typed_expression_type =
      "(unit, nat, unit, unit, unit, unit) expression"
    val typed_expression =
      elaborate URust_Command.Expression
        "\<llangle>1 :: nat\<rrangle>" []
        (SOME (typed_expression_type, Position.line 17))
    val typed_function_type =
      "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
    val typed_function =
      elaborate URust_Command.Function
        "item" [("item", argument_pos)]
        (SOME (typed_function_type, Position.line 19))

    fun count_constant expected =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)

    val _ =
      (case Term.body_type (fastype_of untyped) of
         Type (name, _) =>
           if name = \<^type_name>\<open>expression\<close> then ()
           else error "common elaborator: untyped expression result changed"
       | _ => error "common elaborator: untyped expression type disappeared")
    val _ =
      if fastype_of typed_expression =
          Syntax.read_typ ctxt typed_expression_type
      then ()
      else error "common elaborator: typed expression constraint was not preserved"
    val _ =
      if fastype_of typed_function =
          Syntax.read_typ ctxt typed_function_type
      then ()
      else error "common elaborator: typed function constraint was not preserved"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close>
          typed_expression 0 = 0
      then ()
      else error "common elaborator: expression gained a FunctionBody wrapper"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close>
          typed_function 0 = 1
      then ()
      else error "common elaborator: function wrapper count changed"
  in
    val _ = ()
  end
\<close>


section\<open> Typed declaration surface \<close>

declare [[urust_conformance_check = true]]

urust_expr typed_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>42 :: nat\<rrangle> \<close>

urust_expr typed_contextual ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> item \<close>
  with_args item

urust_expr typed_heterogeneous ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, nat \<times> bool, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>(number, flag)\<rrangle> \<close>
  with_args number flag

urust_expr typed_higher_order ::
  \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>f item\<rrangle> \<close>
  with_args f item

urust_expr typed_polymorphic ::
  \<open>'a \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> item \<close>
  with_args item

urust_expr typed_sort_constrained ::
  \<open>'a::len word \<Rightarrow>
    ('s, 'a word, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> item \<close>
  with_args item

urust_expr typed_placeholders ::
  \<open>_ \<Rightarrow> (_, _, _, _, _, _) expression\<close>
  \<open> item \<close>
  with_args item

text\<open>
A declaration ending in \<open>function_body\<close> selects function elaboration through the same
\<open>urust_expr\<close> command and therefore wraps the checked body exactly once.
\<close>

urust_expr typed_function_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  \<open> item \<close>
  with_args item

thm typed_closed_conformance
thm typed_contextual_conformance
thm typed_heterogeneous_conformance
thm typed_higher_order_conformance
thm typed_polymorphic_conformance
thm typed_sort_constrained_conformance
thm typed_placeholders_conformance
thm typed_function_common_conformance


section\<open> Definitions, abbreviations, flags, locales, and against \<close>

declare [[urust_conformance_check = false]]

urust_expr
  [urust_conformance_check = false, urust_verbose = false, urust_abbrev = false]
  typed_flags_000 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_abbrev = true, urust_conformance_check = false, urust_verbose = false]
  typed_flags_001 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_verbose = true, urust_abbrev = false, urust_conformance_check = false]
  typed_flags_010 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_conformance_check = false, urust_abbrev = true, urust_verbose = true]
  typed_flags_011 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_verbose = false, urust_conformance_check = true, urust_abbrev = false]
  typed_flags_100 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_abbrev = true, urust_verbose = false, urust_conformance_check = true]
  typed_flags_101 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_conformance_check = true, urust_verbose = true, urust_abbrev = false]
  typed_flags_110 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_verbose = true, urust_abbrev = true, urust_conformance_check = true]
  typed_flags_111 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [urust_abbrev = true, urust_conformance_check = true, urust_verbose = true]
  typed_function_abbrev_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  \<open> item \<close>
  with_args item

urust_expr typed_against ::
  \<open>32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit, unit) expression\<close>
  \<open> operand + 1u32 \<close>
  with_args operand
  against \<open> \<lbrakk> operand + 1_u32 \<rbrakk> \<close>

locale typed_expression_locale =
  fixes offset :: nat
begin

urust_expr
  [urust_abbrev = true, urust_conformance_check = true]
  typed_local_add ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>item + offset\<rrangle> \<close>
  with_args item

end

definition typed_flags_abbrev_client where
  \<open>typed_flags_abbrev_client = typed_flags_001\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val consts = Proof_Context.consts_of ctxt

    fun assert message condition =
      if condition then ()
      else error ("typed declaration artifact audit: " ^ message)

    fun has_fact name = can (Proof_Context.get_thm ctxt) name

    fun constant_name name = Consts.intern consts name

    fun is_abbreviation name =
      can (Consts.the_abbreviation consts) (constant_name name)

    fun executable_equations name =
      (case Exn.result (Code.get_cert ctxt []) (constant_name name) of
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

    val definitions =
      ["typed_closed", "typed_contextual", "typed_heterogeneous",
       "typed_higher_order", "typed_polymorphic",
       "typed_sort_constrained", "typed_placeholders",
       "typed_function_common", "typed_flags_000", "typed_flags_010",
       "typed_flags_100", "typed_flags_110", "typed_against"]
    val abbreviations =
      ["typed_flags_001", "typed_flags_011",
       "typed_flags_101", "typed_flags_111",
       "typed_function_abbrev_common"]
    val conforming =
      ["typed_closed", "typed_contextual", "typed_heterogeneous",
       "typed_higher_order", "typed_polymorphic",
       "typed_sort_constrained", "typed_placeholders",
       "typed_function_common", "typed_flags_100",
       "typed_flags_101", "typed_flags_110", "typed_flags_111",
       "typed_function_abbrev_common", "typed_against"]
    val nonconforming =
      ["typed_flags_000", "typed_flags_001",
       "typed_flags_010", "typed_flags_011"]

    fun check_definition name =
      (assert (quote name ^ " is missing its _def fact")
         (has_fact (name ^ "_def"));
       assert (quote name ^ " was installed as an abbreviation")
         (not (is_abbreviation name));
       assert (quote name ^ " does not have one code equation")
         (length (executable_equations name) = 1))

    fun check_abbreviation name =
      (assert (quote name ^ " unexpectedly has a _def fact")
         (not (has_fact (name ^ "_def")));
       assert (quote name ^ " was not installed as an abbreviation")
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

    val abbreviation_proposition =
      Thm.prop_of
        (Proof_Context.get_thm ctxt "typed_flags_abbrev_client_def")
    val abbreviation_name = constant_name "typed_flags_001"
    val _ =
      assert "abbreviation survived in a checked client term"
        (not
          (Term.exists_subterm
            (fn Const (name, _) => name = abbreviation_name
              | _ => false)
            abbreviation_proposition))
  in
    val _ = ()
  end
\<close>


section\<open> Exact expression and function shape \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun definition_rhs name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals
      |> #2

    val expression = definition_rhs "typed_heterogeneous"
    val function = definition_rhs "typed_function_common"
    val expression_type =
      "nat \<Rightarrow> bool \<Rightarrow> " ^
      "(unit, nat \<times> bool, unit, unit, unit, unit) expression"
    val function_type =
      "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
    val expected_expression =
      Syntax.check_term ctxt
        (Type.constraint (Syntax.read_typ ctxt expression_type)
          (Syntax.parse_term ctxt
            "(\<lambda>(number :: nat) (flag :: bool). \<lbrakk> \<llangle>(number, flag)\<rrangle> \<rbrakk>)"))
    val expected_function =
      Syntax.check_term ctxt
        (Type.constraint (Syntax.read_typ ctxt function_type)
          (Syntax.parse_term ctxt
            "(\<lambda>(item :: nat). FunctionBody \<lbrakk> item \<rbrakk>)"))

    fun count_constant expected =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)

    val _ =
      if Term.aconv (expression, expected_expression) then ()
      else error "typed urust_expr: expression lambda shape changed"
    val _ =
      if Term.aconv (function, expected_function) then ()
      else error "typed urust_expr: function lambda shape changed"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close>
          expression 0 = 0
      then ()
      else error "typed urust_expr: expression gained a FunctionBody wrapper"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close>
          function 0 = 1
      then ()
      else error "typed urust_expr: function wrapper count changed"
  in
    val _ = ()
  end
\<close>


section\<open> Migration-sensitive typed expressions \<close>

declare [[urust_conformance_check = true]]

urust_expr typed_boolean_negation ::
  \<open>bool \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> !value \<close>
  with_args value

urust_expr typed_word_negation ::
  \<open>'a::len word \<Rightarrow>
    ('s, 'a word, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> !value \<close>
  with_args value

urust_expr typed_bound_negation ::
  \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> let value = \<epsilon>\<open>source\<close>; !value \<close>
  with_args source

urust_expr typed_indexing ::
  \<open>nat list \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> values[index] \<close>
  with_args values index

urust_expr typed_abort_sequence ::
  \<open>'abort abort \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> \<epsilon>\<open>abort reason\<close>; \<epsilon>\<open>tail\<close> \<close>
  with_args reason tail

urust_expr typed_panic_sequence ::
  \<open>String.literal \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  \<open> panic!(message); \<epsilon>\<open>tail\<close> \<close>
  with_args message tail

definition typed_channel_get :: \<open>nat \<Rightarrow> nat option\<close>
  where \<open>typed_channel_get state = Some state\<close>

definition typed_channel_put :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>typed_channel_put value state = value + state\<close>

urust_expr typed_channel_inference ::
  \<open>(nat, unit, unit, 'abort, 'i, 'o) expression\<close>
  \<open>
    if let Some(value) = \<epsilon>\<open>get typed_channel_get\<close> {
      \<epsilon>\<open>put (typed_channel_put value)\<close>
    }
  \<close>

urust_expr typed_captured_nil ::
  \<open>
    (nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow>
    tnil \<Rightarrow>
    (nat \<Rightarrow> bool \<Rightarrow>
      (nat, nat \<times> bool, unit, unit, unit, unit) expression) \<Rightarrow>
    (nat, nat \<times> bool, unit, unit, unit, unit) expression
  \<close>
  \<open>
    let (left, right) =
      \<epsilon>\<open>get (\<lambda>state. (f state, g state, nil))\<close>;
    \<epsilon>\<open>continuation left right\<close>
  \<close>
  with_args f g nil continuation

thm typed_boolean_negation_conformance
thm typed_word_negation_conformance
thm typed_bound_negation_conformance
thm typed_indexing_conformance
thm typed_abort_sequence_conformance
thm typed_panic_sequence_conformance
thm typed_channel_inference_conformance
thm typed_captured_nil_conformance


section\<open> Rejections, positions, and recovery \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val file = "urust-typed-api-rejection"
    val type_pos = Position.make0 3 30 0 "" file ""
    val arguments_pos = Position.make0 5 50 0 "" file ""
    val source_pos = Position.make0 7 70 0 "" file ""

    fun fail message =
      error ("typed elaboration rejection audit: " ^ message)

    fun source text =
      Parser_Lex_Util.positioned_content_source text source_pos

    fun argument line offset name =
      (name, Position.make0 line offset 0 "" file "")

    fun elaborate kind raw_type arguments body =
      URust_Command.elaborate ctxt
        {kind = kind,
         source = source body,
         arguments = arguments,
         arguments_pos = arguments_pos,
         declared_type = Option.map (fn typ => (typ, type_pos)) raw_type}

    fun rejection_message label action =
      (case Exn.result action () of
         Exn.Res term =>
           fail
             (label ^ " unexpectedly elaborated as " ^
               Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)

    fun expect_rejection label expected action =
      let val message = rejection_message label action in
        if String.isSubstring expected message then ()
        else
          fail
            (label ^ " reported " ^ quote message ^
              " instead of containing " ^ quote expected)
      end

    fun expect_positioned_rejection label expected lines action =
      let
        val message = rejection_message label action
        val has_expected = String.isSubstring expected message
        val has_file = String.isSubstring file message
        val has_lines =
          forall
            (fn line =>
              String.isSubstring ("line " ^ string_of_int line) message)
            lines
      in
        if has_expected andalso has_file andalso has_lines then ()
        else fail (label ^ " lost its expected position: " ^ quote message)
      end

    val expression_type =
      "(unit, nat, unit, unit, unit, unit) expression"
    val unary_expression_type =
      "nat \<Rightarrow> " ^ expression_type
    val binary_expression_type =
      "nat \<Rightarrow> bool \<Rightarrow> " ^ expression_type
    val function_type =
      "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"

    val _ =
      expect_positioned_rejection
        "missing function type" "requires a declared type" [7]
        (fn () =>
          elaborate URust_Command.Function NONE [] "()")
    val _ =
      expect_positioned_rejection
        "wrong function terminal" "result type must be function_body" [3]
        (fn () =>
          elaborate URust_Command.Function
            (SOME unary_expression_type)
            [argument 11 110 "item"] "item")
    val _ =
      expect_positioned_rejection
        "too few expression arguments" "expects 2 arguments" [5]
        (fn () =>
          elaborate URust_Command.Expression
            (SOME binary_expression_type)
            [argument 13 130 "number"] "number")
    val _ =
      expect_positioned_rejection
        "too many expression arguments" "expects 1 argument" [17]
        (fn () =>
          elaborate URust_Command.Expression
            (SOME unary_expression_type)
            [argument 15 150 "item", argument 17 170 "extra"] "item")
    val _ =
      expect_rejection
        "function argument count" "expects 1 parameter"
        (fn () =>
          elaborate URust_Command.Function
            (SOME function_type) [] "0")
    val _ =
      expect_positioned_rejection
        "duplicate typed arguments" "duplicate argument" [19, 23]
        (fn () =>
          elaborate URust_Command.Expression
            (SOME binary_expression_type)
            [argument 19 190 "same", argument 23 230 "same"] "same")
    val _ =
      expect_positioned_rejection
        "wildcard typed argument" "name `_` is not allowed" [29]
        (fn () =>
          elaborate URust_Command.Expression
            (SOME unary_expression_type)
            [argument 29 290 "_"] "0")
    val _ =
      expect_rejection
        "argument type mismatch" "Clash of types"
        (fn () =>
          elaborate URust_Command.Expression
            (SOME unary_expression_type)
            [argument 31 310 "item"] "item == true")
    val _ =
      expect_rejection
        "result type mismatch" "Clash of types"
        (fn () =>
          elaborate URust_Command.Expression
            (SOME "(unit, bool, unit, unit, unit, unit) expression")
            [] "\<llangle>1 :: nat\<rrangle>")
    val _ =
      expect_positioned_rejection
        "malformed declaration type" "syntax" [3]
        (fn () =>
          elaborate URust_Command.Expression
            (SOME "nat \<Rightarrow>") [] "()")

    val recovered =
      elaborate URust_Command.Expression
        (SOME unary_expression_type)
        [argument 37 370 "item"] "item"
    val _ =
      if fastype_of recovered =
          Syntax.read_typ ctxt unary_expression_type
      then ()
      else fail "successful elaboration did not recover after failures"
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    val unit_source = Symbol.open_ ^ " () " ^ Symbol.close
    val unit_expression_type =
      Symbol.open_ ^
      "(unit, unit, unit, unit, unit, unit) expression" ^
      Symbol.close
    val unary_expression_type =
      Symbol.open_ ^
      "nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression" ^
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
          else error "typed command audit: expected exactly one transition"
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun recover () =
      let
        val index = !serial
        val _ = serial := index + 1
      in
        ignore
          (run_command ("typed-command-recovery-" ^ string_of_int index)
            ("urust_expr typed_command_recovered_" ^
              string_of_int index ^ " :: " ^ unit_expression_type ^
              " " ^ unit_source) ())
      end

    fun assert_rejected source_name command_text =
      (case Exn.result (run_command source_name command_text) () of
         Exn.Res _ =>
           error
             ("typed command was unexpectedly accepted" ^
               Position.here (Position.file source_name))
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message = Runtime.exn_message exn
               val _ =
                 if String.isSubstring source_name message then ()
                 else
                   error
                     ("typed command diagnostic lost its source position:\n" ^
                       message)
             in recover () end)

    val _ =
      assert_rejected "typed-malformed-type"
        ("urust_expr typed_bad_type :: " ^
          Symbol.open_ ^ "nat \<Rightarrow>" ^ Symbol.close ^
          " " ^ unit_source)
    val _ =
      assert_rejected "typed-misplaced-type"
        ("urust_expr typed_misplaced_type " ^ unit_source ^
          " :: " ^ unit_expression_type)
    val _ =
      assert_rejected "typed-duplicate-arguments"
        ("urust_expr typed_duplicate_arguments :: " ^
          Symbol.open_ ^
          "nat \<Rightarrow> nat \<Rightarrow> " ^
          "(unit, nat, unit, unit, unit, unit) expression" ^
          Symbol.close ^ " " ^ unit_source ^
          " with_args item item")
    val _ =
      assert_rejected "typed-wildcard-argument"
        ("urust_expr typed_wildcard_argument :: " ^
          unary_expression_type ^ " " ^ unit_source ^
          " with_args _")
    val _ =
      assert_rejected "typed-missing-argument"
        ("urust_expr typed_missing_argument :: " ^
          unary_expression_type ^ " " ^ unit_source)
  in
    val _ = ()
  end
\<close>


section\<open> Typed binder markup and entity identity \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val file = "urust-typed-binder-markup"
    val document_id = "urust-typed-binder-markup"
    val first_definition =
      Position.make0 11 100 0 "" file document_id
    val second_definition =
      Position.make0 11 110 0 "" file document_id
    val body_text =
      "\<llangle>(first, second, first)\<rrangle>"
    val body_start =
      Position.make0 13 200 0 "" file document_id
    val body_source =
      Parser_Lex_Util.positioned_content_source body_text body_start
    val captured =
      Synchronized.var "urust_typed_binder_markup" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured (append chunks)

    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                URust_Command.elaborate ctxt
                  {kind = URust_Command.Expression,
                   source = body_source,
                   arguments =
                     [("first", first_definition),
                      ("second", second_definition)],
                   arguments_pos = Position.line_file 9 file,
                   declared_type =
                     SOME
                       ("nat \<Rightarrow> bool \<Rightarrow> " ^
                        "(unit, nat \<times> bool \<times> nat, " ^
                        "unit, unit, unit, unit) expression",
                        Position.line_file 7 file)}) ())
          ())

    fun collect (XML.Text _) result = result
      | collect (XML.Elem (markup, body)) result =
          fold collect body (markup :: result)
    val markup =
      fold collect
        (maps YXML.parse_body (Synchronized.value captured)) []

    fun find_from needle offset =
      if offset + size needle > size body_text then
        error ("typed binder markup audit: missing " ^ quote needle)
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

    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
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
               ("typed binder markup audit: entity markup changed at" ^
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
      if has_markup Markup.typingN first_definition andalso
         has_markup Markup.typingN second_definition
      then ()
      else error "typed binder markup audit: typed definitions lost tooltips"
    val _ =
      if first_id <> second_id then ()
      else error "typed binder markup audit: arguments reused an entity ID"
    val _ =
      if entity_id Markup.refN first_reference_one = first_id andalso
         entity_id Markup.refN first_reference_two = first_id
      then ()
      else error "typed binder markup audit: first references lost navigation"
    val _ =
      if entity_id Markup.refN second_reference = second_id then ()
      else error "typed binder markup audit: second reference lost navigation"
  in
    val _ = ()
  end
\<close>


section\<open> Public facade audit \<close>

ML_val\<open>
  local
    val implementation_path =
      Resources.master_directory \<^theory> +
        Path.explode "../Micro_Rust_Parser_Impl/Parser_Impl_Command.thy"
    val implementation = File.read implementation_path
    val structure_marker =
      "structure URust_Command :> URUST_COMMAND ="
    val before_structure =
      (case first_field structure_marker implementation of
         SOME (prefix, suffix) =>
           if is_some (first_field structure_marker suffix)
           then error "uRust facade audit: command structure is duplicated"
           else prefix
       | NONE => error "uRust facade audit: command structure is missing")
    val signature_marker = "signature URUST_COMMAND ="
    val signature_text =
      (case first_field signature_marker before_structure of
         SOME (_, signature) =>
           if is_some (first_field signature_marker signature)
           then error "uRust facade audit: command signature is duplicated"
           else signature
       | NONE => error "uRust facade audit: command signature is missing")
    val exported_values =
      split_lines signature_text
      |> filter (String.isPrefix "  val ")

    val _ =
      if exported_values = ["  val elaborate:"] then ()
      else
        error
          ("uRust facade audit: exported value list changed: " ^
            commas_quote exported_values)
    val _ =
      if String.isSubstring
          "datatype elaboration_kind = Expression | Function"
          signature_text
      then ()
      else error "uRust facade audit: elaboration_kind is not exported"
    val _ =
      List.app
        (fn removed =>
          if String.isSubstring removed implementation then
            error
              ("uRust facade audit: compatibility alias remains: " ^
                quote removed)
          else ())
        ["elab_urust", "elab_urust_with_args", "elab_urust_fun"]
  in
    val _ = ()
  end
\<close>

end
