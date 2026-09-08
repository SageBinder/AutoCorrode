theory Parser_Test_Fun_Conformance
  imports Parser_Test_Utils Conformance_Corpus
begin

declare [[urust_conformance_check = true]]

section\<open> Definition parity \<close>

urust_fun parsed_answer ::
  \<open>('s, 32 word, 'abort, 'i, 'o) function_body\<close>
  ()
  \<open> \<llangle>42 :: 32 word\<rrangle> \<close>

thm parsed_answer_conformance

urust_fun parsed_inc ::
  \<open>32 word \<Rightarrow> ('s, 32 word, 'abort, 'i, 'o) function_body\<close>
  (x)
  \<open> x + \<llangle>1 :: 32 word\<rrangle> \<close>

urust_fun parsed_add3 ::
  \<open>
    32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
    ('s, 32 word, 'abort, 'i, 'o) function_body
  \<close>
  (a, b, c)
  \<open> a + b + c \<close>

urust_fun parsed_is_zero ::
  \<open>32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close>
  (x)
  \<open> x == \<llangle>0 :: 32 word\<rrangle> \<close>

urust_fun parsed_safe_div ::
  \<open>
    32 word \<Rightarrow> 32 word \<Rightarrow>
    ('s, (32 word, unit) result, 'abort, 'i, 'o) function_body
  \<close>
  (a, b)
  \<open>
    if b == \<llangle>0 :: 32 word\<rrangle> {
      Err(())
    } else {
      Ok(a / b)
    }
  \<close>

urust_fun parsed_discard ::
  \<open>32 word \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
  (x)
  \<open> () \<close>


section\<open> Signature surface \<close>

urust_fun fun_heterogeneous ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow>
    ('s, nat * bool * 32 word, 'abort, 'i, 'o) function_body\<close>
  (number, flag, word)
  \<open> \<llangle>(number, flag, word)\<rrangle> \<close>

urust_fun fun_polymorphic ::
  \<open>'a \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close>
  (item)
  \<open> item \<close>

urust_fun fun_sort_constrained ::
  \<open>'a::len word \<Rightarrow>
    ('s, 'a word, 'abort, 'i, 'o) function_body\<close>
  (item)
  \<open> item \<close>

urust_fun fun_type_placeholders ::
  \<open>_ \<Rightarrow> (_, _, _, _, _) function_body\<close>
  (item)
  \<open> item \<close>

urust_fun fun_higher_order ::
  \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>
    ('s, nat, 'abort, 'i, 'o) function_body\<close>
  (f, item)
  \<open> \<llangle>f item\<rrangle> \<close>

urust_fun fun_nested_result ::
  \<open>('s, (nat option, (bool, unit) result) result,
    'abort, 'i, 'o) function_body\<close>
  ()
  \<open> Ok(Some(\<llangle>1 :: nat\<rrangle>)) \<close>

urust_fun fun_explicit_prompt_output ::
  \<open>nat \<Rightarrow>
    (unit, nat, unit, unit prompt, unit prompt_output) function_body\<close>
  (item)
  \<open> item \<close>

term fun_heterogeneous
term fun_polymorphic
term fun_sort_constrained
term fun_type_placeholders
term fun_higher_order
term fun_nested_result
term fun_explicit_prompt_output


section\<open> Argument-list boundaries \<close>

urust_fun fun_zero_arguments ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

urust_fun fun_one_argument ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fun fun_trailing_comma ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, nat * bool, unit, unit, unit) function_body\<close>
  (item, flag,)
  \<open> \<llangle>(item, flag)\<rrangle> \<close>

urust_fun fun_multiline_arguments ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body\<close>
  (
    number,
    flag,
    word,
  )
  \<open> if flag { word } else { \<llangle>of_nat number\<rrangle> } \<close>

urust_fun fun_sixteen_arguments ::
  \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body
  \<close>
  (
    p01, p02, p03, p04, p05, p06, p07, p08,
    p09, p10, p11, p12, p13, p14, p15, p16
  )
  \<open>
    \<llangle>
      p01 + p02 + p03 + p04 + p05 + p06 + p07 + p08 +
      p09 + p10 + p11 + p12 + p13 + p14 + p15 + p16
    \<rrangle>
  \<close>


section\<open> Ambient binding and scope \<close>

urust_fun fun_plain_parameter ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fun fun_value_antiquotation ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<llangle>item + 1\<rrangle> \<close>

urust_fun fun_expression_antiquotation ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<epsilon>\<open>literal (item + 1)\<close> \<close>

urust_fun fun_parameter_call ::
  \<open>
    (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
    nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body
  \<close>
  (callee, item)
  \<open> callee(item) \<close>

urust_fun fun_parameter_in_match_guard ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    match Some(item) {
      Some(inner) if inner == item \<Rightarrow> inner,
      _ \<Rightarrow> item
    }
  \<close>

urust_fun fun_parameter_in_loop ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) {
      let observed = item;
      ()
    }
    item
  \<close>

urust_fun fun_parameter_in_closure ::
  \<open>nat \<Rightarrow>
    (unit, nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body,
      unit, unit, unit) function_body\<close>
  (outer)
  \<open> |inner| \<llangle>outer + inner\<rrangle> \<close>

datatype fun_struct_fixture = FunStructFixture nat bool

definition fun_struct_fixture_lift ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, fun_struct_fixture, unit, unit, unit) function_body\<close>
  where \<open>fun_struct_fixture_lift \<equiv> lift_fun2 FunStructFixture\<close>

micro_rust_notation (call) fun_struct_fixture_lift ("FunStructFixture")

urust_fun fun_parameter_in_struct ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, fun_struct_fixture, unit, unit, unit) function_body\<close>
  (item, flag)
  \<open> FunStructFixture { item: item, flag: flag } \<close>

urust_fun fun_nested_let_shadow ::
  \<open>nat \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  (item)
  \<open> let item = true; item \<close>

urust_fun fun_nested_pattern_shadow ::
  \<open>nat \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    let (item, retained) = (true, \<llangle>item\<rrangle>);
    item
  \<close>

urust_fun fun_closure_shadow ::
  \<open>bool \<Rightarrow>
    (unit, nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body,
      unit, unit, unit) function_body\<close>
  (item)
  \<open> |item| \<llangle>item :: nat\<rrangle> \<close>

context
  fixes item :: bool
begin

urust_fun fun_parameter_shadows_context ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<llangle>item :: nat\<rrangle> \<close>

end

urust_fun fun_distinct_heterogeneous ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> String.literal \<Rightarrow>
    (unit, nat * bool * String.literal, unit, unit, unit) function_body\<close>
  (number, flag, message)
  \<open> \<llangle>(number, flag, message)\<rrangle> \<close>


section\<open> Role-specific notation precedence \<close>

definition fun_registered_literal :: nat
  where \<open>fun_registered_literal = 99\<close>

definition fun_registered_call ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open>fun_registered_call \<equiv> lift_fun1 (\<lambda>x. x + 10)\<close>

datatype_record fun_field_record =
  fun_field_value :: nat
micro_rust_record fun_field_record
  (fun_field_value = "funFieldCollision")

micro_rust_notation (literal) fun_registered_literal ("funCollision")
micro_rust_notation (call) fun_registered_call ("funCollision")

urust_fun fun_registered_call_wins ::
  \<open>
    (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
    nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body
  \<close>
  (funCollision, item)
  \<open> funCollision(item) \<close>

urust_fun fun_registered_field_wins ::
  \<open>fun_field_record \<Rightarrow> (fun_field_record, nat) lens \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body\<close>
  (item, funFieldCollision)
  \<open> item.funFieldCollision \<close>

text\<open>
The checked declarations prove frontend conformance. These additional shape lemmas are necessary to
pin the stronger role-specific property: call and field notation win over same-named parameters.
\<close>

lemma fun_registered_call_wins_shape:
  \<open>
    fun_registered_call_wins ignored value =
      FunctionBody \<lbrakk> funCollision(value) \<rbrakk>
  \<close>
  unfolding fun_registered_call_wins_def by (rule refl)

lemma fun_registered_field_wins_shape:
  \<open>
    fun_registered_field_wins value ignored =
      FunctionBody \<lbrakk> \<llangle>value\<rrangle>.funFieldCollision \<rbrakk>
  \<close>
  unfolding fun_registered_field_wins_def by (rule refl)


section\<open> Isabelle declaration integration \<close>

context
begin

qualified urust_fun qualified_identity ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

end

locale fun_command_locale =
  fixes offset :: nat
begin

urust_fun local_add ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<llangle>item + offset\<rrangle> \<close>

end

value \<open>case parsed_inc (1 :: 32 word) of FunctionBody _ \<Rightarrow> True\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val constant = \<^const_name>\<open>parsed_inc\<close>
    val definition = Proof_Context.get_thm ctxt "parsed_inc_def"
    val certificate = Code.get_cert ctxt [] constant
    val (_, equations) = Code.equations_of_cert thy certificate
    val executable =
      map_filter
        (fn (_, (SOME theorem, _)) => SOME theorem
          | _ => NONE)
        (the equations)
    val simps = map #2 (#simps (Raw_Simplifier.dest_ss (simpset_of ctxt)))
    val _ =
      if length executable = 1 then ()
      else error "urust_fun: expected one default code equation"
    val _ =
      if Thm.equiv_thm thy
          (the_single executable, Axclass.unoverload ctxt definition)
      then ()
      else error "urust_fun: code equation differs from _def"
    val _ =
      if exists (Thm.equiv_thm thy o pair definition) simps
      then error "urust_fun: generated definition entered the global simp set"
      else ()
  in
    val _ = ()
  end
\<close>


section\<open> Focused elaboration and rejection matrix \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val file = "urust-fun-rejection-audit"

    fun fail message = error ("urust_fun rejection audit: " ^ message)

    fun positioned line offset text =
      Parser_Lex_Util.positioned_content_source text
        (Position.make0 line offset 0 "" file "")

    fun parameter line offset name =
      (name, Position.make0 line offset 0 "" file "")

    fun elaborate raw_type parameters body =
      Parser_Test_Elaboration.function ctxt
        {raw_type =
           (raw_type, Position.make0 3 30 0 "" file ""),
         parameters = parameters,
         parameters_pos = Position.make0 5 50 0 "" file "",
         body = positioned 7 70 body}

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
        else fail (label ^ " lost its expected source position: " ^ quote message)
      end

    val body_type = "(unit, nat, unit, unit, unit) function_body"
    val unary_type = "nat \<Rightarrow> " ^ body_type

    val _ =
      expect_rejection "duplicate parameters" "duplicate parameter"
        (fn () =>
          elaborate
            ("nat \<Rightarrow> nat \<Rightarrow> " ^ body_type)
            [parameter 11 110 "value", parameter 13 130 "value"]
            "value")
    val _ =
      expect_rejection "wildcard parameter" "name `_` is not allowed"
        (fn () =>
          elaborate unary_type [parameter 17 170 "_"] "0")
    val _ =
      expect_rejection "too few names" "expects 2 parameters"
        (fn () =>
          elaborate
            ("nat \<Rightarrow> nat \<Rightarrow> " ^ body_type)
            [parameter 19 190 "left"] "left")
    val _ =
      expect_rejection "too many names" "expects 1 parameter"
        (fn () =>
          elaborate unary_type
            [parameter 23 230 "left", parameter 25 250 "right"]
            "left")
    val _ =
      expect_rejection "name for nullary type" "expects 0 parameters"
        (fn () =>
          elaborate body_type [parameter 27 270 "value"] "0")
    val _ =
      expect_rejection "missing curried name" "expects 1 parameter"
        (fn () => elaborate unary_type [] "0")
    val _ =
      expect_rejection "non-function-body result"
        "result type must be function_body"
        (fn () => elaborate "nat \<Rightarrow> nat" [parameter 31 310 "x"] "x")
    val _ =
      expect_rejection "body/result mismatch" "Clash of types"
        (fn () => elaborate unary_type [parameter 33 330 "x"] "true")
    val _ =
      expect_rejection "invalid parameter use" "Clash of types"
        (fn () => elaborate unary_type [parameter 35 350 "x"] "x + true")
    val _ =
      expect_rejection "unresolved body name" "unresolved body name"
        (fn () => elaborate body_type [] "missing_body_name")
    val _ =
      expect_rejection "empty body" "empty function body"
        (fn () => elaborate body_type [] "")
    val _ =
      expect_rejection "malformed body" "Parse Error"
        (fn () => elaborate unary_type [parameter 41 410 "x"] "x +")

    val _ =
      expect_positioned_rejection
        "positioned duplicate" "duplicate parameter" [43, 47]
        (fn () =>
          elaborate
            ("nat \<Rightarrow> nat \<Rightarrow> " ^ body_type)
            [parameter 43 430 "same", parameter 47 470 "same"]
            "same")
    val _ =
      expect_positioned_rejection
        "positioned too few names" "expects 2 parameters" [5]
        (fn () =>
          elaborate
            ("nat \<Rightarrow> nat \<Rightarrow> " ^ body_type)
            [parameter 49 490 "only"] "only")
    val _ =
      expect_positioned_rejection
        "positioned too many names" "expects 1 parameter" [61]
        (fn () =>
          elaborate unary_type
            [parameter 59 590 "left", parameter 61 610 "extra"]
            "left")
    val _ =
      expect_positioned_rejection
        "positioned result type" "result type must be function_body" [3]
        (fn () =>
          elaborate "nat \<Rightarrow> nat" [parameter 63 630 "item"] "item")

    val _ =
      List.app
        (fn (label, expected, action) =>
          expect_rejection label expected action)
        [("recovery duplicate", "duplicate parameter",
          fn () =>
            elaborate
              ("nat \<Rightarrow> nat \<Rightarrow> " ^ body_type)
              [parameter 51 510 "x", parameter 53 530 "x"] "x"),
         ("recovery malformed", "Parse Error",
          fn () =>
            elaborate unary_type [parameter 55 550 "x"] "if")]

    val recovered =
      elaborate unary_type [parameter 57 570 "x"] "\<llangle>x + 1\<rrangle>"
    val _ =
      if fastype_of recovered = Syntax.read_typ ctxt unary_type then ()
      else fail "successful elaboration did not recover after independent failures"
  in
    val _ = ()
  end
\<close>


section\<open> Generated term shape \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val parameter_start =
      Position.make0 11 100 0 "" "" "urust-fun-shape"
    val body_start =
      Position.make0 13 200 0 "" "" "urust-fun-shape"
    val raw_type =
      "nat \<Rightarrow> bool \<Rightarrow> " ^
      "(unit, nat * bool, unit, unit, unit) function_body"
    val parameters =
      [("first", parameter_start),
       ("second", Position.symbol_explode "first, " parameter_start)]
    val body =
      Parser_Lex_Util.positioned_content_source
        "\<llangle>(first, second)\<rrangle>" body_start
    val term =
      Parser_Test_Elaboration.function ctxt
        {raw_type = (raw_type, Position.line 9),
         parameters = parameters,
         parameters_pos = parameter_start,
         body = body}
    val (formals, stripped) = Term.strip_abs term

    fun count_constant expected =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)

    val expected =
      Syntax.check_term ctxt
        (Type.constraint (Syntax.read_typ ctxt raw_type)
          (Syntax.parse_term ctxt
            "(\<lambda>(first::nat) (second::bool). \
            \FunctionBody \<lbrakk> \<llangle>(first, second)\<rrangle> \<rbrakk>)"))

    val _ =
      if map #2 formals = [HOLogic.natT, HOLogic.boolT] then ()
      else error "urust_fun shape audit: typed abstraction order changed"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close> term 0 = 1 then ()
      else error "urust_fun shape audit: expected exactly one FunctionBody"
    val _ =
      if count_constant \<^const_name>\<open>urust_dispatch\<close> term 0 = 0 then ()
      else error "urust_fun shape audit: unresolved parser dispatch escaped"
    val _ =
      if Term.aconv (term, expected) then ()
      else error "urust_fun shape audit: hand-written frontend shape changed"
    val _ =
      (case stripped of
         Const (name, _) $ _ =>
           if name = \<^const_name>\<open>FunctionBody\<close> then ()
           else error "urust_fun shape audit: body wrapper changed"
       | _ => error "urust_fun shape audit: body wrapper disappeared")
  in
    val _ = ()
  end
\<close>


section\<open> Parameter markup and navigation \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val file = "urust-fun-markup-audit"
    val document_id = "urust-fun-markup-audit"
    val first_definition =
      Position.make0 11 100 0 "" file document_id
    val second_definition =
      Position.make0 11 110 0 "" file document_id
    val body_text =
      "let first = first; \<llangle>(first, second, second)\<rrangle>"
    val body_start =
      Position.make0 13 200 0 "" file document_id
    val body_source =
      Parser_Lex_Util.positioned_content_source body_text body_start
    val captured = Synchronized.var "urust_fun_markup" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured (append chunks)

    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.function ctxt
                  {raw_type =
                     ("nat \<Rightarrow> bool \<Rightarrow> " ^
                      "(unit, nat * bool * bool, unit, unit, unit) function_body",
                      Position.line_file 7 file),
                   parameters =
                     [("first", first_definition),
                      ("second", second_definition)],
                   parameters_pos = Position.line_file 9 file,
                   body = body_source}) ())
          ())

    fun collect (XML.Text _) result = result
      | collect (XML.Elem (markup, body)) result =
          fold collect body (markup :: result)
    val markup =
      fold collect
        (maps YXML.parse_body (Synchronized.value captured)) []

    fun find_from needle offset =
      if offset + size needle > size body_text then
        error ("urust_fun markup audit: missing " ^ quote needle)
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
               ("urust_fun markup audit: binder entity markup changed at" ^
                 Position.here position ^ " with IDs [" ^
                 commas ids ^ "]"))
      end

    val (let_offset, let_definition) = token_position "first" 0
    val (parameter_ref_offset, parameter_reference) =
      token_position "first" (let_offset + size "first")
    val (_, let_reference) =
      token_position "first" (parameter_ref_offset + size "first")
    val (second_ref_offset, second_reference_one) =
      token_position "second" 0
    val (_, second_reference_two) =
      token_position "second" (second_ref_offset + size "second")

    val first_parameter_id = entity_id Markup.defN first_definition
    val second_parameter_id = entity_id Markup.defN second_definition
    val let_id = entity_id Markup.defN let_definition
    val _ =
      if first_parameter_id <> second_parameter_id andalso
         first_parameter_id <> let_id
      then ()
      else error "urust_fun markup audit: definitions reused entity IDs"
    val _ =
      if entity_id Markup.refN parameter_reference = first_parameter_id
      then ()
      else error "urust_fun markup audit: shadowing RHS lost parameter navigation"
    val _ =
      if entity_id Markup.refN let_reference = let_id
      then ()
      else error "urust_fun markup audit: let body did not target the shadow"
    val _ =
      if entity_id Markup.refN second_reference_one = second_parameter_id andalso
         entity_id Markup.refN second_reference_two = second_parameter_id
      then ()
      else error "urust_fun markup audit: antiquotation references lost navigation"
  in
    val _ = ()
  end
\<close>

end
