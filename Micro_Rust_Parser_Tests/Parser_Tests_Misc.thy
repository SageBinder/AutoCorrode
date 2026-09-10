(* Consolidated parser command, rejection, regression, logging, and term-hook tests. *)

theory Parser_Tests_Misc
  imports
    Parser_Tests_Improvements
    Struct_Ambiguity_Left
    Struct_Ambiguity_Right
    Micro_Rust_Std_Lib.StdLib_Logging
    Micro_Rust_Parser_Impl.Parser_Term_Hook
  keywords
    "urust_expr_rejects" :: thy_decl
    and "new_urust_rejects" :: thy_decl
begin

chapter\<open>Parser facade\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

section\<open> Parser facade smoke test \<close>

urust_expr smoke_num  \<open> 42 \<close>
urust_expr smoke_sfx  \<open> 1_u32 \<close>
urust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def

ML_val\<open>
  val _ =
    if Global_Theory.defined_fact \<^theory> "smoke_num_conformance"
    then error "default urust_conformance_check unexpectedly generated a theorem"
    else ()
\<close>


chapter\<open>Typed expression and shared command API\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

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
  (item)
  \<open> item \<close>

urust_expr typed_heterogeneous ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, nat \<times> bool, unit, unit, unit, unit) expression\<close>
  (number, flag)
  \<open> \<llangle>(number, flag)\<rrangle> \<close>

urust_expr typed_higher_order ::
  \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (f, item)
  \<open> \<llangle>f item\<rrangle> \<close>

urust_expr typed_polymorphic ::
  \<open>'a \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
  (item)
  \<open> item \<close>

urust_expr typed_sort_constrained ::
  \<open>'a::len word \<Rightarrow>
    ('s, 'a word, 'r, 'abort, 'i, 'o) expression\<close>
  (item)
  \<open> item \<close>

urust_expr typed_placeholders ::
  \<open>_ \<Rightarrow> (_, _, _, _, _, _) expression\<close>
  (item)
  \<open> item \<close>

text\<open>
A declaration ending in \<open>function_body\<close> selects function elaboration through the same
\<open>urust_expr\<close> command and therefore wraps the checked body exactly once.
\<close>

urust_expr typed_function_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

thm typed_closed_conformance
thm typed_contextual_conformance
thm typed_heterogeneous_conformance
thm typed_higher_order_conformance
thm typed_polymorphic_conformance
thm typed_sort_constrained_conformance
thm typed_placeholders_conformance
thm typed_function_common_conformance


section\<open> Anonymous declarations \<close>

text\<open>
The dummy declaration name elaborates and optionally proves conformance without installing a
constant, definition, abbreviation, or code equation. Both command facades use an invented
source-position name for the conformance fact and informational output only.
\<close>

urust_expr [conformance_check = true] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> item \<close>

urust_fn [conformance_check = true] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr [abbrev = true, conformance_check = false] _
  \<open> () \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val constants =
      Proof_Context.consts_of ctxt
      |> Consts.dest
      |> #constants
      |> map #1
    val facts =
      Global_Theory.facts_of thy
      |> Facts.dest_static false
           (map Global_Theory.facts_of (Theory.parents_of thy))
      |> map #1

    fun anonymous_base command name =
      String.isPrefix (command ^ "_anonymous_")
        (Long_Name.base_name name)
    fun anonymous_conformance command name =
      anonymous_base command name andalso
      String.isSuffix "_conformance" (Long_Name.base_name name)

    val _ =
      if not (exists (anonymous_base "urust_expr") constants) andalso
         not (exists (anonymous_base "urust_fn") constants)
      then ()
      else error "anonymous uRust command registered a constant"
    val expression_facts =
      filter (anonymous_conformance "urust_expr") facts
    val function_facts =
      filter (anonymous_conformance "urust_fn") facts
    val _ =
      if length expression_facts = 1 andalso
         length function_facts = 1
      then ()
      else
        error
          ("anonymous uRust conformance fact count changed: " ^
            string_of_int (length expression_facts) ^ " expression, " ^
            string_of_int (length function_facts) ^ " function")
  in
    val _ = ()
  end
\<close>


section\<open> Definitions, abbreviations, flags, locales, and against \<close>

declare [[urust_conformance_check = false]]

urust_expr
  [conformance_check = false, verbose = 0, abbrev = false]
  typed_flags_000 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, conformance_check = false, verbose = 0]
  typed_flags_001 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbose = 1, abbrev = false, conformance_check = false]
  typed_flags_010 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [conformance_check = false, abbrev = true, verbose = 1]
  typed_flags_011 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbose = 0, conformance_check = true, abbrev = false]
  typed_flags_100 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, verbose = 0, conformance_check = true]
  typed_flags_101 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [conformance_check = true, verbose = 2, abbrev = false]
  typed_flags_110 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbose = 2, abbrev = true, conformance_check = true]
  typed_flags_111 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, conformance_check = true, verbose = 2]
  typed_function_abbrev_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr typed_against ::
  \<open>32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit, unit) expression\<close>
  (operand)
  \<open> operand + 1u32 \<close>
  against \<open> \<lbrakk> operand + 1_u32 \<rbrakk> \<close>

locale typed_expression_locale =
  fixes offset :: nat
begin

urust_expr
  [abbrev = true, conformance_check = true]
  typed_local_add ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> \<llangle>item + offset\<rrangle> \<close>

end

definition typed_ambient_probe :: \<open>'a itself \<Rightarrow> nat\<close>
  where \<open>typed_ambient_probe _ = 0\<close>

locale typed_ambient_tfree_locale =
  fixes ambient_witness :: \<open>'ambient itself\<close>
begin

urust_expr
  [conformance_check = true]
  typed_ambient_tfree_function ::
  \<open>(unit, nat, unit, unit, unit) function_body\<close>
  \<open> \<llangle>typed_ambient_probe TYPE('ambient)\<rrangle> \<close>

thm typed_ambient_tfree_function_conformance

ML_val\<open>
  local
    val ctxt = \<^context>
    val declared_type =
      "(unit, nat, unit, unit, unit) function_body"
    val source =
      Parser_Lex_Util.text_source
        "\<llangle>typed_ambient_probe TYPE('ambient)\<rrangle>"
    val checked =
      URust_Command.elaborate ctxt
        {kind = URust_Command.Function,
         source = source,
         arguments = [],
         arguments_pos = #2 (Input.range_of source),
         declared_type = SOME (declared_type, Position.none)}
    val installed =
      Proof_Context.get_thm ctxt
        "typed_ambient_tfree_function_def"
      |> Thm.prop_of
      |> Logic.dest_equals
      |> #2
    val expected_probe_type =
      Syntax.read_typ ctxt
        "'ambient itself \<Rightarrow> nat"
    val probe_name =
      \<^const_name>\<open>typed_ambient_probe\<close>

    fun probe_types term =
      Term.fold_aterms
        (fn Const (name, T) =>
              if name = probe_name then cons T else I
          | _ => I)
        term []

    fun assert_probe_type label term =
      (case probe_types term of
         [actual] =>
           if actual = expected_probe_type then ()
           else
             error
               ("ambient TFree regression: " ^ label ^
                 " specialized the probe to " ^
                 Syntax.string_of_typ ctxt actual)
       | actual =>
           error
             ("ambient TFree regression: " ^ label ^
               " has " ^ string_of_int (length actual) ^
               " probe occurrences"))

    val _ =
      if null (Variable.add_fixed ctxt checked []) then ()
      else
        error
          "ambient TFree regression: checked term unexpectedly contains a fixed Free"
    val _ =
      if null (Term.add_tfreesT (fastype_of checked) []) then ()
      else
        error
          "ambient TFree regression: complete declaration unexpectedly exposes the ambient type"
    val _ = assert_probe_type "checked term" checked
    val _ = assert_probe_type "installed term" installed
  in
    val _ = ()
  end
\<close>

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
  (operand)
  \<open> !operand \<close>

urust_expr typed_word_negation ::
  \<open>'a::len word \<Rightarrow>
    ('s, 'a word, 'r, 'abort, 'i, 'o) expression\<close>
  (operand)
  \<open> !operand \<close>

urust_expr typed_bound_negation ::
  \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, bool, 'r, 'abort, 'i, 'o) expression\<close>
  (source)
  \<open> let value = \<epsilon>\<open>source\<close>; !value \<close>

urust_expr typed_indexing ::
  \<open>nat list \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'r, 'abort, 'i, 'o) expression\<close>
  (elements, index)
  \<open> elements[index] \<close>

urust_expr typed_abort_sequence ::
  \<open>'abort abort \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  (reason, tail)
  \<open> \<epsilon>\<open>abort reason\<close>; \<epsilon>\<open>tail\<close> \<close>

urust_expr typed_panic_sequence ::
  \<open>String.literal \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  (message, tail)
  \<open> panic!(message); \<epsilon>\<open>tail\<close> \<close>

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
  (f, g, nil, continuation)
  \<open>
    let (left, right) =
      \<epsilon>\<open>get (\<lambda>state. (f state, g state, nil))\<close>;
    \<epsilon>\<open>continuation left right\<close>
  \<close>

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
          Symbol.close ^ " (item, item) " ^ unit_source)
    val _ =
      assert_rejected "typed-wildcard-argument"
        ("urust_expr typed_wildcard_argument :: " ^
          unary_expression_type ^ " (_) " ^ unit_source)
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
         SOME (_, signature_body) =>
           if is_some (first_field signature_marker signature_body)
           then error "uRust facade audit: command signature is duplicated"
           else signature_body
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


chapter\<open>Expression structural audits\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

text\<open>
This direct resolver regression checks that an HOL record uses the record-specific result variant and
contains only its two source-visible fields, rather than generic constructor metadata or a synthetic
extension slot.
\<close>

ML\<open>
val _ =
  let
    val wildcard = URust_AST.P_Wild Position.none
    val fields =
      [URust_AST.SF_Field ("adv_rec_left", Position.none, wildcard),
       URust_AST.SF_Field ("adv_rec_right", Position.none, wildcard)]
    val resolver =
      URust_Resolution.make_constructor_resolver
        \<^context> Position.none
  in
    (case URust_Resolution.resolve_struct_pattern
        \<^context> resolver
        (URust_AST.make_single_path
           ("adv_record_fixture", Position.none), fields) of
       URust_Resolution.Resolved_Record_Struct (record_name, ordered) =>
         if Long_Name.base_name record_name = "adv_record_fixture" andalso length ordered = 2
         then ()
         else error "record struct-pattern metadata has the wrong source-visible fields"
     | URust_Resolution.Resolved_Constructor_Struct _ =>
         error "HOL record resolved through generic constructor metadata")
  end
\<close>

section\<open>Expression term checks\<close>

term \<open>lit_open x y\<close>

section\<open>Registered macro body retention\<close>

ML_val\<open>
  local
    val body =
      Proof_Context.get_thm \<^context> "macro_registered_full_body_def"
      |> Thm.prop_of
      |> Logic.dest_equals
      |> #2
    val marker_count =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = \<^const_name>\<open>macro_registered_body_marker\<close>
              then Integer.add 1
              else I
          | _ => I)
        body 0
  in
    val _ =
      if marker_count = 1 then ()
      else error "registered full-body macro did not retain its marker exactly once"
  end
\<close>


chapter\<open>Function declaration and elaboration audits\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

section\<open>Signature term checks\<close>

term fun_heterogeneous
term fun_polymorphic
term fun_sort_constrained
term fun_type_placeholders
term fun_higher_order
term fun_nested_result
term fun_explicit_prompt_output

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

value \<open>case inc (1 :: 32 word) of FunctionBody _ \<Rightarrow> True\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val constant = \<^const_name>\<open>inc\<close>
    val definition = Proof_Context.get_thm ctxt "inc_def"
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
      else error "urust_fn: expected one default code equation"
    val _ =
      if Thm.equiv_thm thy
          (the_single executable, Axclass.unoverload ctxt definition)
      then ()
      else error "urust_fn: code equation differs from _def"
    val _ =
      if exists (Thm.equiv_thm thy o pair definition) simps
      then error "urust_fn: generated definition entered the global simp set"
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

    fun fail message = error ("urust_fn rejection audit: " ^ message)

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
      else error "urust_fn shape audit: typed abstraction order changed"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close> term 0 = 1 then ()
      else error "urust_fn shape audit: expected exactly one FunctionBody"
    val _ =
      if count_constant \<^const_name>\<open>urust_dispatch\<close> term 0 = 0 then ()
      else error "urust_fn shape audit: unresolved parser dispatch escaped"
    val _ =
      if Term.aconv (term, expected) then ()
      else error "urust_fn shape audit: hand-written frontend shape changed"
    val _ =
      (case stripped of
         Const (name, _) $ _ =>
           if name = \<^const_name>\<open>FunctionBody\<close> then ()
           else error "urust_fn shape audit: body wrapper changed"
       | _ => error "urust_fn shape audit: body wrapper disappeared")
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
        error ("urust_fn markup audit: missing " ^ quote needle)
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
               ("urust_fn markup audit: binder entity markup changed at" ^
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
      else error "urust_fn markup audit: definitions reused entity IDs"
    val _ =
      if entity_id Markup.refN parameter_reference = first_parameter_id
      then ()
      else error "urust_fn markup audit: shadowing RHS lost parameter navigation"
    val _ =
      if entity_id Markup.refN let_reference = let_id
      then ()
      else error "urust_fn markup audit: let body did not target the shadow"
    val _ =
      if entity_id Markup.refN second_reference_one = second_parameter_id andalso
         entity_id Markup.refN second_reference_two = second_parameter_id
      then ()
      else error "urust_fn markup audit: antiquotation references lost navigation"
  in
    val _ = ()
  end
\<close>


chapter\<open>Command options\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

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


chapter\<open>Negative conformance\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

section\<open> The command \<close>

text\<open>
\<open>urust_expr_rejects fidelity source expected\<close> requires both frontends to reject and
checks the new parser's reason. The new-parser-only variant accepts \<open>frontend_accepts\<close> when
the row must prove that the existing frontend accepts, \<open>divergent\<close> for another recorded
acceptance-boundary difference, or \<open>audit\<close> for a custom-parser invariant whose old-frontend
behavior is deliberately not part of the row. The tags are validated locally by this negative-test
command; bracketed comment labels remain explanatory only.
\<close>
ML\<open>
fun negative_frontend_source source = "\<lbrakk> " ^ source ^ " \<rbrakk>"

val _ = Syntax.read_term \<^context> (negative_frontend_source "()")

datatype rejection_tag = Fidelity | FrontendAccepts | Divergent | Audit

fun validate_rejection_tag check_frontend tag =
  (case (check_frontend, tag) of
     (true, Fidelity) => ()
   | (true, _) =>
       error "urust_expr_rejects requires the `fidelity` tag"
   | (false, Fidelity) =>
       error
         "new_urust_rejects requires the `frontend_accepts`, `divergent`, or `audit` tag"
   | (false, _) => ())

fun parse_rejection_tag (name, pos) =
  (case name of
     "fidelity" => Fidelity
   | "frontend_accepts" => FrontendAccepts
   | "divergent" => Divergent
   | "audit" => Audit
   | _ =>
       error
         ("unknown rejection tag " ^ quote name ^
           "; expected `fidelity`, `frontend_accepts`, `divergent`, or `audit`" ^
           Position.here pos))

fun urust_rejects check_frontend ((tag, source), expected) lthy =
  let
    val _ = validate_rejection_tag check_frontend tag
    val pos      = Input.pos_of source
    (* trim: the cartouche-spacing convention pads content with a blank on each side *)
    val expected = Symbol.trim_blanks (Input.string_of expected)
    fun fail msg = error ("urust_expr_rejects: " ^ msg ^ Position.here pos)

    fun check_parser_rejection () =
      (* Lexer, parser, elaborator, and type errors are all valid new-parser rejections. *)
      (case Exn.result (fn () => Parser_Test_Elaboration.expression lthy source) () of
         Exn.Res t =>
           fail ("expected the new parser to reject, but it accepted and elaborated to: " ^
                 Syntax.string_of_term lthy t)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val msg = Runtime.exn_message exn in
               if String.isSubstring expected msg
               then writeln ("new parser rejected as expected: " ^ msg)
               else fail ("new parser rejected, but not for the expected reason.\n" ^
                          "  expected substring: " ^ quote expected ^
                          "\n  actual message: " ^ msg)
             end)

    fun check_frontend_rejection () =
      (case Exn.result (Syntax.read_term lthy)
              (negative_frontend_source (Input.string_of source)) of
         Exn.Res t =>
           fail ("expected the existing frontend to reject, but it accepted and elaborated to: " ^
                 Syntax.string_of_term lthy t)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else writeln ("existing frontend rejected as expected: " ^ Runtime.exn_message exn))

    fun check_frontend_acceptance () =
      (case Exn.result (Syntax.read_term lthy)
              (negative_frontend_source (Input.string_of source)) of
         Exn.Res _ =>
           writeln "existing frontend accepted as expected"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             fail
               ("expected the existing frontend to accept, but it rejected: " ^
                Runtime.exn_message exn))

    val _ = check_parser_rejection ()
    val _ =
      (case (check_frontend, tag) of
         (true, Fidelity) => check_frontend_rejection ()
       | (false, FrontendAccepts) => check_frontend_acceptance ()
       | _ => ())
  in lthy end

val rejection_args =
  (Parse.name_position >> parse_rejection_tag) --
    (Parse.token Parse.cartouche >>
      Parser_Lex_Util.cartouche_source) --
    (Parse.token Parse.cartouche >>
      Parser_Lex_Util.cartouche_source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_rejects\<close>
          "Assert that both uRust frontends reject; check the new parser's reason"
          (rejection_args >> urust_rejects true)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>new_urust_rejects\<close>
          "Assert that the new uRust parser rejects under the selected frontend policy"
          (rejection_args >> urust_rejects false)
\<close>

section\<open> Non-associative operators \<close>

text\<open>
Grammar \<open>%nonassoc\<close> rejects chained comparisons, matching Rust and the frontend.
\<close>

urust_expr_rejects fidelity \<open> 1 == 2 == 3 \<close> \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] chained \<open>==\<close>; the frontend rejects it with an inner-syntax error. \<close>

urust_expr_rejects fidelity \<open> 1 < 2 < 3 \<close> \<open> syntax error found at < \<close>
  \<comment> \<open> [FIDELITY] chained \<open><\<close>; same on both sides. \<close>

section\<open> Reference-prefix precedence \<close>

text\<open>
The frontend gives \<open>!\<close> a tighter prefix tier than borrow and dereference.
Parentheses make the converse composition explicit; its positive row is
\<open>ref_not_grouped_deref\<close>.
\<close>

urust_expr_rejects fidelity \<open> ! *r \<close> \<open> syntax error found at * \<close>
  \<comment> \<open> [FIDELITY] an unparenthesized dereference cannot be the operand of tighter \<open>!\<close>. \<close>

urust_expr_rejects fidelity \<open> ! &r \<close> \<open> syntax error found at & \<close>
  \<comment> \<open> [FIDELITY] borrow has the same boundary relative to \<open>!\<close>. \<close>

section\<open> Control-flow stratification (D25 / divergence D-1) \<close>

text\<open>
Because \<open>ucontrol_expr\<close> is not a bare \<open>uexp\<close>, an unparenthesized \<open>if\<close>
cannot be a binary operand. The positive \<open>d1_paren_operand\<close> row covers the
parenthesized form.
\<close>

urust_expr_rejects fidelity
  \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } + \<llangle>3 :: 32 word\<rrangle> \<close>
  \<open> syntax error found at + \<close>
  \<comment> \<open> [FIDELITY] \<open>if\<close> as a \<open>+\<close> operand; the frontend rejects it too (priority mismatch). \<close>

section\<open> Integer literals \<close>

urust_expr_rejects fidelity \<open> 1_u7 \<close> \<open> unsupported integer-literal suffix "_u7" \<close>
  \<comment> \<open> [FIDELITY] unknown width suffix, from the single term-layer suffix table (D29); the frontend's
       numeral-ascription syntax rejects it too. Adding \<open>u7\<close> would break this row -- deliberately. \<close>

section\<open> Comments \<close>

urust_expr_rejects fidelity \<open> /* block comments remain unsupported */ () \<close>
  \<open> / \<close>
  \<comment> \<open> [FIDELITY] this increment adds only Rust line comments; neither frontend accepts block
       comments. \<close>

section\<open> Unsupported Rust-compatible integer suffixes \<close>

urust_expr_rejects fidelity \<open> 1u128 \<close> \<open> unsupported integer-literal suffix "u128" \<close>
  \<comment> \<open> [FIDELITY] a glued unsupported decimal width is one numeric token and is rejected at its
       suffix by the sole term-layer table. \<close>

urust_expr_rejects fidelity \<open> 0xffu128 \<close> \<open> unsupported integer-literal suffix "u128" \<close>
  \<comment> \<open> [FIDELITY] the same longest-match and positioned suffix diagnostic apply after hex digits. \<close>

urust_expr_rejects fidelity \<open> 1i32 \<close> \<open> unsupported integer-literal suffix "i32" \<close>
  \<comment> \<open> [FIDELITY] signed integer types are not added by the glued-suffix syntax improvement. \<close>

urust_expr_rejects fidelity \<open> 0xffi32 \<close> \<open> unsupported integer-literal suffix "i32" \<close>
  \<comment> \<open> [FIDELITY] unsupported signed suffixes also stay intact after a hex literal. \<close>

urust_expr_rejects fidelity \<open> 1u32tail \<close> \<open> unsupported integer-literal suffix "u32tail" \<close>
  \<comment> \<open> [FIDELITY] lexical longest-match must not accept the supported prefix and leave an identifier. \<close>

urust_expr_rejects fidelity \<open> 0xffu8tail \<close> \<open> unsupported integer-literal suffix "u8tail" \<close>
  \<comment> \<open> [FIDELITY] hexadecimal suffix candidates obey the same whole-token boundary. \<close>

urust_expr_rejects fidelity \<open> 1foo \<close> \<open> unsupported integer-literal suffix "foo" \<close>
  \<comment> \<open> [FIDELITY] immediate identifier adjacency is a suffix candidate, not a second token. \<close>

urust_expr_rejects fidelity \<open> 0xffvalue \<close> \<open> unsupported integer-literal suffix "value" \<close>
  \<comment> \<open> [FIDELITY] a non-hex identifier start establishes the corresponding hex suffix boundary. \<close>

urust_expr_rejects fidelity \<open> 1 foo \<close> \<open> syntax error found at <identifier> \<close>
  \<comment> \<open> [FIDELITY] whitespace terminates the numeric token; the following identifier is not swallowed. \<close>

urust_expr_rejects fidelity \<open> 1_000 \<close> \<open> unsupported integer-literal suffix "_000" \<close>
  \<comment> \<open> [FIDELITY] numeric separators remain out of scope and do not become decimal digits. \<close>

urust_expr_rejects fidelity \<open> 0xff_00 \<close> \<open> unsupported integer-literal suffix "_00" \<close>
  \<comment> \<open> [FIDELITY] numeric separators remain out of scope for hexadecimal literals too. \<close>

urust_expr_rejects fidelity \<open> 1_ \<close> \<open> unsupported integer-literal suffix "_" \<close>
  \<comment> \<open> [FIDELITY] a compatibility underscore must introduce one of the supported suffixes. \<close>

urust_expr_rejects fidelity \<open> 0xff_ \<close> \<open> unsupported integer-literal suffix "_" \<close>
  \<comment> \<open> [FIDELITY] a trailing underscore is not an empty hexadecimal suffix. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1u8 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> <integer> => \<close>
  \<comment> \<open> [FIDELITY] suffixed decimal literals remain outside the pattern grammar. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { 0xffu8 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> <integer> => \<close>
  \<comment> \<open> [FIDELITY] suffixed hexadecimal literals preserve the same pattern boundary. \<close>

section\<open> Patterns \<close>

datatype negative_struct_fixture =
  NegativeStruct (negative_left: nat) (negative_right: nat)

datatype negative_more_selector_fixture =
  NegativeMoreSelector (negative_more_required: nat) (more: nat)

datatype negative_registered_constructor_fixture =
    NegativeRegisteredNullary
  | NegativeRegisteredUnary nat
  | NegativeRegisteredOther

datatype 'a negative_registered_phantom =
  NegativeRegisteredPhantom

definition negative_registered_nonconstructor ::
  negative_registered_constructor_fixture where
  \<open>
    negative_registered_nonconstructor \<equiv>
      NegativeRegisteredNullary
  \<close>

definition negative_registered_number :: nat where
  \<open> negative_registered_number \<equiv> 42 \<close>

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Nullary")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredUnary
  ("NegativeRegistered::Unary")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredOther
  ("NegativeRegistered::Other")
micro_rust_notation (literal)
  negative_registered_nonconstructor
  ("NegativeRegistered::Value")
micro_rust_notation (literal)
  negative_registered_number
  ("NegativeRegistered::Number")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Ambiguous")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredOther
  ("NegativeRegistered::Ambiguous")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::ConstructorWins")
micro_rust_notation (literal)
  negative_registered_nonconstructor
  ("NegativeRegistered::ConstructorWins")
micro_rust_notation (literal)
  \<open> NegativeRegisteredUnary 0 \<close>
  ("NegativeRegistered::Applied")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Duplicate")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Duplicate")
micro_rust_notation (literal)
  \<open>
    NegativeRegisteredPhantom ::
      nat negative_registered_phantom
  \<close>
  ("NegativeRegistered::Phantom")
micro_rust_notation (literal)
  \<open>
    NegativeRegisteredPhantom ::
      bool negative_registered_phantom
  \<close>
  ("NegativeRegistered::Phantom")

record negative_record_fixture =
  negative_record_left :: nat
  negative_record_right :: nat

subsection\<open> Cycle 1 atomic binder validation (C1-I1--C1-I3) \<close>

text\<open>
Every alternative is validated before Resolution allocates any local. These rows pin duplicate
diagnostics across the recursive shapes and binding sites that currently consume patterns.
\<close>

new_urust_rejects divergent
  \<open> let (x, x) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [DIVERGENT] the custom parser rejects the duplicate before allocating either binder. \<close>

new_urust_rejects audit
  \<open> const x @ x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] aliases participate in the same atomic duplicate-binder validation. \<close>

new_urust_rejects audit
  \<open> for (x, x) in \<llangle>[(1 :: nat, (2 :: nat, TNil))]\<rrangle> { () } \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] loop binders validate recursively before allocating locals. \<close>

new_urust_rejects audit
  \<open> let mut (x, x) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] mutable tuple binders retain the atomic validation boundary. \<close>

new_urust_rejects audit
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some((x, x)) =
      \<llangle>Some (1 :: nat, (2 :: nat, TNil))\<rrangle> { () }
  \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] while-let validates nested constructor payloads atomically. \<close>

new_urust_rejects audit
  \<open> match_case \<llangle>[1 :: nat, 2]\<rrangle> { [x, x] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] slice children share the source arm's single validation pass. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeStruct 1 2\<rrangle> {
      NegativeStruct(x, x) \<Rightarrow> x
    }
  \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] positional constructor children share the atomic binder set. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeStruct 1 2\<rrangle> {
      NegativeStruct { negative_left: x, negative_right: x } \<Rightarrow> x
    }
  \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] struct-field children share the atomic binder set. \<close>

text\<open>
Or-pattern alternatives use the first alternative as the canonical binder set. Recursive duplicate
checks run before cross-alternative comparison; missing names are selected deterministically before
extra names, and no rejected arm reaches guard or body lowering.
\<close>

new_urust_rejects frontend_accepts
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x } \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [DIVERGENT] Rust requires every alternative to bind the same names. \<close>

new_urust_rejects frontend_accepts
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { None | Some(x) \<Rightarrow> 0 } \<close>
  \<open> or-pattern alternative has extra binder "x" \<close>
  \<comment> \<open> [DIVERGENT] reversing the alternatives makes the empty first binder set canonical. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeStruct 1 2\<rrangle> {
      NegativeStruct(z, x) | NegativeStruct(_, _) \<Rightarrow> 0
    }
  \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [AUDIT] multiple missing names are diagnosed in deterministic name order. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) | Some(x) | None \<Rightarrow> x
    }
  \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [AUDIT] a third alternative is compared with the first alternative's binder set. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>Some (Ok (1 :: nat))\<rrangle> {
      Some(Ok(x) | Err(y)) \<Rightarrow> 0, _ \<Rightarrow> 0
    }
  \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [AUDIT] nested alternatives report a missing canonical binder before an extra binder. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>Some (Some (1 :: nat))\<rrangle> {
      Some(None | Some(x)) \<Rightarrow> 0, _ \<Rightarrow> 0
    }
  \<close>
  \<open> or-pattern alternative has extra binder "x" \<close>
  \<comment> \<open> [AUDIT] nested constructor alternatives retain the same extra-binder rule. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) | None if unknown_binder_guard!() \<Rightarrow>
        unknown_binder_body!(),
      _ \<Rightarrow> 0
    }
  \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [AUDIT] binder validation wins before guard and body macro resolution. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>[1 :: nat, 2]\<rrangle> {
      [] | [x, ..] \<Rightarrow> 0, _ \<Rightarrow> 0
    }
  \<close>
  \<open> or-pattern alternative has extra binder "x" \<close>
  \<comment> \<open> [AUDIT] reversing nested slice alternatives exposes the extra-binder diagnostic. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeStruct 1 2\<rrangle> {
      NegativeStruct(x, x) | NegativeStruct(y, _) \<Rightarrow> 0
    }
  \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] a duplicate in the canonical alternative wins before binder-set comparison. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeStruct 1 2\<rrangle> {
      NegativeStruct(x, _) | NegativeStruct(y, y) \<Rightarrow> 0
    }
  \<close>
  \<open> duplicate pattern binder "y" \<close>
  \<comment> \<open> [AUDIT] a duplicate in a later alternative wins before missing/extra comparison. \<close>

urust_expr_rejects fidelity \<open> let Some(x) = \<llangle>Some (0 :: nat)\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] the site gate on the ONE pattern language (D28). The frontend rejects it as well,
       though less cleanly -- an uncaught \<open>TERM\<close> exception out of \<open>abs_tr _shallow_let_pattern\<close>. \<close>

urust_expr_rejects fidelity
  \<open> let (Some(x), y) = \<llangle>(Some (0 :: nat), (True, TNil))\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] tuple binders recurse through the irrefutability gate, so the constructor component
       is rejected at its own source position. \<close>

urust_expr_rejects fidelity \<open> let true = true; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] boolean value patterns are refutable. \<close>

urust_expr_rejects fidelity \<open> const "ok" = "ok"; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] string value patterns are refutable. \<close>

urust_expr_rejects fidelity
  \<open> let \<llangle>2 :: nat\<rrangle> = \<llangle>2 :: nat\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] value-antiquotation patterns are refutable. \<close>

urust_expr_rejects fidelity
  \<open> let mut (x) = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] the frontend accepts a scalar mutable identifier or an actual top-level tuple,
       not a grouped scalar. The diagnostic is positioned at the grouped pattern. \<close>

urust_expr_rejects fidelity
  \<open> let mut Some(x) = \<llangle>Some (1 :: nat)\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] constructor patterns are not mutable binding heads. \<close>

urust_expr_rejects fidelity
  \<open> let mut &x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] reference-pattern syntax has no current binding semantics. \<close>

urust_expr_rejects fidelity
  \<open> let mut whole @ x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] aliases are rejected by the mutable-site gate. \<close>

urust_expr_rejects fidelity
  \<open> let mut [x, ..] = \<llangle>[1 :: nat]\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] slice patterns are rejected by the mutable-site gate. \<close>

urust_expr_rejects fidelity
  \<open> let mut (Some(x), y) = \<llangle>(Some (1 :: nat), (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] top-level tuple \<open>mut\<close> is erased, after which the ordinary recursive
       irrefutability gate rejects a constructor component at its own position. \<close>

urust_expr_rejects fidelity
  \<open> let &x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] reference-pattern syntax has no current binding semantics. \<close>

new_urust_rejects divergent
  \<open> const &x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [DIVERGENT] const bindings share the same non-erasing reference-pattern gate. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>1 :: nat\<rrangle> { &1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] wrapper erasure exposes the underlying unsupported case numeral. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>1 :: nat\<rrangle> { (&1)..2 \<Rightarrow> True, _ \<Rightarrow> False } \<close>
  \<open> invalid range-pattern endpoint \<close>
  \<comment> \<open> [FIDELITY] range endpoints remain value-only; wrapper erasure applies to the complete
       case pattern, not inside an endpoint. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>1 :: nat\<rrangle> { 0..=(&2) \<Rightarrow> True, _ \<Rightarrow> False } \<close>
  \<open> invalid range-pattern endpoint \<close>
  \<comment> \<open> [FIDELITY] the upper range endpoint has the same value-only boundary. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>(0 :: nat, (True, TNil))\<rrangle> { (x, y) \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] tuple patterns require case lowering; explicit \<open>match_switch\<close> remains
       first-order and rejects them with its stable positioned diagnostic. \<close>

urust_expr_rejects fidelity \<open> match_switch true { true \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] boolean patterns require equality-guard case lowering. \<close>

urust_expr_rejects fidelity \<open> match_switch "ok" { "ok" \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] string patterns require equality-guard case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>2 :: nat\<rrangle> { \<llangle>2 :: nat\<rrangle> \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] value-antiquotation patterns require equality-guard case lowering. \<close>

urust_expr_rejects fidelity \<open> (\<llangle>1 :: nat\<rrangle>,) \<close> \<open> syntax error found at ) \<close>
  \<comment> \<open> [FIDELITY] singleton tuples are outside the current frontend tuple grammar. \<close>

urust_expr_rejects fidelity
  \<open> let (x,) = \<llangle>(1 :: nat, TNil)\<rrangle>; x \<close>
  \<open> syntax error: deleting  ) = \<close>
  \<comment> \<open> [FIDELITY] a terminal comma does not turn a grouped singleton pattern into a tuple. \<close>

urust_expr_rejects fidelity
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>,,) \<close>
  \<open> syntax error found at , \<close>
  \<comment> \<open> [FIDELITY] a trailing comma is one separator, not an empty tuple element. \<close>

urust_expr_rejects fidelity
  \<open> let (x, y,,) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> syntax error: deleting  , ) = \<close>
  \<comment> \<open> [FIDELITY] tuple-pattern lists likewise reject an empty element after the terminal comma. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x,,) \<Rightarrow> x, None \<Rightarrow> 0 } \<close>
  \<open> syntax error: deleting  , ) => \<close>
  \<comment> \<open> [FIDELITY] constructor argument lists reject doubled terminal commas. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> x, None \<Rightarrow> 0,, } \<close>
  \<open> syntax error found at , \<close>
  \<comment> \<open> [FIDELITY] match-arm lists reject an empty arm after the terminal comma. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, y,,] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
  \<open> syntax error: deleting  , ] => \<close>
  \<comment> \<open> [FIDELITY] slice-pattern lists reject doubled terminal commas. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, negative_right: y,, } \<Rightarrow> x } \<close>
  \<open> syntax error: deleting  , } => \<close>
  \<comment> \<open> [FIDELITY] struct-field lists reject an empty field after the terminal comma. \<close>

urust_expr_rejects fidelity \<open> let () = (); () \<close> \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] unit is an expression but not a pattern in the current frontend. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] a numeral belongs to \<open>match_switch\<close>; source validation rejects it before
       generated case clauses are constructed. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] literal \<open>1\<close> has the same dedicated case-pattern node and rejection boundary as
       literal \<open>0\<close>. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>2 :: nat\<rrangle> { 2 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] the frontend's attempted guarded lowering retains the raw token and rejects with
       \<open>Undefined constant: "2"\<close>; the parser gives the same accept-set boundary a positioned diagnostic. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>Some (2 :: nat)\<rrangle> { Some(2) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] constructor-nested numerals hit the same frontend raw-token rejection. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>2 :: nat\<rrangle> { 2 if True \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> guards are not supported in explicit `match_switch` \<close>
  \<comment> \<open> [FIDELITY] guards force bare \<open>match\<close> to case lowering, but the explicit switch form rejects
       them rather than changing lowering. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>Some (0 :: nat)\<rrangle> { NoSuchCtor(x) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> `NoSuchCtor` is not a known constructor \<close>
  \<comment> \<open> [FIDELITY] ordinary unregistered constructor lookup retains the \<open>Code.is_constr\<close>
       boundary; the frontend agrees ("Error in case expression: Not a datatype constructor"). \<close>

subsection\<open> Registered constructor diagnostics \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> {
      NegativeRegistered::Unary \<Rightarrow> 0,
      _ \<Rightarrow> 1
    }
  \<close>
  \<open> constructor "Unary" expects 1 pattern argument(s), but got 0 \<close>
  \<comment> \<open> [AUDIT] an exact constructor registration retains its authentic arity for a nullary use. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> {
      NegativeRegistered::Unary(left, right) \<Rightarrow> left,
      _ \<Rightarrow> 0
    }
  \<close>
  \<open> constructor "NegativeRegistered::Unary" expects 1 pattern argument(s), but got 2 \<close>
  \<comment> \<open> [AUDIT] the same arity check covers excess arguments at the terminal constructor token. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>negative_registered_nonconstructor\<rrangle> {
      NegativeRegistered::Value(value) \<Rightarrow> value,
      _ \<Rightarrow> NegativeRegisteredNullary
    }
  \<close>
  \<open> `NegativeRegistered::Value` is not a known constructor \<close>
  \<comment> \<open> [AUDIT] a definition equal to a constructor is still a value registration; resolution does
       not unfold it to manufacture constructor identity. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeRegisteredNullary\<rrangle> {
      NegativeRegistered::Ambiguous \<Rightarrow> 0,
      _ \<Rightarrow> 1
    }
  \<close>
  \<open> constructor pattern "NegativeRegistered::Ambiguous" is ambiguous; candidates: \<close>
  \<comment> \<open> [AUDIT] two distinct authentic registered backends retain a deterministic ambiguity. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> {
      NegativeRegistered::Applied(value) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>
  \<open> `NegativeRegistered::Applied` is not a known constructor \<close>
  \<comment> \<open> [AUDIT] an application headed by a constructor is not the whole constructor term. \<close>

new_urust_rejects divergent \<open> match_switch \<llangle>0 :: nat\<rrangle> { x \<Rightarrow> () } \<close>
  \<open> unsupported match_switch key "x" \<close>
  \<comment> \<open> [DIVERGENT] the frontend accepts a binding key under \<open>match_switch\<close>. The dedicated
       parser accepts numerals, \<open>_\<close>, and exact registered identifiers/paths as keys, but an
       unregistered identifier remains a binding pattern and needs \<open>match_case\<close>. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>Some (0 :: nat)\<rrangle> { 0 \<Rightarrow> (), Some(x) \<Rightarrow> () } \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [FIDELITY] bare-match routing cannot select one lowering for numeral and constructor heads;
       the frontend reports the same mixed-match category. \<close>

new_urust_rejects audit
  \<open>
    match \<llangle>NegativeRegisteredNullary\<rrangle> {
      0 \<Rightarrow> (),
      NegativeRegistered::Nullary \<Rightarrow> ()
    }
  \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [AUDIT] an exact authentic constructor registration remains case-only during automatic
       routing. \<close>

new_urust_rejects audit
  \<open>
    match
      \<llangle>
        NegativeRegisteredPhantom ::
          nat negative_registered_phantom
      \<rrangle> {
      0 \<Rightarrow> (),
      NegativeRegistered::Phantom \<Rightarrow> ()
    }
  \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [AUDIT] phantom instantiation does not disguise registered constructor identity. \<close>

new_urust_rejects audit
  \<open>
    match \<llangle>NegativeRegisteredNullary\<rrangle> {
      0 \<Rightarrow> (),
      NegativeRegistered::ConstructorWins \<Rightarrow> ()
    }
  \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [AUDIT] when one exact key has both a constructor and a nonconstructor backend, the
       authentic constructor makes automatic routing case-only. \<close>

new_urust_rejects audit
  \<open>
    match \<llangle>NegativeRegisteredNullary\<rrangle> {
      0 \<Rightarrow> (),
      NegativeRegistered::Ambiguous \<Rightarrow> ()
    }
  \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [AUDIT] two distinct constructor registrations classify as constructor-shaped before
       later case-resolution ambiguity can run. \<close>

new_urust_rejects audit
  \<open>
    match 42 {
      0 if True \<Rightarrow> (),
      NegativeRegistered::Number \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [AUDIT] any source guard forces case lowering before the first numeral is validated. \<close>

new_urust_rejects audit
  \<open>
    match_case 42 {
      0 \<Rightarrow> (),
      NegativeRegistered::Number \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [AUDIT] explicit case flavour remains authoritative. \<close>

new_urust_rejects audit
  \<open>
    match_switch 42 {
      NegativeRegistered::Number if True \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> guards are not supported in explicit `match_switch` \<close>
  \<comment> \<open> [AUDIT] contextual registered-value support does not relax explicit switch guards. \<close>

new_urust_rejects audit
  \<open>
    match 0 {
      0 \<Rightarrow> (),
      Unregistered::Value \<Rightarrow> ()
    }
  \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [AUDIT] an unregistered qualified path remains case-only. \<close>

new_urust_rejects audit
  \<open>
    match 0 {
      0 \<Rightarrow> (),
      unregistered_key \<Rightarrow> ()
    }
  \<close>
  \<open> unsupported match_switch key "unregistered_key" \<close>
  \<comment> \<open> [AUDIT] an unregistered bare identifier retains the switch-key binder rejection. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>Some (2 :: nat)\<rrangle> { Some(1..2..3) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> range patterns are non-associative \<close>
  \<comment> \<open> [FIDELITY] range patterns are non-associative. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>[1 :: nat]\<rrangle> { [.., ..] \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> slice pattern has multiple `..` rest entries \<close>
  \<comment> \<open> [FIDELITY] a slice has at most one rest marker. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, negative_left: y, .. } \<Rightarrow> x } \<close>
  \<open> has duplicate field "negative_left" \<close>
  \<comment> \<open> [FIDELITY] duplicate struct fields reject at the repeated field. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x } \<Rightarrow> x } \<close>
  \<open> is missing field(s): negative_right \<close>
  \<comment> \<open> [FIDELITY] omitted fields require a struct rest marker. \<close>

new_urust_rejects divergent
  \<open> match_case \<llangle>NegativeMoreSelector 1 2\<rrangle> { NegativeMoreSelector { negative_more_required: x } \<Rightarrow> x } \<close>
  \<open> is missing field(s): more \<close>
  \<comment> \<open> [DIVERGENT] an ordinary datatype selector named \<open>more\<close> is required. The frontend
       mistakes its basename for HOL record-extension metadata and accepts the omission. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>\<lparr>negative_record_left = 1, negative_record_right = 2\<rparr>\<rrangle> { negative_record_fixture { negative_record_left: x, negative_record_right: _ } \<Rightarrow> x } \<close>
  \<open> HOL record pattern "negative_record_fixture" requires selector-based lowering \<close>
  \<comment> \<open> [FIDELITY] both frontends reject HOL record extension constructors. The custom parser
       exposes the explicit boundary for future selector-based lowering (T-29). \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { unknown: x, .. } \<Rightarrow> x } \<close>
  \<open> has unknown field "unknown" \<close>
  \<comment> \<open> [FIDELITY] selector metadata validates struct field names. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NoSuchStruct { field: x, .. } \<Rightarrow> x } \<close>
  \<open> no matching constructor or single-constructor record/datatype found \<close>
  \<comment> \<open> [FIDELITY] struct heads must resolve through constructor/type metadata. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { .., .. } \<Rightarrow> () } \<close>
  \<open> struct pattern has multiple `..` rest entries \<close>
  \<comment> \<open> [FIDELITY] a struct has at most one rest entry. \<close>

urust_expr_rejects fidelity
  \<open> let whole @ x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] aliases remain outside irrefutable let binders. \<close>

urust_expr_rejects fidelity
  \<open> const (1..=2) = \<llangle>1 :: nat\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] ranges remain outside irrefutable const binders. \<close>

urust_expr_rejects fidelity
  \<open> let [x, ..] = \<llangle>[1 :: nat]\<rrangle>; x \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] slices remain outside irrefutable let binders. \<close>

urust_expr_rejects fidelity
  \<open> const NegativeStruct { negative_left: x, .. } = \<llangle>NegativeStruct 1 2\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] structs remain outside irrefutable const binders. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>Some (1 :: nat)\<rrangle> { whole @ Some(x) \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] aliases require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1..=2 \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] ranges require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>[1 :: nat]\<rrangle> { [x, ..] \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] slices require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, .. } \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] struct patterns require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { &1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] explicit switch conversion rejects reference syntax before key lowering. \<close>

new_urust_rejects divergent
  \<open> match_case \<llangle>undefined\<rrangle> { AmbiguousStruct { ambiguous_field: x } \<Rightarrow> x } \<close>
  \<open> Struct_Ambiguity_Left.struct_ambiguity_left.AmbiguousStruct \<close>
  \<comment> \<open> [DIVERGENT] the existing frontend silently picks one of two same-basename constructors.
       The new parser rejects and reports their qualified identities instead. \<close>

ML\<open>
local
  val left_struct =
    "Struct_Ambiguity_Left.struct_ambiguity_left.AmbiguousStruct"
  val right_struct =
    "Struct_Ambiguity_Right.struct_ambiguity_right.AmbiguousStruct"
  val left_nullary =
    "Struct_Ambiguity_Left.nullary_ambiguity_left.AmbiguousNullary"
  val right_nullary =
    "Struct_Ambiguity_Right.nullary_ambiguity_right.AmbiguousNullary"

  fun assert message condition =
    if condition then () else error message

  fun expect_ambiguity label source identities =
    (case Exn.result
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source source)) () of
       Exn.Res _ =>
         error (label ^ " unexpectedly resolved an ambiguous constructor")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn in
             assert (label ^ " did not report ambiguity")
               (String.isSubstring "is ambiguous; candidates:" message);
             List.app
               (fn identity =>
                 assert
                   (label ^ " omitted candidate " ^ quote identity)
                   (String.isSubstring identity message))
               identities
           end)

  val resolver =
    URust_Resolution.make_constructor_resolver
      \<^context> Position.none

  fun qualified identity =
    (case URust_Resolution.resolve_constructor \<^context> resolver
        (URust_AST.make_single_path (identity, Position.none)) of
       SOME info => info
     | NONE =>
         error
           ("qualified constructor did not resolve: " ^
             quote identity))

  val struct_info = qualified left_struct
  val nullary_info = qualified left_nullary

  val _ =
    assert "qualified positional constructor arity changed"
      (URust_Resolution.constructor_arity struct_info = 1)
  val _ =
    assert "qualified nullary constructor arity changed"
      (URust_Resolution.constructor_arity nullary_info = 0)
  val _ =
    (case URust_Resolution.constructor_family struct_info of
       SOME (family, members) =>
         (assert "qualified constructor family changed"
            (family =
              "Struct_Ambiguity_Left.struct_ambiguity_left");
          assert "qualified constructor family members changed"
            (map_filter
              (fn Const (name, _) => SOME name | _ => NONE)
              members = [left_struct]))
     | NONE =>
         error "qualified constructor lost family metadata")

  val _ =
    expect_ambiguity "positional constructor ambiguity"
      "match_case \<llangle>undefined\<rrangle> { AmbiguousStruct(x) \<Rightarrow> x }"
      [left_struct, right_struct]
  val _ =
    expect_ambiguity "nullary constructor ambiguity"
      "match_case \<llangle>undefined\<rrangle> { AmbiguousNullary \<Rightarrow> \<llangle>True\<rrangle> }"
      [left_nullary, right_nullary]
in
end
\<close>

subsection\<open> Cycle 1 source-diagnostic isolation (C1-I7/C1-I8) \<close>

text\<open>
Representative source failures must be raised before generated HOL reaches type checking. In
particular, diagnostics may not expose administrative names, generated case clauses, old internal
numeric-pattern wording, or synthetic positionless fallbacks.
\<close>

ML\<open>
local
  val forbidden =
    ["_urust_local_", "_urust_case_", "case_elem", "case_abs",
     "clauses are redundant", "numeric pattern in match_case", "Position.none"]

  fun expect_clean_rejection source required =
    (case Exn.result
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source source)) () of
       Exn.Res term =>
         error ("Cycle 1 diagnostic audit expected rejection, but got " ^
           Syntax.string_of_term \<^context> term)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let
             val message = Runtime.exn_message exn
             val _ =
               List.app
                 (fn expected =>
                   if String.isSubstring expected message then ()
                   else
                     error ("Cycle 1 diagnostic audit expected " ^
                       quote expected ^ ", but got " ^ quote message))
                 required
             val _ =
               List.app
                 (fn leaked =>
                   if String.isSubstring leaked message
                   then
                     error ("Cycle 1 diagnostic audit leaked " ^
                       quote leaked ^ " in " ^ quote message)
                   else ())
                 forbidden
           in () end)

  val _ =
    expect_clean_rejection
      "let (x, x) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x"
      ["duplicate pattern binder \"x\"", "The original binder is here"]
  val _ =
    expect_clean_rejection
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x }"
      ["or-pattern alternative is missing binder \"x\""]
  val _ =
    expect_clean_rejection
      "match_case \<llangle>0 :: nat\<rrangle> { Some(&0) \<Rightarrow> True, _ \<Rightarrow> False }"
      ["numeric patterns are not supported in case patterns"]
  val _ =
    expect_clean_rejection
      "match_case \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> True, _ \<Rightarrow> False }"
      ["numeric patterns are not supported in case patterns"]
  val _ =
    expect_clean_rejection
      "for None in \<llangle>[None :: nat option]\<rrangle> { () }"
      ["unsupported or refutable pattern in a `for` binder position"]
in end
\<close>

section\<open> Calls \<close>

definition ncf1 :: \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> ncf1 \<equiv> lift_fun1 (\<lambda>x. x) \<close>

micro_rust_notation (call) ncf1 ("NegativeArity::Registered")
micro_rust_notation (call) ncf1 ("negative_arity_registered_method")

new_urust_rejects frontend_accepts
  \<open> assert!(!o.is_none()) \<close>
  \<open> Type unification failed \<close>
  \<comment> \<open> [INTENTIONAL] The legacy frontend infers the bare method head as a
       free, but the dedicated parser rejects an unresolved method spelling.
       An explicit call registration, lexical method binder, fixed shallow
       function, or shallow HOL constant must provide the backend. \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>,,) \<close>
  \<open> syntax error found at , \<close>
  \<comment> \<open> [FIDELITY] call argument lists reject an empty argument after the terminal comma. \<close>

urust_expr_rejects fidelity \<open> zz(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] the arity cap is ONE policy number derived from the frontend's surface lowering (D29);
       the frontend rejects 15 args too ("Undefined constant: _urust_shallow_fun_with_args"). \<close>

new_urust_rejects audit
  \<open> NegativeArity::Registered(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

new_urust_rejects audit
  \<open> ncf1(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

new_urust_rejects audit
  \<open> Suc(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

context
  fixes negative_arity_fixed :: unit
  fixes negative_arity_fixed_method :: unit
begin

new_urust_rejects audit
  \<open> negative_arity_fixed(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

new_urust_rejects audit
  \<open> 0.negative_arity_fixed_method(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

new_urust_rejects audit
  \<open> 0.negative_arity_fixed_method(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) \<close>
  \<open> unsupported call arity 16 \<close>

end

urust_expr_rejects fidelity
  \<open> \<epsilon>\<open>ncf1\<close>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] expression-antiquotation callees share the inclusive
       \<open>funcall14\<close> policy. \<close>

urust_expr_rejects fidelity
  \<open> 0.zz(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] 14 explicit method arguments plus the prepended receiver exceed
       the inclusive \<open>funcall14\<close> limit by one. \<close>

urust_expr_rejects fidelity
  \<open> 0.zz(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) \<close>
  \<open> unsupported call arity 16 \<close>
  \<comment> \<open> [FIDELITY] the 15-explicit-argument boundary lowers to 16 total arguments. \<close>

new_urust_rejects audit
  \<open> 0.negative_arity_registered_method(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

new_urust_rejects audit
  \<open> 0.negative_arity_registered_method(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) \<close>
  \<open> unsupported call arity 16 \<close>

new_urust_rejects audit
  \<open> 0.ncf1(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

new_urust_rejects audit
  \<open> 0.ncf1(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) \<close>
  \<open> unsupported call arity 16 \<close>

new_urust_rejects audit
  \<open> 0.Suc(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>

new_urust_rejects audit
  \<open> 0.Suc(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) \<close>
  \<open> unsupported call arity 16 \<close>

new_urust_rejects audit
  \<open>
    Suc(
      unknown_arity_argument!(),
      1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14
    )
  \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> Structural arity wins before the incompatible pure-HOL head and argument lowering. \<close>

new_urust_rejects audit
  \<open>
    unknown_arity_receiver!().zz(
      unknown_arity_argument!(),
      2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14
    )
  \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> The receiver plus fourteen explicit arguments are counted before receiver, head, or argument lowering. \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>)(\<llangle>2 :: 64 word\<rrangle>) \<close>
  \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] curried application \<open>f(a)(b)\<close>: rejected by both (a call result is not a callee). \<close>

urust_expr_rejects fidelity \<open> (ncf1)(\<llangle>1 :: 64 word\<rrangle>) \<close> \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] parenthesised callee \<open>(g)(x)\<close>: rejected by both (\<open>urust_callable\<close> has no paren form). \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>ncf1\<rrangle>(\<llangle>1 :: 64 word\<rrangle>) \<close>
  \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] a value antiquotation is a value, not a callable antiquotation. \<close>

urust_expr_rejects fidelity
  \<open> (\<epsilon>\<open>ncf1\<close>)(\<llangle>1 :: 64 word\<rrangle>) \<close>
  \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] grouping does not turn an expression into a callee. \<close>

urust_expr_rejects fidelity
  \<open> \<epsilon>\<open>ncf1\<close>(\<llangle>1 :: 64 word\<rrangle>)(\<llangle>2 :: 64 word\<rrangle>) \<close>
  \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] a call result is not a callee. \<close>

urust_expr_rejects fidelity
  \<open> \<epsilon>\<open>ncf1\<close>(,\<llangle>1 :: 64 word\<rrangle>) \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] an antiquotation-headed call cannot start with an empty argument. \<close>

urust_expr_rejects fidelity
  \<open> \<epsilon>\<open>ncf1\<close>(\<llangle>1 :: 64 word\<rrangle> \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] an antiquotation-headed call requires its closing parenthesis. \<close>

subsection\<open> Arity-indexed function-literal callees \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>0() \<close>
  \<open> unexpected input \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1\<^sub>5() \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>_1() \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1\<^sub>1\<^sub>1() \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>2\<^sub>2() \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle> \<^sub>1() \<close>
  \<open> function-literal arity suffix must immediately follow the value antiquotation \<close>

urust_expr_rejects fidelity
  \<open> \<epsilon>\<open>id\<close>\<^sub>1() \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1 \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity
  \<open> (\<llangle>id\<rrangle>\<^sub>1)(0) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1(0)(1) \<close>
  \<open> syntax error found at ( \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1(,0) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1(0,,1) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1(0 \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>\<lambda>x. x\<rrangle>\<^sub>1() \<close>
  \<open> Type unification failed \<close>
  \<comment> \<open> [FIDELITY] lift arity is not compared with runtime arity; HOL checking rejects the mismatch. \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>\<lambda>x. x\<rrangle>\<^sub>1(0, 1) \<close>
  \<open> Type unification failed \<close>
  \<comment> \<open> [FIDELITY] the opposite lift/runtime mismatch also remains a HOL type error. \<close>

urust_expr_rejects fidelity
  \<open>
    \<llangle>\<lambda>x. x\<rrangle>\<^sub>1(
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14
    )
  \<close>
  \<open> unsupported call arity 15 \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1::<>(0) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1::<,1>(0) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1::<1,,2>(0) \<close>
  \<open> syntax error \<close>

new_urust_rejects divergent
  \<open> \<llangle>\<lambda>x. x\<rrangle>\<^sub>1::<-1>() \<close>
  \<open> unexpected input \<close>
  \<comment> \<open> [DIVERGENT] function literals use the same restricted D-20 turbofish grammar. \<close>

new_urust_rejects divergent
  \<open> \<llangle>\<lambda>x. x\<rrangle>\<^sub>1::<1 * 2>() \<close>
  \<open> unexpected input \<close>
  \<comment> \<open> [DIVERGENT] unsupported generic operators do not regain arbitrary HOL syntax here. \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1::<1(0) \<close>
  \<open> unterminated turbofish \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id\<rrangle>\<^sub>1::<1> \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>id \<^sub>1(0) \<close>
  \<open> unterminated value antiquotation \<close>

section\<open> Legacy macros \<close>

definition negative_macro_shout ::
  \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where \<open> negative_macro_shout \<equiv> lift_fun1 id \<close>

micro_rust_notation (call) negative_macro_shout ("negativeshout!")

consts
  negative_macro_raw_ref :: \<open>('a, 'b) Global_Store.gref\<close>
  negative_macro_read_only_ref :: \<open>('a, 'b, 'v) Global_Store.ro_ref\<close>

subsection\<open> Arity and raw-message policy \<close>

urust_expr_rejects fidelity \<open> assert!() \<close>
  \<open> macro "assert!" expects at least 1 argument(s), but got 0 \<close>

urust_expr_rejects fidelity \<open> assert_eq!(true) \<close>
  \<open> macro "assert_eq!" expects at least 2 argument(s), but got 1 \<close>

urust_expr_rejects fidelity \<open> assert_ne![true] \<close>
  \<open> macro "assert_ne!" expects at least 2 argument(s), but got 1 \<close>

urust_expr_rejects fidelity \<open> addr_of!() \<close>
  \<open> macro "addr_of!" expects exactly 1 argument(s), but got 0 \<close>

urust_expr_rejects fidelity \<open> addr_of_mut!(r, other) \<close>
  \<open> macro "addr_of_mut!" expects exactly 1 argument(s), but got 2 \<close>

urust_expr_rejects fidelity \<open> addr_of!(negative_macro_raw_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> addr_of_mut!(negative_macro_raw_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> addr_of!(negative_macro_read_only_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> addr_of_mut!(negative_macro_read_only_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> panic!((message)) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

urust_expr_rejects fidelity \<open> unreachable!(if true { "left" } else { "right" }) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

urust_expr_rejects fidelity \<open> unimplemented!(1_u32) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

urust_expr_rejects fidelity \<open> todo!(true) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

subsection\<open> Names, registration precedence, and delimiters \<close>

urust_expr_rejects fidelity \<open> unknown_macro!(true) \<close>
  \<open> unknown macro "unknown_macro!" \<close>

urust_expr_rejects fidelity \<open> negativeshout ! (true) \<close>
  \<open> unknown macro "negativeshout!" \<close>

urust_expr_rejects fidelity \<open> negativeshout!() \<close>
  \<open> no backend matches the use-site type \<close>

urust_expr_rejects fidelity \<open> negativeshout!(1_u32) \<close>
  \<open> no backend matches the use-site type \<close>

urust_expr_rejects fidelity \<open> assert!(true,) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> vec![1_u32,] \<close>
  \<open> syntax error found at ] \<close>

urust_expr_rejects fidelity \<open> panic!("message",) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> assert!(true] \<close>
  \<open> syntax error found at ] \<close>

urust_expr_rejects fidelity \<open> vec![1_u32) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> assert!(true \<close>
  \<open> syntax error found at end of input \<close>

subsection\<open> Complete-body argument failures \<close>

urust_expr_rejects fidelity \<open> assert!(let flag = true;) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> assert!(let flag = true; flag,) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> vec![let value = 1_u32; value,] \<close>
  \<open> syntax error found at ] \<close>

urust_expr_rejects fidelity
  \<open> assert_eq!(let left = true; left,, false) \<close>
  \<open> syntax error: deleting  , false ) \<close>

urust_expr_rejects fidelity \<open> assert!(let flag true; flag) \<close>
  \<open> syntax error: deleting  <identifier> true ; \<close>

urust_expr_rejects fidelity \<open> assert![let flag = ; flag] \<close>
  \<open> syntax error: deleting  ; <identifier> ] \<close>

urust_expr_rejects fidelity
  \<open> assert!(let flag = true; if flag { true } else { false) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> assert!(let flag = true; flag] \<close>
  \<open> syntax error found at ] \<close>

urust_expr_rejects fidelity \<open> assert![let flag = true; flag) \<close>
  \<open> syntax error found at ) \<close>

subsection\<open> Matches shape and case-compiler boundaries \<close>

urust_expr_rejects fidelity \<open> matches!() \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32)) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(_), ignored) \<close>
  \<open> syntax error: deleting \<close>

urust_expr_rejects fidelity \<open> matches!(true, true && false) \<close>
  \<open> syntax error: deleting \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(,)) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> matches![Some(1_u32), Some(_)] \<close>
  \<open> syntax error: deleting \<close>

urust_expr_rejects fidelity \<open> matches !(Some(1_u32), Some(_)) \<close>
  \<open> unknown macro "matches!" \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(_),) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), _) \<close>
  \<open> clauses are redundant \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), binder) \<close>
  \<open> clauses are redundant \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(1..=3)) \<close>
  \<open> range patterns are not supported by legacy matches! \<close>

subsection\<open> Borrow and assignment-result boundaries \<close>

urust_expr_rejects fidelity \<open> &vec![r] \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> & mut vec![r] \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> vec![] = rhs \<close>
  \<open> invalid assignment target \<close>

urust_expr_rejects fidelity \<open> assert!(true) = rhs \<close>
  \<open> invalid assignment target \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(_)) = rhs \<close>
  \<open> invalid assignment target \<close>

section\<open> Assignment right-hand control-flow precedence \<close>

text\<open>
The frontend's priority-40 assignment accepts block expressions directly, but
priority-20/21 control-flow expressions require parentheses on the right-hand
side. Assignment remains right-associative by recursing through its own tier.
\<close>

urust_expr_rejects fidelity
  \<open> r = match flag { true \<Rightarrow> lhs, false \<Rightarrow> rhs } \<close>
  \<open> syntax error: deleting  match \<close>
  \<comment> \<open> [FIDELITY] bare match forms have the same assignment-RHS boundary as \<open>if\<close>. \<close>

urust_expr_rejects fidelity
  \<open> r = if flag { lhs } else { rhs } \<close>
  \<open> syntax error: deleting  if \<close>
  \<comment> \<open> [FIDELITY] a bare \<open>if\<close> is too weak to be an assignment RHS; the grouped form is positive. \<close>

urust_expr_rejects fidelity
  \<open> r += match flag { true \<Rightarrow> lhs, false \<Rightarrow> rhs } \<close>
  \<open> syntax error: deleting  match \<close>
  \<comment> \<open> [FIDELITY] compound assignment has the same bare-match RHS boundary. \<close>

urust_expr_rejects fidelity
  \<open> r += if flag { lhs } else { rhs } \<close>
  \<open> syntax error: deleting  if \<close>
  \<comment> \<open> [FIDELITY] compound assignment recurses through \<open>uassign\<close>, not lower-priority control flow. \<close>

urust_expr_rejects fidelity \<open> r /= rhs \<close> \<open> = \<close>
  \<comment> \<open> [FIDELITY] the current frontend has no \<open>/=\<close> production; this remains a post-parity
       Rust-facing extension. \<close>

section\<open> Invalid assignment targets \<close>

text\<open>
Assignment parses below pure operators, then one \<open>expr_to_place\<close> conversion rejects
every non-place expression with the same positioned diagnostic.
\<close>

urust_expr_rejects fidelity \<open> 0 = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] numeric literals are values, not places. \<close>

urust_expr_rejects fidelity \<open> true = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] boolean literals are not places. \<close>

urust_expr_rejects fidelity \<open> \<llangle>r\<rrangle> = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] value antiquotations are values; only expression antiquotations can be places. \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>) = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] call results are not assignment targets. \<close>

urust_expr_rejects fidelity \<open> receiver.ncf1() = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] method-call results are not assignment targets. \<close>

urust_expr_rejects fidelity \<open> opt? = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] propagation is value-only. \<close>

urust_expr_rejects fidelity \<open> &r = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] borrowing produces a value and cannot head a place. \<close>

urust_expr_rejects fidelity \<open> !r = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] unary negation is not a place. \<close>

urust_expr_rejects fidelity \<open> r + other = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] assignment is below pure operators, so the full binary expression is rejected. \<close>

urust_expr_rejects fidelity \<open> (r, other) = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] tuple values are not destructuring assignment targets. \<close>

urust_expr_rejects fidelity \<open> { r } = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] blocks remain value expressions, not places. \<close>

urust_expr_rejects fidelity
  \<open> (if true { r } else { other }) = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] grouping admits the control-flow expression to operand position but does not
       make it a place. \<close>

urust_expr_rejects fidelity \<open> (r = rhs) = other \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] an assignment result cannot itself be assigned through. \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>).field = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] field-place validation recursively rejects an invalid call-result base. \<close>

urust_expr_rejects fidelity \<open> 0 += rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] compound assignment uses the same literal-target rejection path. \<close>

urust_expr_rejects fidelity \<open> r + other *= rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] pure operators bind above every assignment operator, so the complete binary LHS
       reaches the shared place validator. \<close>

urust_expr_rejects fidelity
  \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>)[0] = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] indexed places recursively require a valid place base. \<close>

section\<open> Bounded ranges, arrays, and indexing \<close>

urust_expr_rejects fidelity \<open> 1..2..3 \<close>
  \<open> syntax error found at .. \<close>
  \<comment> \<open> [FIDELITY] expression ranges are non-associative. \<close>

urust_expr_rejects fidelity \<open> 1.. \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] open-ended ranges are outside the frontend syntax and parser scope. \<close>

urust_expr_rejects fidelity \<open> ..2 \<close>
  \<open> syntax error found at .. \<close>
  \<comment> \<open> [FIDELITY] a bounded range requires its lower endpoint. \<close>

urust_expr_rejects fidelity \<open> [1,,2] \<close>
  \<open> syntax error: deleting  , <integer> ] \<close>
  \<comment> \<open> [FIDELITY] array literals reject empty elements. \<close>

urust_expr_rejects fidelity \<open> [1 2] \<close>
  \<open> syntax error found at <integer> \<close>
  \<comment> \<open> [FIDELITY] array elements require commas. \<close>

urust_expr_rejects fidelity \<open> [1, 2 \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] array literals require a closing bracket. \<close>

urust_expr_rejects fidelity \<open> xs[] \<close>
  \<open> syntax error found at ] \<close>
  \<comment> \<open> [FIDELITY] indexing requires a subscript expression. \<close>

urust_expr_rejects fidelity \<open> xs[0 \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] indexing requires a closing bracket. \<close>

urust_expr_rejects fidelity \<open> xs[0, 1] \<close>
  \<open> syntax error: deleting  , <integer> ] \<close>
  \<comment> \<open> [FIDELITY] one indexing postfix contains exactly one expression. \<close>

section\<open> Numeric tuple projections \<close>

text\<open>
Numeric tuple labels are canonical unsuffixed decimal tokens from \<open>0\<close> through
\<open>15\<close>. Tuple projections remain value-only and therefore do not become
assignment places.
\<close>

urust_expr_rejects fidelity \<open> pair.16 \<close>
  \<open> invalid tuple projection index "16" (expected an unsuffixed decimal integer from 0 through 15) \<close>

urust_expr_rejects fidelity \<open> pair.00 \<close>
  \<open> invalid tuple projection index "00" (expected an unsuffixed decimal integer from 0 through 15) \<close>

urust_expr_rejects fidelity \<open> pair.01 \<close>
  \<open> invalid tuple projection index "01" (expected an unsuffixed decimal integer from 0 through 15) \<close>

urust_expr_rejects fidelity \<open> pair.0x1 \<close>
  \<open> invalid tuple projection index "0x1" (expected an unsuffixed decimal integer from 0 through 15) \<close>

urust_expr_rejects fidelity \<open> pair.1u8 \<close>
  \<open> invalid tuple projection index "1u8" (expected an unsuffixed decimal integer from 0 through 15) \<close>

urust_expr_rejects fidelity \<open> pair.1_u8 \<close>
  \<open> invalid tuple projection index "1_u8" (expected an unsuffixed decimal integer from 0 through 15) \<close>

urust_expr_rejects fidelity \<open> pair. \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity \<open> pair.-1 \<close>
  \<open> syntax error found at - \<close>

urust_expr_rejects fidelity \<open> pair.0() \<close>
  \<open> syntax error found at ( \<close>

urust_expr_rejects fidelity \<open> pair.0 = rhs \<close>
  \<open> invalid assignment target \<close>

urust_expr_rejects fidelity \<open> pair.0 += rhs \<close>
  \<open> invalid assignment target \<close>

section\<open> If-let and let-else \<close>

subsection\<open> Required delimiters and whole input \<close>

urust_expr_rejects fidelity
  \<open> if let Some(value) Some(1) { value } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] the pattern and scrutinee require an equals delimiter. \<close>

urust_expr_rejects fidelity
  \<open> if let Some(value) = Some(1) value \<close>
  \<open> syntax error found at <identifier> \<close>
  \<comment> \<open> [FIDELITY] the success branch requires braces. \<close>

urust_expr_rejects fidelity
  \<open> if let Some(value) = Some(1) { value \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] an unterminated success branch cannot consume EOF. \<close>

urust_expr_rejects fidelity
  \<open> if let Some(value) = Some(1) { value } else 0 \<close>
  \<open> syntax error found at <integer> \<close>
  \<comment> \<open> [FIDELITY] the fallback branch also requires braces. \<close>

new_urust_rejects audit
  \<open> if true { () } else if let Some(value) Some(()) { () } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a chained conditional binding still requires an equals delimiter. \<close>

new_urust_rejects audit
  \<open> if true { () } else if false () \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] an ordinary chained arm requires a block. \<close>

new_urust_rejects audit
  \<open> if true { () } else if let Some(value) = Some(()) value \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a chained conditional-binding arm requires a success block. \<close>

new_urust_rejects audit
  \<open> if true { () } else if \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a dangling ordinary chained arm cannot consume EOF. \<close>

new_urust_rejects audit
  \<open> if true { () } else if let \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a dangling conditional-binding arm cannot consume EOF. \<close>

new_urust_rejects audit
  \<open>
    if true { () }
    else if let Some(value) = Some(()) { let _ = value; () }
    else { () }
    trailing trailing
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a complete mixed chain does not hide trailing input. \<close>

urust_expr_rejects fidelity
  \<open> let Some(value) = Some(1) { 0 }; value \<close>
  \<open> syntax error found at { \<close>
  \<comment> \<open> [FIDELITY] a refutable conditional binding requires \<open>else\<close>. \<close>

urust_expr_rejects fidelity
  \<open> let Some(value) = Some(1) else 0; value \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] the \<open>else\<close> body requires braces. \<close>

urust_expr_rejects fidelity
  \<open> let Some(value) = Some(1) else { 0 } value \<close>
  \<open> syntax error found at <identifier> \<close>
  \<comment> \<open> [FIDELITY] \<open>let ... else\<close> requires a semicolon before its continuation. \<close>

urust_expr_rejects fidelity
  \<open> let Some(value) = Some(1) else { 0 }; \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] the frontend form requires a continuation after that semicolon. \<close>

urust_expr_rejects fidelity
  \<open> if let Some(value) = Some(1) { value } trailing trailing \<close>
  \<open> syntax error found at <identifier> \<close>
  \<comment> \<open> [FIDELITY] semicolon-free sequencing still consumes exactly one following statement. \<close>

urust_expr_rejects fidelity
  \<open> if let Some(value) = Some(1) { value } + 1 \<close>
  \<open> syntax error found at + \<close>
  \<comment> \<open> [FIDELITY] a bare conditional-let is not a binary operand. \<close>

urust_expr_rejects fidelity
  \<open> if let Some(value) = Some(1) { value } = rhs \<close>
  \<open> syntax error found at = \<close>
  \<comment> \<open> [FIDELITY] grouping is required before any attempted assignment-target validation. \<close>

subsection\<open> Pattern validation and fallback diagnostics \<close>

urust_expr_rejects fidelity
  \<open> if let 0 = \<llangle>0 :: nat\<rrangle> { () } else { () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] case numerals retain the frontend rejection. \<close>

urust_expr_rejects fidelity
  \<open>
    if let (&left, right) =
      (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      left
    } else {
      0
    }
  \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] the frontend's syntactic top-level tuple exception remains an irrefutable
       binding path, where reference-pattern wrappers are unsupported. \<close>

urust_expr_rejects fidelity
  \<open>
    let (left, &right) =
      (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) else { 0 };
    right
  \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] top-level tuple \<open>let ... else\<close> uses the same non-case binding path. \<close>

new_urust_rejects audit
  \<open>
    if let Some((value, value)) =
      \<llangle>Some (1 :: nat, (2 :: nat, TNil))\<rrangle> {
      value
    } else {
      0
    }
  \<close>
  \<open> duplicate pattern binder "value" \<close>
  \<comment> \<open> [AUDIT] conditional-let patterns share atomic duplicate-binder validation. \<close>

new_urust_rejects divergent
  \<open>
    let Some(value) | None = \<llangle>Some (1 :: nat)\<rrangle> else { 0 };
    value
  \<close>
  \<open> or-pattern alternative is missing binder "value" \<close>
  \<comment> \<open> [DIVERGENT] all alternatives must bind the continuation's same names. \<close>

urust_expr_rejects fidelity
  \<open>
    if let _ = \<llangle>1 :: nat\<rrangle> {
      1
    } else {
      unknown_total_fallback!()
    }
  \<close>
  \<open> unknown macro "unknown_total_fallback!" \<close>
  \<comment> \<open> [AUDIT] a discarded total-pattern fallback is still lowered and diagnosed. \<close>

urust_expr_rejects fidelity
  \<open>
    if let Some(_) = \<llangle>Some (1 :: nat)\<rrangle> {
      1
    } else {
      unknown_partial_fallback!()
    }
  \<close>
  \<open> unknown macro "unknown_partial_fallback!" \<close>
  \<comment> \<open> [FIDELITY] partial-pattern fallback diagnostics remain active. \<close>

urust_expr_rejects fidelity
  \<open>
    if let (Some(value), other) =
      (\<llangle>Some (1 :: nat)\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      value
    } else {
      other
    }
  \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] the frontend's top-level tuple path is irrefutable-binding syntax. \<close>

section\<open> Fueled loops \<close>

urust_expr_rejects fidelity
  \<open> for Some(value) in \<llangle>[Some (1 :: nat)]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [FIDELITY] \<open>for\<close> uses the frontend's irrefutable binder shape. \<close>

urust_expr_rejects fidelity
  \<open> for true in \<llangle>[True]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [FIDELITY] literal loop binders are rejected at the pattern site. \<close>

urust_expr_rejects fidelity
  \<open> for whole @ value in \<llangle>[1 :: nat]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [FIDELITY] aliases remain unsupported in \<open>for\<close> binders. \<close>

urust_expr_rejects fidelity
  \<open> for &value in \<llangle>[1 :: nat]\<rrangle> { () } \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] reference-pattern syntax has no current loop-binding semantics. \<close>

new_urust_rejects divergent
  \<open> for None in \<llangle>[None :: nat option]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [DIVERGENT] a known nullary constructor is resolved before binder classification. \<close>

new_urust_rejects divergent
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x } \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [DIVERGENT] all alternatives of one source arm must bind the same names and modes. \<close>

new_urust_rejects divergent
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, ..] | [] if True \<Rightarrow> True, _ \<Rightarrow> False } \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [DIVERGENT] nested slice alternatives obey the same exact binder-set rule. \<close>

urust_expr_rejects fidelity \<open> while (true) { () } \<close>
  \<open> while \<close>
  \<comment> \<open> [FIDELITY] \<open>while\<close> requires the existing frontend's fuel annotation. \<close>

urust_expr_rejects fidelity \<open> while let Some(value) = Some(1) { () } \<close>
  \<open> while \<close>
  \<comment> \<open> [FIDELITY] \<open>while let\<close> also requires a fuel annotation. \<close>

urust_expr_rejects fidelity \<open> loop { () } \<close>
  \<open> loop \<close>
  \<comment> \<open> [FIDELITY] unconditional \<open>loop\<close> also requires fuel. \<close>

urust_expr_rejects fidelity \<open> #[fuel(1)] loop { () } \<close>
  \<open> <integer> \<close>
  \<comment> \<open> [FIDELITY] fuel must use an expression antiquotation, not a numeral. \<close>

urust_expr_rejects fidelity \<open> #[fuel(\<llangle>1 :: nat\<rrangle>)] loop { () } \<close>
  \<open> <value antiquotation> \<close>
  \<comment> \<open> [FIDELITY] a value antiquotation is not a fuel payload. \<close>

new_urust_rejects divergent
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while true { () } \<close>
  \<open> true \<close>
  \<comment> \<open> [DIVERGENT] the dedicated parser requires Rust's condition parentheses; Isabelle's
       mixfix parser accepts this spelling despite displaying parentheses on pretty-print. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } == () \<close>
  \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] a fueled loop needs parentheses in binary operand position. \<close>

urust_expr_rejects fidelity
  \<open> for value in \<llangle>[1 :: nat]\<rrangle> { () } == () \<close>
  \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] a bare \<open>for\<close> loop is not a binary operand. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) =
    \<llangle>Some (1 :: nat)\<rrangle> { () } == () \<close>
  \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] a bare \<open>while let\<close> loop is not a binary operand. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value)
    \<llangle>Some (1 :: nat)\<rrangle> { () } \<close>
  \<open> <value antiquotation> \<close>
  \<comment> \<open> [FIDELITY] the pattern and scrutinee require an equals delimiter. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let 0 =
    \<llangle>0 :: nat\<rrangle> { () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] case numerals retain the existing frontend rejection. \<close>

urust_expr_rejects fidelity
  \<open> for value in \<llangle>[1 :: nat]\<rrangle> { () } 1 2 \<close>
  \<open> syntax error found at <integer> \<close>
  \<comment> \<open> [FIDELITY] semicolon-free sequencing does not admit value juxtaposition. \<close>

section\<open> Full guard bodies \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if let flag = \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a guard binding requires an initializer before its arrow. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if let mut flag = ; true \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a mutable guard binding cannot omit its initializer. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if const FLAG = ; FLAG \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a const guard binding cannot omit its initializer. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if let Some(flag) = Some(true) else { false }; \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a let-else guard requires a continuation after its semicolon. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if let flag = true \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] an ordinary guard binding requires both semicolon and continuation. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if if true { true } else \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a dangling guard fallback cannot terminate at the arm arrow. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if
        #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false { () }
        true
        \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a fueled while guard requires a complete parenthesized head. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if
        #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) Some(()) { () }
        true
        \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a while-let guard head requires its equals delimiter. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if true,
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a complete guard must be terminated by an arm arrow. \<close>

new_urust_rejects audit
  \<open>
    match_case Some(()) {
      Some(_) if true \<Rightarrow> (),
      None \<Rightarrow> ()
    }
    trailing trailing
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [AUDIT] a guarded match cannot hide trailing whole-input tokens. \<close>

urust_expr_rejects fidelity
  \<open>
    match_case Some(()) {
      Some(_) if (); \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> bool \<close>
  \<comment> \<open> [FIDELITY] the complete body parses as a guard, then \<open>Syntax.check_term\<close> rejects its
       non-boolean result. \<close>

section\<open> Second-class closure boundaries \<close>

subsection\<open> Formal syntax and closure bodies \<close>

urust_expr_rejects fidelity
  \<open> |x x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] the closing formal bar is mandatory. \<close>

urust_expr_rejects fidelity
  \<open> || \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a zero-formal closure still requires a body. \<close>

urust_expr_rejects fidelity
  \<open> |x| \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a nonempty formal list cannot terminate at its closing bar. \<close>

urust_expr_rejects fidelity
  \<open> |x,| x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] closure formals do not accept a trailing comma. \<close>

urust_expr_rejects fidelity
  \<open> |x,, y| y \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] an empty formal between commas is malformed. \<close>

urust_expr_rejects fidelity
  \<open> |x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] premature EOF cannot complete the formal delimiter pair. \<close>

urust_expr_rejects fidelity
  \<open> |if| true \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] reserved words are not closure formals. \<close>

urust_expr_rejects fidelity
  \<open> |match| true \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a second reserved-word boundary exercises a control keyword. \<close>

urust_expr_rejects fidelity
  \<open> |_| true \<close>
  \<open> closure formal must be an identifier \<close>
  \<comment> \<open> [FIDELITY] `_` is normalized to the shared wildcard node and rejected by the
       closure-formal gate. \<close>

urust_expr_rejects fidelity
  \<open> |(x)| x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] grouped patterns are not closure formals. \<close>

urust_expr_rejects fidelity
  \<open> |Some(x)| x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] constructor patterns are not closure formals. \<close>

urust_expr_rejects fidelity
  \<open> |mut x| x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] Rust mutable-formal syntax is outside the closure subset. \<close>

urust_expr_rejects fidelity
  \<open> |x: nat| x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] closure formal type annotations are not implemented. \<close>

urust_expr_rejects fidelity
  \<open> || let x = 1; x \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare binding is below the closure-body priority; a block admits it. \<close>

urust_expr_rejects fidelity
  \<open> || if let Some(x) = Some(1) { x } else { 0 } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] bare conditional bindings are not direct closure bodies. \<close>

urust_expr_rejects fidelity
  \<open> || if true { 0 } else if let Some(x) = Some(1) { x } else { 0 } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] conditional bindings are excluded from every bare closure-body arm. \<close>

urust_expr_rejects fidelity
  \<open> || #[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] loop expressions are not direct closure bodies. \<close>

urust_expr_rejects fidelity
  \<open> || (); () \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] direct closure bodies do not admit sequencing. \<close>

urust_expr_rejects fidelity
  \<open> || return \<llangle>1 :: nat\<rrangle> \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] the closure-body return form is the legacy semicolon-bearing spelling. \<close>

urust_expr_rejects fidelity
  \<open> || || \<llangle>1 :: nat\<rrangle> \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure cannot directly be another closure's body. \<close>

subsection\<open> Bare placement and invocation \<close>

urust_expr_rejects fidelity
  \<open> let closure = |x| x; () \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure is not a binding initializer. \<close>

urust_expr_rejects fidelity
  \<open> target = || \<llangle>1 :: nat\<rrangle> \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure is not an assignment RHS. \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>1 :: nat\<rrangle> + || \<llangle>2 :: nat\<rrangle> \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure is not a binary operand. \<close>

urust_expr_rejects fidelity
  \<open> if || true { () } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure is not a condition. \<close>

urust_expr_rejects fidelity
  \<open> match || true { _ \<Rightarrow> () } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure is not a match scrutinee. \<close>

urust_expr_rejects fidelity
  \<open> for item in || [] { () } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure is not an iterable. \<close>

urust_expr_rejects fidelity
  \<open>
    match true {
      true \<Rightarrow> || true,
      false \<Rightarrow> || false
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] a bare closure is not a match-arm body. \<close>

urust_expr_rejects fidelity
  \<open> || \<llangle>1 :: nat\<rrangle>; () \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] an unparenthesized closure cannot be the left side of sequencing. \<close>

urust_expr_rejects fidelity
  \<open> (|| \<llangle>1 :: nat\<rrangle>)() \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] grouping does not enable general expression invocation. \<close>

urust_expr_rejects fidelity
  \<open>
    match_case Some(()) {
      Some(_) if || true \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> bool \<close>
  \<comment> \<open> [FIDELITY] a closure is a complete guard body syntactically, then ordinary checking
       rejects the non-boolean guard result. \<close>


section\<open> Cast targets, placement, and recovery boundaries \<close>

subsection\<open> Unsupported targets \<close>

urust_expr_rejects fidelity \<open> value as u128 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as i8 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as i16 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as i128 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as isize \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as f32 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as f64 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as char \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as bool \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as Target \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as Target::Word \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as Vec::<u8> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as *const i32 \<close>
  \<open> syntax error found at <signed cast type> \<close>

urust_expr_rejects fidelity \<open> value as *mut i64 \<close>
  \<open> syntax error found at <signed cast type> \<close>

urust_expr_rejects fidelity \<open> value as *const bool \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as *mut Target \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as *mut u128 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as *const *const u8 \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as &u8 \<close>
  \<open> syntax error found at & \<close>

subsection\<open> Missing and malformed cast components \<close>

urust_expr_rejects fidelity \<open> as u8 \<close>
  \<open> syntax error found at as \<close>

urust_expr_rejects fidelity \<open> value as \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity \<open> value as * \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity \<open> value as *const \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity \<open> value as *mut \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity \<open> value as const u8 \<close>
  \<open> syntax error found at const \<close>

urust_expr_rejects fidelity \<open> value as mut u8 \<close>
  \<open> syntax error found at mut \<close>

urust_expr_rejects fidelity \<open> value as **const u8 \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as *const const u8 \<close>
  \<open> syntax error found at const \<close>

urust_expr_rejects fidelity \<open> value as *mut mut u8 \<close>
  \<open> syntax error found at mut \<close>

urust_expr_rejects fidelity \<open> value as as u8 \<close>
  \<open> syntax error found at as \<close>

urust_expr_rejects fidelity \<open> value as u8 as \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity \<open> value as u8 as *const \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity \<open> value as () \<close>
  \<open> syntax error found at ( \<close>

urust_expr_rejects fidelity \<open> value as [u8] \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as u8, \<close>
  \<open> syntax error found at , \<close>

urust_expr_rejects fidelity \<open> value as u8 trailing \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value asu8 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as U8 \<close>
  \<open> syntax error found at <identifier> \<close>

urust_expr_rejects fidelity \<open> value as u8_u16 \<close>
  \<open> syntax error found at <identifier> \<close>

subsection\<open> Invalid source types and cast chains \<close>

urust_expr_rejects fidelity \<open> true as u8 \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> 1_u32 as *const u8 \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity
  \<open> \<llangle>undefined :: ('addr, 'gv) gref\<rrangle> as u8 \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity
  \<open>
    \<llangle>undefined :: ('addr, 'gv, 32 word) Global_Store.ref\<rrangle>
      as *mut u8
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> 1_u32 as u8 as *const u16 \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity
  \<open>
    \<llangle>undefined :: ('addr, 'gv) gref\<rrangle>
      as *const u8 as u16
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity
  \<open>
    \<llangle>undefined :: ('addr, 'gv) gref\<rrangle>
      as *const u8 as *const u16
  \<close>
  \<open> Type unification failed \<close>

subsection\<open> Cast results require grouping before postfix operations \<close>

urust_expr_rejects fidelity \<open> value as u32.field \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as u32.method() \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as u32[0] \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as u32? \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as u32() \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> value as u8 as u32.field \<close>
  \<open> syntax error \<close>

subsection\<open> Cast results are values, not assignment places \<close>

urust_expr_rejects fidelity \<open> value as u32 = rhs \<close>
  \<open> invalid assignment target \<close>

urust_expr_rejects fidelity \<open> (value as u32) = rhs \<close>
  \<open> invalid assignment target \<close>

urust_expr_rejects fidelity \<open> (value as u32) += rhs \<close>
  \<open> invalid assignment target \<close>

subsection\<open> Reserved cast words are not identifiers \<close>

urust_expr_rejects fidelity \<open> let as = 1; as \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> let u8 = 1; u8 \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> let u16 = 1; u16 \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> let u32 = 1; u32 \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> let u64 = 1; u64 \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> let usize = 1; usize \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> let i32 = 1; i32 \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> let i64 = 1; i64 \<close>
  \<open> syntax error \<close>

section\<open> Struct-expression failures (D-21) \<close>

definition negative_d21_identity ::
    \<open>'a \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close>
  where \<open> negative_d21_identity \<equiv> lift_fun1 (\<lambda>value. value) \<close>

definition negative_d21_any ::
    \<open>'a \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
  where \<open> negative_d21_any \<equiv> undefined \<close>

definition negative_d21_pair ::
    \<open>
      64 word \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body
    \<close>
  where \<open> negative_d21_pair \<equiv> lift_fun2 (+) \<close>

micro_rust_notation (call) negative_d21_identity ("NegativeD21One")
micro_rust_notation (call) negative_d21_any ("NegativeD21Any")
micro_rust_notation (call) negative_d21_pair ("NegativeD21Pair")

subsection\<open> Field-list grammar \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair {} \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] struct-expression field lists are nonempty. \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair {, left: 1_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: 1_u64, } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] trailing field commas are not in the active frontend grammar. \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: 1_u64,, right: 2_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: 1_u64; right: 2_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { : 1_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left 1_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: 1_u64 right: 2_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: 1_u64 \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: 1_u64 } } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { 0: 1_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left::nested: 1_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { if: 1_u64 } \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] Rust field shorthand is not supported. \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { left: 1_u64, ..base } \<close>
  \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] Rust rest update is not supported. \<close>

subsection\<open> Head generics and nested failures \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair::<T> { left: 1_u64, right: 2_u64 } \<close>
  \<open> generic arguments are not supported in struct-expression heads \<close>

urust_expr_rejects fidelity
  \<open> Negative::<T>::D21Pair { left: 1_u64, right: 2_u64 } \<close>
  \<open> generic arguments are not supported in struct-expression heads \<close>

urust_expr_rejects fidelity
  \<open>
    NegativeD21Pair {
      left: NegativeD21Pair { inner: },
      right: 2_u64
    }
  \<close>
  \<open> syntax error \<close>

subsection\<open> Shared call arity and type boundary \<close>

urust_expr_rejects fidelity
  \<open> NegativeD21Pair { only: 1_u64 } \<close>
  \<open> no backend matches the use-site type \<close>
  \<comment> \<open> [FIDELITY] too few initializers reach the ordinary call type check. \<close>

urust_expr_rejects fidelity
  \<open>
    NegativeD21Pair {
      first: 1_u64, second: 2_u64, third: 3_u64
    }
  \<close>
  \<open> no backend matches the use-site type \<close>
  \<comment> \<open> [FIDELITY] too many supported-arity initializers fail at the same final type check. \<close>

urust_expr_rejects fidelity
  \<open>
    NegativeD21Pair {
      f00: 0, f01: 1, f02: 2, f03: 3, f04: 4,
      f05: 5, f06: 6, f07: 7, f08: 8, f09: 9,
      f10: 10, f11: 11, f12: 12, f13: 13, f14: 14
    }
  \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] struct expressions share the frontend's inclusive arity-14 cap. \<close>

new_urust_rejects audit
  \<open>
    UnknownArityStruct {
      f00: unknown_arity_initializer!(),
      f01: 1, f02: 2, f03: 3, f04: 4,
      f05: 5, f06: 6, f07: 7, f08: 8, f09: 9,
      f10: 10, f11: 11, f12: 12, f13: 13, f14: 14
    }
  \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> Structural arity wins before label reporting, head resolution, and initializer lowering. \<close>

section\<open> Unparenthesized struct expressions in control heads (D-23) \<close>

text\<open>
Rust excludes an unparenthesized struct expression throughout the outer precedence depth of a
control head. Each row proves that the legacy frontend accepts the former spelling while the
dedicated parser requires an explicit delimiter.
\<close>

subsection\<open> Direct control heads \<close>

new_urust_rejects frontend_accepts
  \<open> if NegativeD21One { value: true } { () } else { () } \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open> || if NegativeD21One { value: true } { () } else { () } \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    if let Some(value) = NegativeD21One { value: Some(()) } {
      value
    } else {
      ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open> for _ in NegativeD21One { value: [()] } { () } \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      NegativeD21One { value: Some(()) } { () }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match NegativeD21One { value: Some(()) } {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_case NegativeD21One { value: Some(()) } {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_switch NegativeD21One { value: \<llangle>0 :: nat\<rrangle> } {
      0 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

subsection\<open> Restricted precedence tiers \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_case NegativeD21One { value: [()] }[0_usize] {
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open> if !NegativeD21One { value: false } { () } \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_case &NegativeD21Any { value: () } {
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_case NegativeD21One { value: 1_u32 } as u64 {
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_case NegativeD21One { value: 1_u64 } + 2_u64 {
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_case 1_u64 + NegativeD21One { value: 2_u64 } {
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    match_case 0_usize..NegativeD21One { value: 2_usize } {
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects frontend_accepts
  \<open>
    let mut slot = 1_u64;
    match_case slot = NegativeD21One { value: 2_u64 } {
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

section\<open> Lexer and whole-input failures \<close>

subsection\<open> Primitive logging \<close>

urust_expr_rejects fidelity
  \<open> \<l>\<o>\<g> \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity
  \<open> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<close>
  \<open> syntax error found at end of input \<close>

urust_expr_rejects fidelity
  \<open>
    \<l>\<o>\<g>
      \<epsilon>\<open>literal Error\<close>
      \<llangle>[]\<rrangle>
  \<close>
  \<open> syntax error found at <expression antiquotation> \<close>

urust_expr_rejects fidelity
  \<open>
    \<l>\<o>\<g>
      \<llangle>Error\<rrangle>
      \<llangle>[]\<rrangle>
      \<llangle>[]\<rrangle>
  \<close>
  \<open> syntax error found at <value antiquotation> \<close>

urust_expr_rejects fidelity
  \<open> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[] \<close>
  \<open> unterminated value antiquotation \<close>

new_urust_rejects audit
  \<open> Foo::<T>::bar() \<close>
  \<open> generic arguments on an intermediate path segment require an exact registration \<close>

new_urust_rejects audit
  \<open> value::<T> \<close>
  \<open> generic arguments on a bare value require an exact literal registration \<close>

new_urust_rejects audit
  \<open> f::<> \<close>
  \<open> syntax error \<close>

new_urust_rejects audit
  \<open> f::<1,>() \<close>
  \<open> syntax error \<close>

new_urust_rejects audit
  \<open> f::<(1]() \<close>
  \<open> unexpected input "]" \<close>

new_urust_rejects audit
  \<open> f::<1() \<close>
  \<open> unterminated turbofish \<close>

subsection\<open> Restricted turbofish grammar \<close>

text\<open>
The legacy frontend admits arbitrary unquoted HOL in generic position. The dedicated parser
intentionally accepts only unsuffixed integers, paths, grouping, and left-associative addition.
\<close>

new_urust_rejects divergent \<open> f::<Suc 4>() \<close> \<open> syntax error \<close>
new_urust_rejects divergent \<open> f::<(1, 2)>() \<close> \<open> syntax error \<close>
new_urust_rejects divergent \<open> f::<[1, 2]>() \<close> \<open> unexpected input "[" \<close>
new_urust_rejects divergent \<open> f::<"text">() \<close> \<open> unexpected input \<close>
new_urust_rejects divergent \<open> f::<STR ''text''>() \<close> \<open> unexpected input \<close>
new_urust_rejects divergent \<open> f::<1 :: nat>() \<close> \<open> syntax error \<close>
new_urust_rejects divergent \<open> f::<a < b>() \<close> \<open> unexpected input "<" \<close>
new_urust_rejects divergent \<open> f::<a << b>() \<close> \<open> unexpected input "<" \<close>
new_urust_rejects divergent \<open> f::<a & b>() \<close> \<open> unexpected input "&" \<close>
new_urust_rejects divergent \<open> f::<a && b>() \<close> \<open> unexpected input "&" \<close>
new_urust_rejects divergent \<open> f::<a % b>() \<close> \<open> unexpected input "%" \<close>
new_urust_rejects divergent \<open> f::<a ^ b>() \<close> \<open> unexpected input "^" \<close>
new_urust_rejects divergent \<open> f::<-a>() \<close> \<open> unexpected input "-" \<close>
new_urust_rejects divergent \<open> f::<a - b>() \<close> \<open> unexpected input "-" \<close>
new_urust_rejects divergent \<open> f::<a * b>() \<close> \<open> unexpected input "*" \<close>
new_urust_rejects divergent \<open> f::<a / b>() \<close> \<open> unexpected input "/" \<close>
new_urust_rejects divergent \<open> f::<a div b>() \<close> \<open> syntax error \<close>
new_urust_rejects divergent \<open> f::<a mod b>() \<close> \<open> syntax error \<close>
new_urust_rejects divergent \<open> f::<\<clubsuit>>() \<close> \<open> unexpected input \<close>
new_urust_rejects divergent
  \<open> f::<\<open>opaque\<close>>() \<close>
  \<open> unexpected input \<close>
new_urust_rejects divergent
  \<open> f::<\<epsilon>\<open>1\<close>>() \<close>
  \<open> unexpected input \<close>
new_urust_rejects divergent
  \<open> f::<1 // comments are not generic trivia
       + 2>() \<close>
  \<open> unexpected input "/" \<close>

new_urust_rejects audit \<open> f::<,1>() \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> f::<1,,2>() \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> f::<1,>() \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> f::<1 a>() \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> f::<1 +>() \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> f::<* 1>() \<close> \<open> unexpected input "*" \<close>
new_urust_rejects audit \<open> f::<->() \<close> \<open> unexpected input "-" \<close>
new_urust_rejects audit \<open> f::<((1)>() \<close> \<open> syntax error \<close>
new_urust_rejects audit \<open> f::<1)>() \<close> \<open> syntax error \<close>
new_urust_rejects audit
  \<open> f::<1>>() \<close>
  \<open> generic arguments on a bare value require an exact literal registration \<close>
new_urust_rejects divergent \<open> f::<1u8>() \<close> \<open> syntax error \<close>
new_urust_rejects divergent \<open> f::<0xff_u8>() \<close> \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> "bad\q" \<close> \<open> bad escape character in string \<close>
  \<comment> \<open> [FIDELITY] malformed escapes are rejected by the same Isabelle string decoder. \<close>

urust_expr_rejects fidelity \<open> "unterminated \<close> \<open> malformed or unterminated string literal \<close>
  \<comment> \<open> [FIDELITY] the opening quote receives a positioned lexer diagnostic. \<close>

urust_expr_rejects fidelity \<open> \<llangle>1 :: nat \<close> \<open> unterminated value antiquotation \<close>
  \<comment> \<open> [FIDELITY] EOF in a value antiquotation is diagnosed at its opening delimiter. \<close>

ML\<open>
local
  fun expect_rejection text expected =
    (case Exn.result
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source text)) () of
       Exn.Res _ => error ("expected direct parser rejection containing " ^ quote expected)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn
           in
             if String.isSubstring expected message then ()
             else error ("expected direct parser rejection containing " ^ quote expected ^
               ", but got " ^ quote message)
           end)
  val _ =
    expect_rejection ("\<epsilon>" ^ Symbol.open_ ^ "True")
      "unterminated expression antiquotation"
  val _ =
    ignore
      (Parser_Test_Elaboration.expression \<^context>
        (Parser_Lex_Util.text_source "()"))
in end
\<close>

urust_expr_rejects fidelity
  \<open> match_case true { \<epsilon>\<open>Bool_Type.true\<close> \<Rightarrow> () } \<close>
  \<open> <expression antiquotation> => \<close>
  \<comment> \<open> [FIDELITY] expression antiquotation remains expression-only. \<close>

urust_expr_rejects fidelity \<open> 1 @ 2 \<close> \<open> syntax error found at @ \<close>
  \<comment> \<open> [FIDELITY] \<open>@\<close> is pattern-only; expression position rejects it after lexing. \<close>

urust_expr_rejects fidelity
  \<open> match true { true => => () } \<close>
  \<open> syntax error: deleting  => ( ) \<close>
  \<comment> \<open> [FIDELITY] generated ML-Yacc arrow names are rendered as their source spelling. \<close>

urust_expr_rejects fidelity \<open> { () \<close> \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] unbalanced brace -- input must be consumed to EOF by a complete derivation. \<close>

urust_expr_rejects fidelity \<open> { ; } \<close> \<open> syntax error found at ; \<close>
  \<comment> \<open> [FIDELITY] a block cannot begin with a standalone semicolon. \<close>

urust_expr_rejects fidelity \<open> \<close> \<open> empty expression \<close>
  \<comment> \<open> [FIDELITY] \<open>parse_source\<close> returns NONE on blank input; the frontend's empty bracket is an
       inner-syntax error. \<close>


chapter\<open>Regression audits\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

section\<open> Frontend-shape structural audit \<close>

text\<open>
Guarded case compilation must reproduce the existing frontend's expanded term directly. In
particular, the scrutinee is evaluated once, source handlers are duplicated across expanded
or-alternatives exactly as in the frontend, and a false source guard enters the next source arm rather
than retrying a sibling alternative. No parser-private HOL constant may mediate that term shape.
\<close>

datatype cycle1_case =
    Cycle1_A | Cycle1_B

consts
  cycle1_scrutinee :: cycle1_case
  cycle1_guard_marker :: \<open>nat \<Rightarrow> bool\<close>
  cycle1_first_body :: nat
  cycle1_next_body :: nat
  cycle1_last_body :: nat
  cycle1_while_body_marker :: unit

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 1 pattern audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source source)

    fun antiquotation source =
      "\<llangle>" ^ source ^ "\<rrangle>"

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_named_constant base_name term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if Long_Name.base_name name = base_name
              then Integer.add 1
              else I
          | _ => I)
        term 0

    fun conditional_branches term =
      let
        fun collect
            (Const (name, _) $ condition $ then_branch $ else_branch) branches =
              let
                val nested =
                  collect condition
                    (collect then_branch
                      (collect else_branch branches))
              in
                if name = \<^const_name>\<open>two_armed_conditional\<close>
                then (condition, then_branch, else_branch) :: nested
                else nested
              end
          | collect (left $ right) branches =
              collect left (collect right branches)
          | collect (Abs (_, _, body)) branches =
              collect body branches
          | collect _ branches = branches
      in collect term [] end

    val fallthrough =
      checked
        ("match " ^ antiquotation "cycle1_scrutinee" ^ " { " ^
         "Cycle1_A | Cycle1_B if " ^
         antiquotation "cycle1_guard_marker 99" ^ " \<Rightarrow> " ^
         antiquotation "cycle1_first_body" ^
         ", Cycle1_B \<Rightarrow> " ^ antiquotation "cycle1_next_body" ^
         ", _ \<Rightarrow> " ^ antiquotation "cycle1_last_body" ^ " }")
    val _ =
      audit_assert "the guarded match did not bind its scrutinee exactly once"
        (count_constant \<^const_name>\<open>cycle1_scrutinee\<close> fallthrough = 1)
    val _ =
      audit_assert "the guarded source body did not retain frontend expansion"
        (count_constant \<^const_name>\<open>cycle1_first_body\<close> fallthrough = 2)
    val _ =
      audit_assert "the term contains a parser-private administrative constant"
        (count_named_constant "urust_admin_let" fallthrough = 0)
    val guarded =
      filter
        (fn (_, then_branch, _) =>
          count_constant \<^const_name>\<open>cycle1_first_body\<close>
            then_branch > 0)
        (conditional_branches fallthrough)
    val _ =
      audit_assert "the direct term contains no source-guard false branch"
        (not (null guarded))
    val _ =
      List.app
        (fn (_, _, else_branch) =>
          (audit_assert
             "a false source guard retried a sibling or-alternative"
             (count_constant \<^const_name>\<open>cycle1_first_body\<close>
                else_branch = 0);
           audit_assert
             "a false source guard did not continue with the next source arm"
             (count_constant \<^const_name>\<open>cycle1_next_body\<close>
                else_branch > 0)))
        guarded
  in
    val _ = ()
  end
\<close>

section\<open> Full guard-body grammar audit \<close>

text\<open>
Match guards reuse the complete non-nullable body grammar. This audit checks the AST before
elaboration, including branches whose final type is intentionally not boolean.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>
    val arm_prefix = "match_case Some(()) { Some(_) if "
    val arm_suffix = " => (), None => (), }"

    fun audit_assert message condition =
      if condition then ()
      else error ("full guard-body grammar audit: " ^ message)

    fun source_text guard = arm_prefix ^ guard ^ arm_suffix

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "full guard-body grammar audit: empty parse")

    fun guard_of source =
      (case parse source of
         UE_Match
           (MF_Case, _,
            UR_Arm (_, SOME (guard, if_pos), UE_Unit _) ::
              UR_Arm (_, NONE, UE_Unit _) :: [],
            _) =>
           (guard, if_pos)
       | _ =>
           error
             "full guard-body grammar audit: wrapper AST changed")

    fun parse_guard guard =
      guard_of
        (Parser_Lex_Util.text_source (source_text guard))

    fun check_guard label guard expected =
      let val (expression, _) = parse_guard guard
      in
        audit_assert (label ^ " AST changed") (expected expression)
      end

    fun is_true (UE_Literal (LP_Bool (true, _))) = true
      | is_true _ = false

    fun is_unit (UE_Unit _) = true
      | is_unit _ = false

    fun is_path name (UE_Path path) = render_path path = name
      | is_path _ _ = false

    val _ = check_guard "terminal value" "true" is_true
    val _ =
      check_guard "semicolon value sequence" "(); true"
        (fn UE_Seq (left, right) =>
              is_unit left andalso is_true right
          | _ => false)
    val _ =
      check_guard "terminal statement" "();"
        (fn UE_Seq (left, right) =>
              is_unit left andalso is_unit right
          | _ => false)
    val _ =
      check_guard "block prefix" "{ () } true"
        (fn UE_Seq (UE_Block (body, _), right) =>
              is_unit body andalso is_true right
          | _ => false)
    val _ =
      check_guard "unsafe-block prefix" "unsafe { () } true"
        (fn UE_Seq (UE_Block (body, _), right) =>
              is_unit body andalso is_true right
          | _ => false)
    val _ =
      check_guard "conditional prefix"
        "if false { () } else { () } true"
        (fn UE_Seq (UE_If _, right) => is_true right
          | _ => false)
    val _ =
      check_guard "while prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) { () } true")
        (fn UE_Seq (UE_While _, right) => is_true right
          | _ => false)
    val _ =
      check_guard "loop prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } true")
        (fn UE_Seq (UE_Loop _, right) => is_true right
          | _ => false)
    val _ =
      check_guard "for prefix"
        "for item in values { () } true"
        (fn UE_Seq (UE_For (P_Ident ("item", _), _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "while-let prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
         "Some(item) = Some(()) { () } true")
        (fn UE_Seq
              (UE_WhileLet
                (_, P_Constr (path, [P_Ident ("item", _)]),
                 _, _, _),
               right) =>
              render_path path = "Some" andalso is_true right
          | _ => false)
    val _ =
      check_guard "bare-match prefix"
        "match true { true => (), false => () } true"
        (fn UE_Seq (UE_Match (MF_Auto, _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "explicit case-match prefix"
        "match_case Some(()) { Some(value) => value, None => () } true"
        (fn UE_Seq (UE_Match (MF_Case, _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "explicit switch-match prefix"
        "match_switch 0 { 0 => (), _ => () } true"
        (fn UE_Seq (UE_Match (MF_Switch, _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "let binding"
        "let flag = true; flag"
        (fn UE_Let (P_Ident ("flag", _), value, body) =>
              is_true value andalso is_path "flag" body
          | _ => false)
    val _ =
      check_guard "mutable binding"
        "let mut flag = true; true"
        (fn UE_LetMut (P_Ident ("flag", _), value, body, _) =>
              is_true value andalso is_true body
          | _ => false)
    val _ =
      check_guard "const binding"
        "const FLAG = true; FLAG"
        (fn UE_Const (P_Ident ("FLAG", _), value, body) =>
              is_true value andalso is_path "FLAG" body
          | _ => false)
    val _ =
      check_guard "let-else binding"
        "let Some(flag) = Some(true) else { false }; flag"
        (fn UE_LetElse
              (P_Constr (path, [P_Ident ("flag", _)]),
               _, UE_Block (fallback, _), body, _) =>
              render_path path = "Some" andalso is_path "flag" body andalso
                (case fallback of
                   UE_Literal (LP_Bool (false, _)) => true
                 | _ => false)
          | _ => false)
    val _ =
      check_guard "right-associated bindings"
        "let first = true; const SECOND = first; SECOND"
        (fn UE_Let
              (P_Ident ("first", _), _,
               UE_Const
                 (P_Ident ("SECOND", _), first, second)) =>
              is_path "first" first andalso is_path "SECOND" second
          | _ => false)
    val _ =
      check_guard "if-let value"
        "if let Some(flag) = Some(true) { flag } else { false }"
        (fn UE_IfLet
              (P_Constr (path, [P_Ident ("flag", _)]),
               _, UE_Block (body, _),
               SOME (UE_Block (UE_Literal (LP_Bool (false, _)), _)), _) =>
              render_path path = "Some" andalso is_path "flag" body
          | _ => false)
    val _ =
      check_guard "legacy return with operand" "return true;"
        (fn UE_Return (SOME value, _) => is_true value
          | _ => false)
    val _ =
      check_guard "legacy operandless return" "return;"
        (fn UE_Return (NONE, _) => true
          | _ => false)
    val _ =
      check_guard "tail return" "return true"
        (fn UE_Return (SOME value, _) => is_true value
          | _ => false)

    val positioned_guard =
      "if let Some(flag) = Some(true) { flag } else { false }"
    val positioned_text = source_text positioned_guard
    val positioned_start =
      Position.make0 17 80 200 "" "" "full-guard-body-ast-audit"
    val (positioned_ast, arm_if_pos) =
      guard_of
        (Parser_Lex_Util.positioned_content_source
          positioned_text positioned_start)
    val arm_if_raw = size arm_prefix - size "if "
    val guard_stop_raw = size arm_prefix + size positioned_guard
    fun position_at raw =
      Position.symbol_explode
        (String.substring (positioned_text, 0, raw))
        positioned_start
    val _ =
      audit_assert "guard keyword position moved"
        (Position.offset_of arm_if_pos =
          Position.offset_of (position_at arm_if_raw))
    val _ =
      (case positioned_ast of
         UE_IfLet (_, _, _, _, span) =>
           (audit_assert "if-let guard span start moved"
              (Position.offset_of span =
                Position.offset_of (position_at (size arm_prefix)));
            audit_assert "if-let guard span stopped before the arrow"
              (Position.end_offset_of span =
                Position.offset_of (position_at guard_stop_raw)))
       | _ =>
           error
             "full guard-body grammar audit: positioned if-let AST changed")

    val positioned_let_else =
      "let Some(flag) = Some(true) else { false }; flag"
    val positioned_let_else_text = source_text positioned_let_else
    val (positioned_let_else_ast, _) =
      guard_of
        (Parser_Lex_Util.positioned_content_source
          positioned_let_else_text positioned_start)
    val positioned_let_else_stop =
      Position.symbol_explode
        (String.substring
          (positioned_let_else_text, 0,
           size arm_prefix + size positioned_let_else))
        positioned_start
    val _ =
      (case positioned_let_else_ast of
         UE_LetElse (_, _, _, _, span) =>
           (audit_assert "let-else guard span start moved"
              (Position.offset_of span =
                Position.offset_of (position_at (size arm_prefix)));
            audit_assert "let-else guard span stopped before the arrow"
              (Position.end_offset_of span =
                Position.offset_of positioned_let_else_stop))
       | _ =>
           error
             "full guard-body grammar audit: positioned let-else AST changed")

    val non_boolean_source = source_text "();"
    val (non_boolean_ast, _) =
      guard_of (Parser_Lex_Util.text_source non_boolean_source)
    val _ =
      audit_assert "non-boolean terminal statement did not parse"
        (case non_boolean_ast of
           UE_Seq (left, right) =>
             is_unit left andalso is_unit right
         | _ => false)
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source non_boolean_source)) () of
         Exn.Res _ =>
           error
             "full guard-body grammar audit: non-boolean guard type-checked"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "non-boolean guard failed outside boolean checking"
               (String.isSubstring "bool" (Runtime.exn_message exn)))
  in
    val _ = writeln "Full guard-body grammar audit passed"
  end
\<close>

section\<open> Conservative while-let coverage \<close>

text\<open>
C1-I6 removes the false continuation only for coverage proved by the resolved-pattern metadata.
The condition still sequences the source body with true, and the bounded loop body remains skip.
Partial patterns retain exactly one false fallback.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 1 while-let audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source source)

    fun antiquotation source =
      "\<llangle>" ^ source ^ "\<rrangle>"

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun loop_source pattern scrutinee =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
      pattern ^ " = " ^ scrutinee ^ " { let _ = " ^
      antiquotation "cycle1_while_body_marker" ^ "; () }"

    fun bounded_while_arguments term =
      let
        fun find
            (Const (name, _) $ fuel $ condition $ body) =
              if name = \<^const_name>\<open>bounded_while\<close>
              then SOME (fuel, condition, body)
              else
                get_first find [fuel, condition, body]
          | find (left $ right) =
              (case find left of
                 SOME result => SOME result
               | NONE => find right)
          | find (Abs (_, _, body)) = find body
          | find _ = NONE
      in
        (case find term of
           SOME result => result
         | NONE => error "Cycle 1 while-let audit: bounded_while was not generated")
      end

    fun is_skip term =
      (case Term.strip_comb term of
         (Const (literal_name, _), [Const (unit_name, _)]) =>
           literal_name = \<^const_name>\<open>literal\<close> andalso
             unit_name = \<^const_name>\<open>Product_Type.Unity\<close>
       | _ => false)

    fun check_exhaustive label source =
      let
        val term = checked source
        val (_, condition, body) = bounded_while_arguments term
      in
        audit_assert (label ^ " retained a false fallback")
          (count_constant \<^const_name>\<open>False\<close> term = 0);
        audit_assert (label ^ " moved the source body out of the condition")
          (count_constant
             \<^const_name>\<open>cycle1_while_body_marker\<close>
             condition > 0);
        audit_assert (label ^ " did not keep skip as the bounded loop body")
          (is_skip body)
      end

    val _ =
      check_exhaustive "TNil"
        (loop_source "TNil" "TNil")
    val _ =
      check_exhaustive "complete option family"
        (loop_source "Some(_) | None"
          (antiquotation "Some (1 :: nat)"))
    val _ =
      check_exhaustive "nested complete option family"
        (loop_source "Some(Some(_) | None) | None"
          (antiquotation "Some (None :: nat option)"))

    val partial =
      checked
        (loop_source "Some(_)"
          (antiquotation "None :: nat option"))
    val (_, partial_condition, partial_body) =
      bounded_while_arguments partial
    val _ =
      audit_assert "a partial while-let pattern lost its false fallback"
        (count_constant \<^const_name>\<open>False\<close> partial = 1)
    val _ =
      audit_assert "a partial while-let moved the source body out of the condition"
        (count_constant
           \<^const_name>\<open>cycle1_while_body_marker\<close>
           partial_condition > 0)
    val _ =
      audit_assert "a partial while-let did not keep skip as the bounded loop body"
        (is_skip partial_body)
  in
    val _ = writeln "Cycle 1 conservative while-let coverage audit passed"
  end
\<close>

section\<open> Conditional binding structure and markup \<close>

text\<open>
Certified-total conditional bindings use the same case shape as an explicit complete match and omit
the unreachable fallback only after lowering it. Partial patterns retain the frontend-shaped wildcard
case. These audits also pin mixed-chain pruning, the top-level tuple exception, conservative coverage,
scope, diagnostics, recovery, and editor markup.
\<close>

consts
  conditional_let_scrutinee_marker :: \<open>nat option\<close>
  conditional_let_success_marker :: nat
  conditional_let_fallback_marker :: nat
  conditional_chain_first_scrutinee_marker :: \<open>nat option\<close>
  conditional_chain_second_condition_marker :: bool
  conditional_chain_last_scrutinee_marker :: \<open>nat option\<close>
  conditional_chain_first_success_marker :: nat
  conditional_chain_second_success_marker :: nat
  conditional_chain_last_success_marker :: nat
  conditional_chain_fallback_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("conditional-binding regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "conditional-binding regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse_text text)

    fun path_named name path = render_path path = name
    fun expression_named name (UE_Path path) = path_named name path
      | expression_named _ _ = false
    fun call_named name (UE_Call (UC_Path path, _, _)) =
          path_named name path
      | call_named _ _ = false

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val if_text =
      "if let Some(value) = Some(1) { value } else { 0 }"
    val if_start =
      Position.make0 7 30 0 "" "" "conditional-binding-ast-audit"
    val if_stop =
      Position.symbol_explode if_text if_start
    val if_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          if_text if_start)
    val _ =
      (case if_ast of
         UE_IfLet
           (P_Constr (pattern_path, [P_Ident ("value", _)]),
            call,
            UE_Block (body, _),
            SOME (UE_Block (UE_Literal (LP_Integer ("0", _)), _)),
            position) =>
           (audit_assert "if-let path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "if-let span start moved"
              (Position.offset_of position =
                Position.offset_of if_start);
            audit_assert "if-let span end moved"
              (Position.end_offset_of position =
                Position.offset_of if_stop))
       | _ =>
           error "conditional-binding regression audit: if-let AST changed")

    val mixed_text =
      "if let Some(first) = Some(1) { first } else if false { 2 } " ^
      "else if let Some(last) = Some(3) { last } else { 4 }"
    val mixed_start =
      Position.make0 13 70 0 "" "" "conditional-chain-ast-audit"
    val mixed_stop =
      Position.symbol_explode mixed_text mixed_start
    val mixed_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          mixed_text mixed_start)
    val _ =
      (case mixed_ast of
         UE_IfLet
           (P_Constr (first_pattern_path, [P_Ident ("first", _)]),
            first_call,
            UE_Block (first_body, _),
            SOME
              (UE_If
                (UE_Literal (LP_Bool (false, _)),
                 UE_Block (UE_Literal (LP_Integer ("2", _)), _),
                 SOME
                   (UE_IfLet
                     (P_Constr (last_pattern_path, [P_Ident ("last", _)]),
                      last_call,
                      UE_Block (last_body, _),
                      SOME
                        (UE_Block
                          (UE_Literal (LP_Integer ("4", _)), _)),
                      nested_position)),
                 _)),
            position) =>
           (audit_assert "mixed-chain path structure changed"
              (path_named "Some" first_pattern_path andalso
               call_named "Some" first_call andalso
               expression_named "first" first_body andalso
               path_named "Some" last_pattern_path andalso
               call_named "Some" last_call andalso
               expression_named "last" last_body);
            audit_assert "mixed-chain span start moved"
              (Position.offset_of position =
                Position.offset_of mixed_start);
            audit_assert "mixed-chain span stopped before the final arm"
              (Position.end_offset_of position =
                Position.offset_of mixed_stop);
            audit_assert "nested if-let span stopped before its fallback"
              (Position.end_offset_of nested_position =
                Position.offset_of mixed_stop))
       | _ =>
           error
             "conditional-binding regression audit: mixed-chain AST changed")

    val let_text =
      "let Some(value) = Some(1) else { 0 }; value"
    val let_start =
      Position.make0 11 50 0 "" "" "conditional-binding-ast-audit"
    val let_stop =
      Position.symbol_explode let_text let_start
    val let_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          let_text let_start)
    val _ =
      (case let_ast of
         UE_LetElse
           (P_Constr (pattern_path, [P_Ident ("value", _)]),
            call,
            UE_Block (UE_Literal (LP_Integer ("0", _)), _),
            body,
            position) =>
           (audit_assert "let-else path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "let-else span start moved"
              (Position.offset_of position =
                Position.offset_of let_start);
            audit_assert "let-else span end moved"
              (Position.end_offset_of position =
                Position.offset_of let_stop))
       | _ =>
           error "conditional-binding regression audit: let-else AST changed")

    val mixed_chain =
      checked
        ("if let Some(first) = " ^
         "\<llangle>conditional_chain_first_scrutinee_marker\<rrangle> { " ^
         "let _ = first; " ^
         "\<llangle>conditional_chain_first_success_marker\<rrangle> " ^
         "} else if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else if let Some(last) = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "let _ = last; " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> }")
    val nested_mixed_chain =
      checked
        ("if let Some(first) = " ^
         "\<llangle>conditional_chain_first_scrutinee_marker\<rrangle> { " ^
         "let _ = first; " ^
         "\<llangle>conditional_chain_first_success_marker\<rrangle> " ^
         "} else { if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else { if let Some(last) = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "let _ = last; " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> } } }")
    val _ =
      audit_assert "mixed chain lost right-associated branch order"
        (Term.aconv (mixed_chain, nested_mixed_chain))
    val _ =
      List.app
        (fn (name, label) =>
          audit_assert (label ^ " was not lowered exactly once")
            (count_constant name mixed_chain = 1))
        [(\<^const_name>\<open>conditional_chain_first_scrutinee_marker\<close>,
          "first mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_second_condition_marker\<close>,
          "mixed-chain ordinary condition"),
         (\<^const_name>\<open>conditional_chain_last_scrutinee_marker\<close>,
          "last mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_first_success_marker\<close>,
          "first mixed-chain success branch"),
         (\<^const_name>\<open>conditional_chain_second_success_marker\<close>,
          "mixed-chain ordinary success branch"),
         (\<^const_name>\<open>conditional_chain_last_success_marker\<close>,
          "last mixed-chain success branch"),
         (\<^const_name>\<open>conditional_chain_fallback_marker\<close>,
          "mixed-chain final fallback")]

    val total_mixed_chain =
      checked
        ("if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else if let _ = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> }")
    val explicit_total_mixed_chain =
      checked
        ("if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else { match_case " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> } }")
    val _ =
      audit_assert "a total mixed-chain arm retained its unreachable remainder"
        (Term.aconv (total_mixed_chain, explicit_total_mixed_chain))
    val _ =
      List.app
        (fn (name, expected, label) =>
          audit_assert (label ^ " has the wrong occurrence count")
            (count_constant name total_mixed_chain = expected))
        [(\<^const_name>\<open>conditional_chain_second_condition_marker\<close>,
          1, "total mixed-chain ordinary condition"),
         (\<^const_name>\<open>conditional_chain_second_success_marker\<close>,
          1, "total mixed-chain ordinary success"),
         (\<^const_name>\<open>conditional_chain_last_scrutinee_marker\<close>,
          1, "total mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_last_success_marker\<close>,
          1, "total mixed-chain success"),
         (\<^const_name>\<open>conditional_chain_fallback_marker\<close>,
          0, "total mixed-chain unreachable fallback")]

    val two_armed =
      checked
        ("if let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val explicit_two_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle>, _ \<Rightarrow> " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "two-armed if-let stopped using the explicit case shape"
        (Term.aconv (two_armed, explicit_two_armed))
    val _ =
      audit_assert "if-let lowered its scrutinee more than once"
        (count_constant
          \<^const_name>\<open>conditional_let_scrutinee_marker\<close>
          two_armed = 1)
    val _ =
      audit_assert "if-let lost success/fallback ordering"
        (count_constant
          \<^const_name>\<open>conditional_let_success_marker\<close>
          two_armed = 1 andalso
         count_constant
          \<^const_name>\<open>conditional_let_fallback_marker\<close>
          two_armed = 1)

    val total_two_armed =
      checked
        ("if let _ = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val explicit_total_two_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle> }")
    val _ =
      audit_assert "total if-let did not match a complete case without fallback"
        (Term.aconv (total_two_armed, explicit_total_two_armed))
    val _ =
      audit_assert "total if-let changed scrutinee/success multiplicity"
        (count_constant
           \<^const_name>\<open>conditional_let_scrutinee_marker\<close>
           total_two_armed = 1 andalso
         count_constant
           \<^const_name>\<open>conditional_let_success_marker\<close>
           total_two_armed = 1)
    val _ =
      audit_assert "total if-let retained its unreachable fallback"
        (count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           total_two_armed = 0)

    val one_armed =
      checked
        ("if let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { let _ = " ^
         "\<llangle>conditional_let_success_marker\<rrangle>; () }")
    val explicit_one_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> { let _ = " ^
         "\<llangle>conditional_let_success_marker\<rrangle>; () }, _ \<Rightarrow> () }")
    val _ =
      audit_assert "one-armed if-let lost its skip fallback"
        (Term.aconv (one_armed, explicit_one_armed))
    val _ =
      audit_assert "partial one-armed if-let lost its synthetic skip"
        (count_constant
           \<^const_name>\<open>Product_Type.Unity\<close>
           one_armed = 2)

    val total_one_armed =
      checked
        ("if let value = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { let _ = " ^
         "value; \<llangle>conditional_let_success_marker\<rrangle> }")
    val explicit_total_one_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "value \<Rightarrow> { let _ = value; " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } }")
    val _ =
      audit_assert "total one-armed if-let retained synthetic skip"
        (Term.aconv (total_one_armed, explicit_total_one_armed) andalso
         count_constant
           \<^const_name>\<open>Product_Type.Unity\<close>
           total_one_armed = 0)

    val let_else =
      checked
        ("let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }; " ^
         "\<llangle>value + conditional_let_success_marker\<rrangle>")
    val explicit_let_else =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> " ^
         "\<llangle>value + conditional_let_success_marker\<rrangle>, _ \<Rightarrow> " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "let-else stopped placing its continuation in the success arm"
        (Term.aconv (let_else, explicit_let_else))

    val total_let_else =
      checked
        ("let _ = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }; " ^
         "\<llangle>conditional_let_success_marker\<rrangle>")
    val explicit_total_let_else =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle> }")
    val _ =
      audit_assert "total let-else retained its unreachable fallback"
        (Term.aconv (total_let_else, explicit_total_let_else) andalso
         count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           total_let_else = 0)

    val tuple_if =
      checked
        ("if let (left, right) = " ^
         "(\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { " ^
         "\<llangle>left + right\<rrangle> } else { missing_tuple_audit }")
    val tuple_bind =
      checked
        ("let (left, right) = " ^
         "(\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); " ^
         "\<llangle>left + right\<rrangle>")
    val _ =
      audit_assert "top-level tuple stopped using the frontend's direct binding"
        (Term.aconv (tuple_if, tuple_bind))

    fun conditional_source pattern scrutinee =
      "if let " ^ pattern ^ " = " ^ scrutinee ^ " { " ^
      "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
      "\<llangle>conditional_let_fallback_marker\<rrangle> }"

    fun explicit_case_source pattern scrutinee fallback =
      "match_case " ^ scrutinee ^ " { " ^ pattern ^ " \<Rightarrow> " ^
      "\<llangle>conditional_let_success_marker\<rrangle>" ^
      (if fallback
       then ", _ \<Rightarrow> \<llangle>conditional_let_fallback_marker\<rrangle>"
       else "") ^ " }"

    fun check_total label pattern scrutinee =
      let
        val actual = unchecked (conditional_source pattern scrutinee)
        val explicit =
          unchecked (explicit_case_source pattern scrutinee false)
      in
        audit_assert (label ^ " did not use the complete case shape")
          (Term.aconv (actual, explicit));
        audit_assert (label ^ " retained a fallback")
          (count_constant
             \<^const_name>\<open>conditional_let_fallback_marker\<close>
             actual = 0)
      end

    val _ =
      List.app
        (fn (label, pattern, scrutinee) =>
          check_total label pattern scrutinee)
        [("wildcard totality", "_", "\<llangle>1 :: nat\<rrangle>"),
         ("identifier totality", "value", "\<llangle>1 :: nat\<rrangle>"),
         ("group totality", "(value)", "\<llangle>1 :: nat\<rrangle>"),
         ("alias totality", "whole @ _", "\<llangle>1 :: nat\<rrangle>"),
         ("grouped recursive tuple totality",
          "((left, (middle, right)))",
          "(\<llangle>1 :: nat\<rrangle>, " ^
            "(\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>))"),
         ("sole-constructor totality", "TNil", "TNil"),
         ("complete option totality", "Some(_) | None",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("nested complete option totality",
          "Some(Some(_) | None) | None",
          "\<llangle>Some (Some (1 :: nat))\<rrangle>"),
         ("wildcard-alternative totality", "Some(_) | _",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("borrow-wrapper totality", "&_", "\<llangle>1 :: nat\<rrangle>")]

    fun check_partial label pattern scrutinee =
      let
        val actual = unchecked (conditional_source pattern scrutinee)
        val explicit =
          unchecked (explicit_case_source pattern scrutinee true)
      in
        audit_assert (label ^ " lost the explicit wildcard-case shape")
          (Term.aconv (actual, explicit));
        audit_assert (label ^ " incorrectly discarded its fallback")
          (count_constant
             \<^const_name>\<open>conditional_let_fallback_marker\<close>
             actual > 0)
      end

    val _ =
      List.app
        (fn (label, pattern, scrutinee) =>
          check_partial label pattern scrutinee)
        [("Some-only option coverage", "Some(_)",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("None-only option coverage", "None",
          "\<llangle>None :: nat option\<rrangle>"),
         ("incomplete multi-constructor family",
          "ConditionalLetA(_) | ConditionalLetB(_)",
          "\<llangle>ConditionalLetA 1\<rrangle>"),
         ("internally complete but externally partial family",
          "Some(Some(_) | None)",
          "\<llangle>Some (Some (1 :: nat))\<rrangle>"),
         ("literal pattern", "true", "\<llangle>True\<rrangle>"),
         ("value pattern", "\<llangle>1 :: nat\<rrangle>",
          "\<llangle>1 :: nat\<rrangle>"),
         ("range pattern", "1..=3", "\<llangle>2 :: nat\<rrangle>"),
         ("slice pattern", "[_, ..]", "\<llangle>[1 :: nat, 2]\<rrangle>"),
         ("struct pattern",
          "AdvStruct { adv_left: _, adv_right: _ }",
          "\<llangle>AdvStruct 1 2\<rrangle>"),
         ("nonconstructor path pattern", "Color::Red", "Color::Red"),
         ("constructor with a partial argument", "Some(true)",
          "\<llangle>Some True\<rrangle>"),
         ("or-pattern from different constructor families",
          "Some(_) | ConditionalLetA(_)",
          "\<llangle>Some (1 :: nat)\<rrangle>")]

    val callback_ast =
      parse_text
        ("if let _ = callback_scrutinee { callback_success } " ^
         "else { callback_fallback }")
    val callback_count = Unsynchronized.ref 0
    fun callback_lower _ _ =
      let
        val index = !callback_count + 1
        val _ = callback_count := index
      in
        (case index of
           1 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_scrutinee_marker\<close>
         | 2 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_success_marker\<close>
         | 3 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_fallback_marker\<close>
         | _ =>
             error
               "conditional-binding regression audit: lowering callback called too often")
      end
    val callback_term =
      (case callback_ast of
         UE_IfLet (pattern, scrutinee, success, fallback, position) =>
           URust_Matching.lower_if_let callback_lower ctxt
             URust_Resolution.empty_environment
             (pattern, scrutinee, success, fallback, position)
       | _ =>
           error
             "conditional-binding regression audit: callback fixture AST changed")
    val _ =
      audit_assert "discarded total fallback was not lowered exactly once"
        (!callback_count = 3)
    val _ =
      audit_assert "discarded callback fallback leaked into the final term"
        (count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           callback_term = 0)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("conditional-binding regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
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

    fun expect_positioned_rejection label text start expected needle =
      let
        val (_, position) = token_position text start needle 0
        val expected_here =
          XML.content_of (YXML.parse_body (Position.here position))
      in
        (case Exn.result
            (fn () =>
              Parser_Test_Elaboration.expression ctxt
                (Parser_Lex_Util.positioned_content_source
                  text start)) () of
           Exn.Res _ =>
             error
               ("conditional-binding regression audit: " ^ label ^
                " unexpectedly elaborated")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let
                 val message =
                   XML.content_of
                     (YXML.parse_body (Runtime.exn_message exn))
               in
                 audit_assert (label ^ " changed its diagnostic")
                   (String.isSubstring expected message);
                 audit_assert (label ^ " moved its diagnostic")
                   (String.isSubstring expected_here message)
               end)
      end

    val bad_total_text =
      "if let _ = \<llangle>1 :: nat\<rrangle> { 1 } else { " ^
      "unknown_total_fallback!() }"
    val bad_total_start =
      Position.make0 19 120 900 "" ""
        "conditional-total-fallback-diagnostic-audit"
    val _ =
      expect_positioned_rejection "total fallback"
        bad_total_text bad_total_start
        "unknown macro \"unknown_total_fallback!\""
        "unknown_total_fallback"

    val bad_partial_text =
      "if let Some(_) = \<llangle>Some (1 :: nat)\<rrangle> { 1 } else { " ^
      "unknown_partial_fallback!() }"
    val bad_partial_start =
      Position.make0 23 160 1200 "" ""
        "conditional-partial-fallback-diagnostic-audit"
    val _ =
      expect_positioned_rejection "partial fallback"
        bad_partial_text bad_partial_start
        "unknown macro \"unknown_partial_fallback!\""
        "unknown_partial_fallback"

    val recovered_total =
      checked
        ("if let _ = \<llangle>1 :: nat\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "failed total fallback leaked state into the next command"
        (count_constant
           \<^const_name>\<open>conditional_let_success_marker\<close>
           recovered_total = 1 andalso
         count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           recovered_total = 0)

    val total_markup_text =
      "let outer = \<llangle>1 :: nat\<rrangle>; " ^
      "if let _ = \<llangle>2 :: nat\<rrangle> { 3 } else { outer }"
    val total_markup_start =
      Position.make0 29 200 1600 "" ""
        "conditional-total-fallback-markup-audit"
    val partial_markup_text =
      "let outer = \<llangle>1 :: nat\<rrangle>; " ^
      "if let Some(_) = \<llangle>Some (2 :: nat)\<rrangle> { 3 } " ^
      "else { outer }"
    val partial_markup_start =
      Position.make0 31 220 2000 "" ""
        "conditional-partial-fallback-markup-audit"

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source
                      text start))) ())
          ())
    val _ = capture_elaboration total_markup_text total_markup_start
    val _ = capture_elaboration partial_markup_text partial_markup_start
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    if_text if_start)) ())
          ())
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    mixed_text mixed_start)) ())
          ())
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    let_text let_start)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
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
               "conditional-binding regression audit: binder entity markup changed")
      end

    val (total_outer_offset, total_outer_definition) =
      token_position total_markup_text total_markup_start "outer" 0
    val (_, total_outer_fallback) =
      token_position total_markup_text total_markup_start "outer"
        (total_outer_offset + size "outer")
    val (partial_outer_offset, partial_outer_definition) =
      token_position partial_markup_text partial_markup_start "outer" 0
    val (_, partial_outer_fallback) =
      token_position partial_markup_text partial_markup_start "outer"
        (partial_outer_offset + size "outer")
    val _ =
      audit_assert "discarded total fallback lost outer-scope resolution markup"
        (has_markup Markup.boundN total_outer_fallback andalso
         entity_id Markup.defN total_outer_definition =
           entity_id Markup.refN total_outer_fallback)
    val _ =
      audit_assert "partial fallback outer-scope resolution markup changed"
        (has_markup Markup.boundN partial_outer_fallback andalso
         entity_id Markup.defN partial_outer_definition =
           entity_id Markup.refN partial_outer_fallback)

    val (_, if_keyword) = token_position if_text if_start "if" 0
    val (if_offset, if_let_keyword) =
      token_position if_text if_start "let" 0
    val (if_let_offset, if_equals) =
      token_position if_text if_start "=" (if_offset + 2)
    val (_, if_else_keyword) =
      token_position if_text if_start "else" (if_let_offset + 3)
    val (mixed_else_offset, mixed_else_keyword) =
      token_position mixed_text mixed_start "else" 0
    val (mixed_if_offset, mixed_if_keyword) =
      token_position mixed_text mixed_start "if" (mixed_else_offset + 4)
    val (mixed_second_else_offset, mixed_second_else_keyword) =
      token_position mixed_text mixed_start "else" (mixed_if_offset + 2)
    val (mixed_if_let_offset, mixed_if_let_keyword) =
      token_position mixed_text mixed_start "if"
        (mixed_second_else_offset + 4)
    val (_, mixed_let_keyword) =
      token_position mixed_text mixed_start "let" (mixed_if_let_offset + 2)
    val (_, let_semicolon) =
      token_position let_text let_start ";" 0
    val _ =
      audit_assert "if keyword markup changed"
        (has_markup Markup.keyword1N if_keyword)
    val _ =
      audit_assert "let keyword markup changed"
        (has_markup Markup.keyword1N if_let_keyword)
    val _ =
      audit_assert "equals delimiter markup changed"
        (has_markup Markup.delimiterN if_equals)
    val _ =
      audit_assert "else keyword markup changed"
        (has_markup Markup.keyword1N if_else_keyword)
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " keyword markup changed")
            (has_markup Markup.keyword1N position))
        [(mixed_else_keyword, "mixed-chain else"),
         (mixed_if_keyword, "mixed-chain ordinary if"),
         (mixed_second_else_keyword, "mixed-chain second else"),
         (mixed_if_let_keyword, "mixed-chain if-let if"),
         (mixed_let_keyword, "mixed-chain if-let let")]
    val _ =
      audit_assert "let-else semicolon delimiter markup changed"
        (has_markup Markup.delimiterN let_semicolon)
  in
    val _ = writeln "Conditional-binding structure and markup regressions passed"
  end
\<close>

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
    val expected =
      Syntax.parse_term ctxt
        ("\<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; " ^
         "\<llangle>(\<lambda>x :: nat. x) x\<rrangle> \<rbrakk>")
      |> Syntax.check_term ctxt

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
      audit_assert "checked term differs from the legacy frontend"
        (Term.aconv (actual, expected))
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

section\<open> Positions and pattern grammar \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("parser regression audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "parser regression audit: empty parse")

    fun pattern_source pattern =
      "match_case \<llangle>undefined\<rrangle> { " ^ pattern ^
      " \<Rightarrow> \<llangle>undefined\<rrangle> }"

    fun parse_pattern pattern =
      (case parse (pattern_source pattern) of
         UE_Match (_, _, [UR_Arm (result, NONE, _)], _) => result
       | _ => error "parser regression audit: unexpected pattern AST")

    fun integer text (P_Literal (LP_Integer (actual, _))) =
          actual = text
      | integer _ _ = false

    fun range kind lower upper
        (P_Range (actual_kind, actual_lower, actual_upper, _)) =
          actual_kind = kind andalso
          integer lower actual_lower andalso
          integer upper actual_upper
      | range _ _ _ _ = false

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("parser regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    val _ =
      audit_assert "exclusive range shape changed"
        (range RK_Exclusive "5" "7"
          (parse_pattern "5..7"))
    val _ =
      audit_assert "inclusive range shape changed"
        (range RK_Inclusive "5" "7"
          (parse_pattern "5..=7"))

    val borrow_text = pattern_source "& mut &value"
    val outer_borrow_offset = find_from borrow_text "&" 0
    val inner_borrow_offset = find_from borrow_text "&" (outer_borrow_offset + 1)
    val borrow_start = Position.make0 11 4 0 "" "" ""
    val outer_borrow_position =
      Position.symbol_explode
        (String.substring (borrow_text, 0, outer_borrow_offset))
        borrow_start
    val inner_borrow_position =
      Position.symbol_explode
        (String.substring (borrow_text, 0, inner_borrow_offset))
        borrow_start
    val _ =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.positioned_content_source
            borrow_text borrow_start) of
         SOME
           (UE_Match
             (_, _,
              [UR_Arm
                (P_Borrow
                  (BM_Mut,
                   P_Borrow (BM_Imm, P_Ident ("value", _), inner_pos),
                   outer_pos),
                 NONE, _)],
              _)) =>
           (audit_assert "outer borrow-pattern mode or position changed"
              (Position.offset_of outer_pos =
                Position.offset_of outer_borrow_position);
            audit_assert "inner borrow-pattern mode or position changed"
              (Position.offset_of inner_pos =
                Position.offset_of inner_borrow_position))
       | _ =>
           error
             "parser regression audit: nested borrow-pattern AST changed")

    val _ =
      (case parse_pattern "whole @ 5..=7" of
         P_Alias ("whole", _, inner, _) =>
           audit_assert "alias did not bind the whole range"
             (range RK_Inclusive "5" "7" inner)
       | _ =>
           error "parser regression audit: range alias shape changed")

    val _ =
      (case parse_pattern "outer @ inner @ 5..7" of
         P_Alias ("outer", _,
           P_Alias ("inner", _, nested, _), _) =>
             audit_assert "nested aliases lost right associativity"
               (range RK_Exclusive "5" "7" nested)
       | _ =>
           error "parser regression audit: nested alias shape changed")

    val _ =
      (case parse_pattern "whole @ Some(5..=7)" of
         P_Alias ("whole", _,
           P_Constr (path, [nested]), _) =>
             audit_assert "constructor alias lost its path or range argument"
               (render_path path = "Some" andalso
                range RK_Inclusive "5" "7" nested)
       | _ =>
           error
             "parser regression audit: constructor alias shape changed")

    val _ =
      (case parse_pattern "whole @ Head { field: 5..7 }" of
         P_Alias ("whole", _,
           P_Struct (path,
             [SF_Field ("field", _, nested)]), _) =>
             audit_assert "struct alias lost its path or range field"
               (render_path path = "Head" andalso
                range RK_Exclusive "5" "7" nested)
       | _ =>
           error "parser regression audit: struct alias shape changed")

    val _ =
      (case parse_pattern "left @ 1..2 | right @ 3..=4" of
         P_Or
           ([P_Alias ("left", _, left, _),
             P_Alias ("right", _, right, _)], _) =>
             (audit_assert "exclusive range lost alias precedence"
                (range RK_Exclusive "1" "2" left);
              audit_assert "inclusive range lost alias precedence"
                (range RK_Inclusive "3" "4" right))
       | _ =>
           error
             "parser regression audit: alias/range/or precedence changed")

    val chained_text =
      pattern_source "1..2..3"
    val chained_start =
      Position.make0 7 1 0 "" "" ""

    val first_range =
      find_from chained_text ".." 0
    val second_range =
      find_from chained_text ".." (first_range + 2)
    val second_range_position =
      Position.symbol_explode
        (String.substring (chained_text, 0, second_range))
        chained_start
    val second_range_here =
      XML.content_of
        (YXML.parse_body
          (Position.here second_range_position))
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.positioned_content_source
                chained_text chained_start)) () of
         Exn.Res _ =>
           error
             "parser regression audit: chained range unexpectedly elaborated"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message =
                 XML.content_of
                   (YXML.parse_body
                     (Runtime.exn_message exn))
             in
               audit_assert "chained range missed semantic validation"
                 (String.isSubstring
                   "range patterns are non-associative" message);
               audit_assert "chained range diagnostic moved"
                 (String.isSubstring second_range_here message)
             end)

    fun alternative_name index =
      "regression_alt_" ^ string_of_int index

    fun audit_alternatives count =
      let
        val alternatives =
          space_implode " | "
            (map alternative_name (0 upto (count - 1)))
      in
        (case parse_pattern alternatives of
           P_Or (patterns, _) =>
             (audit_assert
                ("large or-pattern was not flattened at " ^
                  string_of_int count)
                (length patterns = count);
              audit_assert
                ("large or-pattern source order changed at " ^
                  string_of_int count)
                (case (hd patterns, List.last patterns) of
                   (P_Ident (first, _), P_Ident (last, _)) =>
                     first = alternative_name 0 andalso
                     last = alternative_name (count - 1)
                 | _ => false))
         | _ =>
             error
               ("parser regression audit: large or-pattern AST changed at " ^
                 string_of_int count))
      end

    val _ = audit_alternatives 4096
    val _ = audit_alternatives 16384

    fun expect_positioned_rejection
        label text start expected expected_position =
      let
        val expected_here =
          XML.content_of
            (YXML.parse_body (Position.here expected_position))
      in
        (case Exn.result
            (fn () =>
              Parser_Test_Elaboration.expression ctxt
                (Parser_Lex_Util.positioned_content_source
                  text start)) () of
           Exn.Res _ =>
             error
               ("parser regression audit: " ^ label ^
                 " unexpectedly parsed")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let
                 val message =
                   XML.content_of
                     (YXML.parse_body
                       (Runtime.exn_message exn))
               in
                 audit_assert (label ^ " diagnostic changed")
                   (String.isSubstring expected message);
                 audit_assert (label ^ " position changed")
                   (String.isSubstring expected_here message)
               end)
      end

    val operator_text = "1 + 2 ++ 3"
    val operator_start =
      Position.make0 4 10 0 "" "" ""
    val second_operator =
      Position.symbol_explode
        (String.substring (operator_text, 0, 7))
        operator_start
    val _ =
      expect_positioned_rejection
        "malformed operator"
        operator_text operator_start
        "syntax error found at +"
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
        "syntax error found at end of input"
        eof_stop
  in
    val _ = writeln "Parser position and pattern grammar regressions passed"
  end
\<close>

section\<open> Range, array, and indexing structure \<close>

text\<open>
The public AST keeps each source form explicit, while the term layer emits only
the frontend vocabulary before the command's single final \<open>Syntax.check_term\<close>.
Same-source commands in \<open>Parser_Tests_Expr\<close> separately require the
checked terms to close by \<open>refl\<close>.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("range/array/index regression audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE =>
           error "range/array/index regression audit: empty parse")

    fun integer text (UE_Literal (LP_Integer (actual, _))) =
          actual = text
      | integer _ _ = false

    fun identifier text (UE_Path path) = render_path path = text
      | identifier _ _ = false

    val _ =
      (case parse "1..2" of
         UE_Range (RK_Exclusive, lower, upper, _) =>
           audit_assert "exclusive range AST changed"
             (integer "1" lower andalso integer "2" upper)
       | _ => error "range/array/index regression audit: exclusive range AST changed")

    val _ =
      (case parse "1..=2" of
         UE_Range (RK_Inclusive, lower, upper, _) =>
           audit_assert "inclusive range AST changed"
             (integer "1" lower andalso integer "2" upper)
       | _ => error "range/array/index regression audit: inclusive range AST changed")

    val _ =
      (case parse "[]" of
         UE_Array ([], _) => ()
       | _ => error "range/array/index regression audit: empty array AST changed")

    val _ =
      (case parse "[1, 2]" of
         UE_Array ([first, second], _) =>
           audit_assert "array element order changed"
             (integer "1" first andalso integer "2" second)
       | _ => error "range/array/index regression audit: array AST changed")

    val _ =
      (case parse "xs[0].field[1]" of
         UE_Index
           (UE_Field
             (UE_Index (base, first_index, _), "field", _),
            second_index, _) =>
           audit_assert "postfix index/field nesting changed"
             (identifier "xs" base andalso
              integer "0" first_index andalso
              integer "1" second_index)
       | _ =>
           error
             "range/array/index regression audit: postfix nesting AST changed")

    val _ =
      (case parse "xs[0] += 1" of
         UE_Assign
           (AssignAdd,
            UP_Index (UP_Path path, index, _),
            rhs, _) =>
           audit_assert "indexed place conversion changed"
             (render_path path = "xs" andalso
              integer "0" index andalso integer "1" rhs)
       | _ =>
           error
             "range/array/index regression audit: indexed place AST changed")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    fun has_head name arity term =
      (case Term.strip_comb term of
         (Const (actual, _), arguments) =>
           actual = name andalso length arguments = arity
       | _ => false)

    fun function_call2 target term =
      (case Term.strip_comb term of
         (Const (call, _), Const (actual, _) :: arguments) =>
           call = \<^const_name>\<open>funcall2\<close> andalso
           actual = target andalso length arguments = 2
       | _ => false)

    val _ =
      audit_assert "exclusive range term shape changed"
        (function_call2 \<^const_name>\<open>range_new\<close>
          (unchecked "1..2"))

    val _ =
      audit_assert "inclusive range term shape changed"
        (function_call2 \<^const_name>\<open>range_eq_new\<close>
          (unchecked "1..=2"))

    fun array_shape [] term =
          (case Term.strip_comb term of
             (Const (literal_name, _), [Const (nil_name, _)]) =>
               literal_name = \<^const_name>\<open>literal\<close> andalso
               nil_name = \<^const_name>\<open>List.Nil\<close>
           | _ => false)
      | array_shape (_ :: rest) term =
          (case Term.strip_comb term of
             (Const (bindlift_name, _),
              [Const (cons_name, _), _, tail]) =>
               bindlift_name = \<^const_name>\<open>bindlift2\<close> andalso
               cons_name = \<^const_name>\<open>List.Cons\<close> andalso
               array_shape rest tail
           | _ => false)

    val _ =
      audit_assert "empty array term shape changed"
        (array_shape [] (unchecked "[]"))

    val _ =
      audit_assert "nonempty array term shape changed"
        (array_shape [(), (), ()] (unchecked "[1, 2, 3]"))

    val _ =
      audit_assert "index term shape changed"
        (function_call2 \<^const_name>\<open>index_const\<close>
          (unchecked "[1][0]"))

    val _ =
      audit_assert "direct array borrow stopped erasing"
        (Term.aconv (unchecked "&[1, 2]", unchecked "[1, 2]"))

    val indexed_assignment = unchecked "xs[0] = 1"
    val _ =
      audit_assert "indexed assignment lost store-update lowering"
        (has_head \<^const_name>\<open>bind2\<close> 3 indexed_assignment)
    val index_count =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = \<^const_name>\<open>index_const\<close>
              then Integer.add 1
              else I
          | _ => I)
        indexed_assignment 0
    val _ =
      audit_assert "indexed assignment did not lower its place exactly once"
        (index_count = 1)
  in
    val _ = writeln "Range, array, and indexing regressions passed"
  end
\<close>

section\<open> Numeric tuple projection structure, ranges, and markup \<close>

consts
  tuple_projection_audit_marker ::
    \<open>
      (unit,
       nat \<times> nat \<times> nat \<times>
         (bool \<times> bool \<times> Tuple.tnil) \<times> Tuple.tnil,
       unit, unit, unit, unit) expression
    \<close>

text\<open>
These checks keep numeric projections distinct from fields and bracket indexing.
They pin the canonical index payload, left-associated AST, numeric-token ranges,
lexer markup, direct expanded \<open>tuple_index_N\<close> shape, recovery, value-only
assignment policy, and exactly-once receiver lowering.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("tuple-projection regression audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "tuple-projection regression audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)
      |> Term_Position.strip_positions

    fun path_named name (UE_Path path) = render_path path = name
      | path_named _ _ = false

    fun projection index receiver (UE_TupleProjection (actual, stored, _)) =
          stored = index andalso receiver actual
      | projection _ _ _ = false

    val _ =
      List.app
        (fn index =>
          audit_assert
            ("AST index " ^ string_of_int index ^ " changed")
            (projection index (path_named "source")
              (parse ("source." ^ string_of_int index))))
        [0, 1, 10, 15]

    val _ =
      (case parse "source.2.0" of
         UE_TupleProjection
           (UE_TupleProjection (base, 2, _), 0, _) =>
           audit_assert "projection chain base changed"
             (path_named "source" base)
       | _ => error "tuple-projection regression audit: chain AST changed")

    val _ =
      (case parse "source.field[0].1" of
         UE_TupleProjection
           (UE_Index
             (UE_Field (base, "field", _),
              UE_Literal (LP_Integer ("0", _)), _),
            1, _) =>
           audit_assert "field/index/projection source order changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: mixed postfix AST changed")

    val _ =
      (case parse "!source.0" of
         UE_Unary
           (U_Not, UE_TupleProjection (base, 0, _), _) =>
           audit_assert "projection/prefix precedence changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: prefix AST changed")

    val _ =
      (case parse "source.0 + other" of
         UE_Bin
           (Add, UE_TupleProjection (base, 0, _), other, _) =>
           audit_assert "projection/binary precedence changed"
             (path_named "source" base andalso
              path_named "other" other)
       | _ =>
           error
             "tuple-projection regression audit: binary AST changed")

    val _ =
      (case parse "if source.0 { () } else { () }" of
         UE_If
           (UE_TupleProjection (base, 0, _),
            UE_Block (UE_Unit _, _),
            SOME (UE_Block (UE_Unit _, _)), _) =>
           audit_assert "restricted control-head projection changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: control-head AST changed")

    fun find_from text needle offset =
      if offset + size needle > size text
      then
        error
          ("tuple-projection regression audit: missing " ^ quote needle)
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

    fun same_range actual expected =
      Position.offset_of actual = Position.offset_of expected andalso
      Position.end_offset_of actual = Position.end_offset_of expected

    val ranged_text =
      "\<llangle>tuple_projection_audit_marker\<rrangle>.10.15"
    val ranged_start =
      Position.make0 13 70 700 "" ""
        "tuple-projection-range-audit"
    val (ten_offset, ten_position) =
      token_position ranged_text ranged_start "10" 0
    val (_, fifteen_position) =
      token_position ranged_text ranged_start "15"
        (ten_offset + size "10")
    val ranged_ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          ranged_text ranged_start)
    val _ =
      (case ranged_ast of
         UE_TupleProjection
           (UE_TupleProjection
             (UE_Literal (LP_ValAntiq _), 10, inner_position),
            15, outer_position) =>
           (audit_assert "inner two-digit token range changed"
              (same_range inner_position ten_position);
            audit_assert "outer two-digit token range changed"
              (same_range outer_position fifteen_position);
            audit_assert "expression_position lost the outer numeric token"
              (same_range
                (expression_position ranged_ast) fifteen_position))
       | _ =>
           error
             "tuple-projection regression audit: ranged AST changed")

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun decoded_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))

    fun expect_positioned_failure label text start expected position =
      (case Exn.result
          (fn () =>
            parse_source
              (Parser_Lex_Util.positioned_content_source text start)) () of
         Exn.Res _ =>
           error
             ("tuple-projection regression audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
               val markup = fold collect_markup body []
             in
               audit_assert (label ^ " diagnostic changed")
                 (String.isSubstring expected message);
               audit_assert (label ^ " diagnostic position changed")
                 (exists
                   (fn (name, properties) =>
                     name = Markup.positionN andalso
                       has_position properties position)
                   markup)
             end)

    val assignment_text = "source.0 = rhs"
    val assignment_start =
      Position.make0 19 90 900 "" ""
        "tuple-projection-assignment-audit"
    val (_, assignment_index_position) =
      token_position assignment_text assignment_start "0" 0
    val _ =
      expect_positioned_failure
        "value-only assignment"
        assignment_text assignment_start
        "invalid assignment target"
        assignment_index_position

    val invalid_start =
      Position.make0 23 110 1100 "" ""
        "tuple-projection-invalid-index-audit"
    fun expect_invalid_projection (text, token) =
      let
        val (_, token_position) =
          token_position text invalid_start token 0
      in
        expect_positioned_failure
          ("invalid index " ^ quote token)
          text invalid_start
          ("invalid tuple projection index " ^ quote token ^
            " (expected an unsuffixed decimal integer from 0 through 15)")
          token_position
      end
    val _ =
      List.app expect_invalid_projection
        [("source.16", "16"),
         ("source.00", "00"),
         ("source.01", "01"),
         ("source.0x1", "0x1"),
         ("source.1u8", "1u8"),
         ("source.1_u8", "1_u8")]

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun projection_parts expected_index term =
      (case Term.strip_comb term of
         (Const (bindlift, _), [selector, receiver]) =>
           (audit_assert
              ("projection " ^ string_of_int expected_index ^
                " did not use bindlift1")
              (bindlift = \<^const_name>\<open>bindlift1\<close>);
            audit_assert
              ("projection " ^ string_of_int expected_index ^
                " selector lost fst")
              (count_constant \<^const_name>\<open>fst\<close> selector = 1);
            audit_assert
              ("projection " ^ string_of_int expected_index ^
                " selector has the wrong snd depth")
              (count_constant \<^const_name>\<open>snd\<close> selector =
                expected_index);
            receiver)
       | _ =>
           error
             ("tuple-projection regression audit: projection " ^
               string_of_int expected_index ^ " term shape changed"))

    fun marker_projection index =
      unchecked
        ("\<epsilon>\<open>tuple_projection_audit_marker\<close>." ^
          string_of_int index)

    val _ =
      List.app
        (fn index =>
          let
            val term = marker_projection index
            val receiver = projection_parts index term
          in
            audit_assert
              ("projection " ^ string_of_int index ^
                " receiver changed or was duplicated")
              (count_constant
                 \<^const_name>\<open>tuple_projection_audit_marker\<close>
                 receiver = 1);
            audit_assert
              ("projection " ^ string_of_int index ^
                " introduced field/index/literal lowering")
              (count_constant
                 \<^const_name>\<open>focus_lens_const\<close> term = 0 andalso
               count_constant \<^const_name>\<open>index_const\<close> term = 0 andalso
               count_constant \<^const_name>\<open>literal\<close> term = 0)
          end)
        [0, 1, 10, 15]

    val chain =
      unchecked
        "\<epsilon>\<open>tuple_projection_audit_marker\<close>.3.0"
    val inner = projection_parts 0 chain
    val receiver = projection_parts 3 inner
    val _ =
      audit_assert "chained receiver was not lowered exactly once"
        (count_constant
           \<^const_name>\<open>tuple_projection_audit_marker\<close>
           chain = 1)
    val _ =
      audit_assert "chained projections lost one selected operation"
        (count_constant \<^const_name>\<open>bindlift1\<close> chain = 2)
    val _ =
      audit_assert "chained projection receiver changed"
        (count_constant
           \<^const_name>\<open>tuple_projection_audit_marker\<close>
           receiver = 1)

    fun expect_failure text expected =
      (case Exn.result (fn () => parse text) () of
         Exn.Res _ =>
           error
             ("tuple-projection regression audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (decoded_message exn)))

    val _ =
      (expect_failure "source.16"
         "invalid tuple projection index \"16\"";
       audit_assert "parser did not recover after invalid index"
         (projection 15 (path_named "source") (parse "source.15"));
       expect_failure "source."
         "syntax error found at end of input";
       audit_assert "parser did not recover after trailing dot"
         (projection 15 (path_named "source") (parse "source.15")))

    val captured_reports =
      Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (parse_source
                    (Parser_Lex_Util.positioned_content_source
                      ranged_text ranged_start))) ())
          ())

    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun has_any_entity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            has_position properties position)
        markup
    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size ranged_text
          then rev positions
          else
            (case try (find_from ranged_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position ranged_text ranged_start needle raw
                 in
                   collect (raw + size needle)
                     (position :: positions)
                 end
             | NONE => rev positions)
      in collect 0 [] end

    val _ =
      List.app
        (fn position =>
          audit_assert "projection dot lost delimiter markup"
            (has_markup Markup.delimiterN position))
        (all_token_positions ".")
    val _ =
      List.app
        (fn position =>
          (audit_assert "projection index lost numeral markup"
             (has_markup Markup.numeralN position);
           audit_assert "projection index lost typing markup"
             (has_markup Markup.typingN position);
           audit_assert "projection index received field/free markup"
             (not (has_markup Markup.freeN position));
           audit_assert "projection index received entity markup"
             (not (has_any_entity position))))
        [ten_position, fifteen_position]
  in
    val _ =
      writeln
        "Numeric tuple projection AST, range, markup, lowering, and recovery regressions passed"
  end
\<close>

section\<open> Legacy macro structure, spans, and markup \<close>

consts
  macro_audit_scrutinee :: \<open>nat option\<close>
  macro_audit_ref :: \<open>('a, 'b, 'v) Global_Store.ref\<close>
  macro_audit_marker :: bool
  macro_audit_ignored_marker :: bool
  macro_audit_vec_first :: nat
  macro_audit_vec_second :: nat

text\<open>
These checks pin complete-body macro payload boundaries, source spans, markup, recovery,
and the exact shallow term vocabulary. They also prove that retained bindings evaluate
once, discarded arguments never enter semantic lowering, \<open>vec!\<close> preserves
complete-body element order through the array builder, address macros retain the exact
legacy \<open>ref_address\<close> target, registered bang-names win only when adjacent, and
\<open>matches!\<close> uses the ordinary case compiler with one scrutinee evaluation and
false fallback.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("legacy macro regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "legacy macro regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse_text text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("legacy macro regression audit: missing " ^ quote needle)
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

    val full_body_text =
      "debug_assert!(let flag = true; " ^
      "if let Some(_) = Some(flag) { flag } else { false })"
    val full_body_start =
      Position.make0 7 30 0 "" "" "macro-full-body-span-audit"
    val full_body_stop =
      Position.symbol_explode full_body_text full_body_start
    val full_body =
      parse
        (Parser_Lex_Util.positioned_content_source
          full_body_text full_body_start)
    val (full_body_name_pos, full_body_bang_pos,
         full_body_invocation_pos, full_body_binder_pos,
         full_body_literal_pos, full_body_if_pos) =
      (case full_body of
         UE_Macro
           (path, bang_pos,
            MP_Arguments
              [UE_Let
                (P_Ident ("flag", binder_pos),
                 UE_Literal (LP_Bool (true, literal_pos)),
                 UE_IfLet
                   (P_Constr (pattern_path, [P_Wild _]),
                    UE_Call
                      (UC_Path call_path, [UE_Path scrutinee_path], _),
                    UE_Block (UE_Path then_path, _),
                    SOME
                      (UE_Block
                        (UE_Literal (LP_Bool (false, _)), _)),
                    if_pos))],
           invocation_pos) =>
           (audit_assert "full-body macro path changed"
              (render_path path = "debug_assert");
            audit_assert "full-body condition escaped its binding continuation"
              (render_path pattern_path = "Some" andalso
               render_path call_path = "Some" andalso
               render_path scrutinee_path = "flag" andalso
               render_path then_path = "flag");
            (path_position path, bang_pos, invocation_pos,
             binder_pos, literal_pos, if_pos))
       | _ =>
           error "legacy macro regression audit: full-body macro AST changed")
    val _ =
      audit_assert "full-body invocation start moved"
        (Position.offset_of full_body_invocation_pos =
          Position.offset_of full_body_start)
    val _ =
      audit_assert "full-body invocation end moved"
        (Position.end_offset_of full_body_invocation_pos =
          Position.offset_of full_body_stop)
    val (_, full_body_binder_token) =
      token_position full_body_text full_body_start "flag" 0
    val (_, full_body_literal_token) =
      token_position full_body_text full_body_start "true" 0
    val (_, full_body_if_token) =
      token_position full_body_text full_body_start "if" 0
    val (full_body_name_raw, full_body_name_token) =
      token_position full_body_text full_body_start "debug_assert" 0
    val (_, full_body_bang_token) =
      token_position full_body_text full_body_start "!"
        (full_body_name_raw + size "debug_assert")
    val (first_brace_raw, _) =
      token_position full_body_text full_body_start "}" 0
    val (_, full_body_final_brace) =
      token_position full_body_text full_body_start "}"
        (first_brace_raw + 1)
    val _ =
      audit_assert "full-body binder position moved"
        (Position.offset_of full_body_binder_pos =
           Position.offset_of full_body_binder_token andalso
         Position.end_offset_of full_body_binder_pos =
           Position.end_offset_of full_body_binder_token)
    val _ =
      audit_assert "full-body literal position moved"
        (Position.offset_of full_body_literal_pos =
           Position.offset_of full_body_literal_token andalso
         Position.end_offset_of full_body_literal_pos =
           Position.end_offset_of full_body_literal_token)
    val _ =
      audit_assert "nested conditional span moved"
        (Position.offset_of full_body_if_pos =
           Position.offset_of full_body_if_token andalso
         Position.end_offset_of full_body_if_pos =
           Position.end_offset_of full_body_final_brace)
    val _ =
      audit_assert "full-body macro name span moved"
        (Position.offset_of full_body_name_pos =
           Position.offset_of full_body_name_token andalso
         Position.end_offset_of full_body_name_pos =
           Position.end_offset_of full_body_name_token)
    val full_body_bang_markup_pos =
      Position.range_position
        (full_body_bang_pos,
         Position.symbol_explode "!" full_body_bang_pos)
    val _ =
      audit_assert "full-body macro bang span moved"
        (Position.offset_of full_body_bang_markup_pos =
           Position.offset_of full_body_bang_token andalso
         Position.end_offset_of full_body_bang_markup_pos =
           Position.end_offset_of full_body_bang_token)
    val _ =
      audit_assert "full-body macro name and bang stopped being adjacent"
        (Position.end_offset_of full_body_name_pos =
           Position.offset_of full_body_bang_pos)

    val bracket_body_text =
      "assert_eq![let left = true; left, " ^
      "const right = false; if right { false } else { true }]"
    val bracket_body_start =
      Position.make0 9 60 0 "" "" "macro-bracket-body-span-audit"
    val bracket_body_stop =
      Position.symbol_explode bracket_body_text bracket_body_start
    val bracket_body =
      parse
        (Parser_Lex_Util.positioned_content_source
          bracket_body_text bracket_body_start)
    val bracket_body_invocation_pos =
      (case bracket_body of
         UE_Macro
           (path, _,
            MP_Arguments
              [UE_Let
                (P_Ident ("left", _),
                 UE_Literal (LP_Bool (true, _)),
                 UE_Path left_path),
               UE_Const
                (P_Ident ("right", _),
                 UE_Literal (LP_Bool (false, _)),
                 UE_If
                   (UE_Path right_path, UE_Block _, SOME (UE_Block _), _))],
            invocation_pos) =>
           (audit_assert "bracket full-body macro path changed"
              (render_path path = "assert_eq");
            audit_assert "bracket full-body argument order changed"
              (render_path left_path = "left" andalso
               render_path right_path = "right");
            invocation_pos)
       | _ =>
           error "legacy macro regression audit: bracket full-body AST changed")
    val _ =
      audit_assert "bracket full-body invocation start moved"
        (Position.offset_of bracket_body_invocation_pos =
          Position.offset_of bracket_body_start)
    val _ =
      audit_assert "bracket full-body invocation end moved"
        (Position.end_offset_of bracket_body_invocation_pos =
          Position.offset_of bracket_body_stop)

    val spaced_text = "assert\n  ! [\<llangle>True\<rrangle>]"
    val spaced_start =
      Position.make0 11 40 0 "" "" "macro-span-audit"
    val spaced_stop =
      Position.symbol_explode spaced_text spaced_start
    val spaced =
      parse
        (Parser_Lex_Util.positioned_content_source
          spaced_text spaced_start)
    val (spaced_name_pos, spaced_bang_pos, spaced_invocation_pos) =
      (case spaced of
         UE_Macro
           (path, bang_pos,
            MP_Arguments [UE_Literal (LP_ValAntiq _)],
            invocation_pos) =>
           let val name_pos = path_position path in
           (audit_assert "generic macro path changed"
              (render_path path = "assert");
            audit_assert "generic macro name span moved"
              (Position.offset_of name_pos =
                Position.offset_of spaced_start);
            audit_assert "generic whitespace before bang was lost"
              (Position.end_offset_of name_pos <>
                Position.offset_of bang_pos);
            audit_assert "generic invocation start moved"
              (Position.offset_of invocation_pos =
                Position.offset_of spaced_start);
            audit_assert "generic invocation end moved"
              (Position.end_offset_of invocation_pos =
                Position.offset_of spaced_stop);
            (name_pos, bang_pos, invocation_pos))
           end
       | _ =>
           error "legacy macro regression audit: generic macro AST changed")

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) ())
          ())
    val _ = capture_elaboration spaced_text spaced_start
    val _ = capture_elaboration full_body_text full_body_start
    val _ = capture_elaboration bracket_body_text bracket_body_start

    val ignored_markup_text =
      "debug_assert!(true, let ignored = unknown_macro_markup; ignored)"
    val ignored_markup_start =
      Position.make0 13 90 0 "" "" "macro-ignored-body-markup-audit"
    val _ =
      capture_elaboration ignored_markup_text ignored_markup_start

    val matches_text =
      "matches!(Some(\<llangle>1 :: nat\<rrangle>), Some(_))"
    val matches_start =
      Position.make0 17 80 0 "" "" "macro-markup-audit"
    val matches_stop =
      Position.symbol_explode matches_text matches_start
    val matches =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    matches_text matches_start)) ())
          ())
    val (matches_name_pos, matches_bang_pos, matches_invocation_pos) =
      (case matches of
         UE_Macro
           (path, bang_pos,
            MP_Matches
              (UE_Call (UC_Path call_path, [_], _),
               P_Constr (pattern_path, [P_Wild _])),
            invocation_pos) =>
           if render_path path = "matches" andalso
               render_path call_path = "Some" andalso
               render_path pattern_path = "Some"
           then (path_position path, bang_pos, invocation_pos)
           else error "legacy macro regression audit: matches paths changed"
       | _ =>
           error "legacy macro regression audit: matches macro AST changed")
    val _ =
      audit_assert "matches name and bang stopped being adjacent"
        (Position.end_offset_of matches_name_pos =
          Position.offset_of matches_bang_pos)
    val _ =
      audit_assert "matches invocation start moved"
        (Position.offset_of matches_invocation_pos =
          Position.offset_of matches_start)
    val _ =
      audit_assert "matches invocation end moved across Isabelle symbols"
        (Position.end_offset_of matches_invocation_pos =
          Position.offset_of matches_stop)

    val registered_text = "shout!(true)"
    val registered_start =
      Position.make0 23 120 0 "" "" "macro-registered-markup-audit"
    val registered =
      parse
        (Parser_Lex_Util.positioned_content_source
          registered_text registered_start)
    val (registered_name_pos, registered_bang_pos) =
      (case registered of
         UE_Macro
           (path, bang_pos,
            MP_Arguments [UE_Literal (LP_Bool (true, _))], _) =>
           if render_path path = "shout"
           then (path_position path, bang_pos)
           else error "legacy macro regression audit: registered macro path changed"
       | _ =>
           error "legacy macro regression audit: registered macro AST changed")
    val _ =
      audit_assert "registered macro name and bang stopped being adjacent"
        (Position.end_offset_of registered_name_pos =
          Position.offset_of registered_bang_pos)
    val registered_complete_name_pos =
      Position.range_position
        (registered_name_pos,
         Position.symbol_explode "!" registered_bang_pos)
    val _ = capture_elaboration registered_text registered_start

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)
    fun has_markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun has_urust_entity pos =
      has_entity_markup "urust_var" pos
    fun entity_id property pos =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties pos
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "legacy macro regression audit: binder entity markup changed")
      end
    val _ =
      audit_assert "generic built-in macro keyword markup moved"
        (has_markup Markup.keyword1N spaced_name_pos)
    val spaced_bang_markup_pos =
      Position.range_position
        (spaced_bang_pos,
         Position.symbol_explode "!" spaced_bang_pos)
    val _ =
      audit_assert "generic built-in macro bang markup moved"
        (has_markup Markup.operatorN spaced_bang_markup_pos)
    val _ =
      audit_assert "generic macro invocation lost its symbol-counted end"
        (Position.end_offset_of spaced_invocation_pos =
          Position.offset_of spaced_stop)
    val _ =
      audit_assert "matches keyword markup moved"
        (has_markup Markup.keyword1N matches_name_pos)
    val matches_bang_markup_pos =
      Position.range_position
        (matches_bang_pos,
         Position.symbol_explode "!" matches_bang_pos)
    val _ =
      audit_assert "matches bang operator markup moved"
        (has_markup Markup.operatorN matches_bang_markup_pos)
    val _ =
      audit_assert "registered complete-bang-name notation markup moved"
        (has_entity_markup
          Micro_Rust_Names.notationN registered_complete_name_pos)
    val _ =
      audit_assert "registered complete-bang-name dispatch styling moved"
        (has_markup Markup.keyword3N registered_complete_name_pos)

    val (_, full_body_let_keyword) =
      token_position full_body_text full_body_start "let" 0
    val (_, full_body_else_keyword) =
      token_position full_body_text full_body_start "else" 0
    val (_, full_body_semicolon) =
      token_position full_body_text full_body_start ";" 0
    val (_, full_body_left_paren) =
      token_position full_body_text full_body_start "(" 0
    val (_, full_body_right_paren) =
      token_position full_body_text full_body_start ")"
        (size full_body_text - 1)
    val (full_body_definition_raw, full_body_definition) =
      token_position full_body_text full_body_start "flag" 0
    val (_, full_body_reference) =
      token_position full_body_text full_body_start "flag"
        (full_body_definition_raw + size "flag")
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " keyword markup moved")
            (has_markup Markup.keyword1N position))
        [(full_body_let_keyword, "full-body let"),
         (full_body_if_token, "full-body if"),
         (full_body_else_keyword, "full-body else")]
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " delimiter markup moved")
            (has_markup Markup.delimiterN position))
        [(full_body_semicolon, "full-body semicolon"),
         (full_body_left_paren, "full-body opening parenthesis"),
         (full_body_right_paren, "full-body closing parenthesis")]
    val _ =
      audit_assert "full-body built-in macro keyword markup moved"
        (has_markup Markup.keyword1N full_body_name_pos)
    val _ =
      audit_assert "full-body macro bang operator markup moved"
        (has_markup Markup.operatorN full_body_bang_markup_pos)
    val _ =
      audit_assert "retained full-body binder navigation changed"
        (has_markup Markup.boundN full_body_definition andalso
         has_markup Markup.boundN full_body_reference andalso
         entity_id Markup.defN full_body_definition =
           entity_id Markup.refN full_body_reference)

    val (_, bracket_const_keyword) =
      token_position bracket_body_text bracket_body_start "const" 0
    val (_, bracket_comma) =
      token_position bracket_body_text bracket_body_start "," 0
    val (_, bracket_semicolon) =
      token_position bracket_body_text bracket_body_start ";" 0
    val (_, bracket_left) =
      token_position bracket_body_text bracket_body_start "[" 0
    val (_, bracket_right) =
      token_position bracket_body_text bracket_body_start "]" 0
    val _ =
      audit_assert "full-body const keyword markup moved"
        (has_markup Markup.keyword1N bracket_const_keyword)
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " delimiter markup moved")
            (has_markup Markup.delimiterN position))
        [(bracket_comma, "full-body top-level comma"),
         (bracket_semicolon, "bracket full-body semicolon"),
         (bracket_left, "full-body opening bracket"),
         (bracket_right, "full-body closing bracket")]

    val (_, ignored_let_keyword) =
      token_position ignored_markup_text ignored_markup_start "let" 0
    val (_, ignored_semicolon) =
      token_position ignored_markup_text ignored_markup_start ";" 0
    val (ignored_definition_raw, ignored_definition) =
      token_position ignored_markup_text ignored_markup_start "ignored" 0
    val (_, ignored_reference) =
      token_position ignored_markup_text ignored_markup_start "ignored"
        (ignored_definition_raw + size "ignored")
    val _ =
      audit_assert "ignored full-body let lost syntactic keyword markup"
        (has_markup Markup.keyword1N ignored_let_keyword)
    val _ =
      audit_assert "ignored full-body semicolon lost delimiter markup"
        (has_markup Markup.delimiterN ignored_semicolon)
    val _ =
      audit_assert "ignored full-body binder entered semantic markup"
        (not (has_markup Markup.boundN ignored_definition) andalso
         not (has_markup Markup.boundN ignored_reference) andalso
         not (has_urust_entity ignored_definition) andalso
         not (has_urust_entity ignored_reference))

    val full_body_parent_term =
      checked
        ("debug_assert!(let observed = macro_audit_marker; " ^
         "if observed { observed } else { false })")
    val full_body_bracket_term =
      checked
        ("debug_assert![let observed = macro_audit_marker; " ^
         "if observed { observed } else { false }]")
    val _ =
      audit_assert "full-body delimiters changed lowering"
        (Term.aconv (full_body_parent_term, full_body_bracket_term))
    val _ =
      audit_assert "retained full-body initializer evaluated more than once"
        (count_constant
          \<^const_name>\<open>macro_audit_marker\<close>
          full_body_parent_term = 1)

    val ignored_full_body_term =
      checked
        ("debug_assert!(true, " ^
         "let ignored = macro_audit_ignored_marker; ignored)")
    val _ =
      audit_assert "ignored full-body assertion argument entered the term"
        (Term.aconv
          (ignored_full_body_term, checked "debug_assert!(true)"))
    val _ =
      audit_assert "ignored full-body initializer entered the term"
        (count_constant
          \<^const_name>\<open>macro_audit_ignored_marker\<close>
          ignored_full_body_term = 0)
    val _ =
      audit_assert "ignored full-body message argument entered the term"
        (Term.aconv
          (checked
            ("panic!(\"kept\", " ^
             "let ignored = macro_audit_ignored_marker; ignored)"),
           checked "panic!(\"kept\")"))

    val vec_full_body_term =
      checked
        ("vec![" ^
         "let first = macro_audit_vec_first; first, " ^
         "let second = macro_audit_vec_second; second]")
    val vec_grouped_array_term =
      checked
        ("[(let first = macro_audit_vec_first; first), " ^
         "(let second = macro_audit_vec_second; second)]")
    val _ =
      audit_assert "vec! complete-body element order changed"
        (Term.aconv (vec_full_body_term, vec_grouped_array_term))
    val _ =
      audit_assert "vec! complete-body elements were not evaluated once each"
        (count_constant
           \<^const_name>\<open>macro_audit_vec_first\<close>
           vec_full_body_term = 1 andalso
         count_constant
           \<^const_name>\<open>macro_audit_vec_second\<close>
           vec_full_body_term = 1)

    val _ =
      audit_assert "ignored assertion arguments entered the term"
        (Term.aconv
          (unchecked "assert!(true, unknown_ignored, 1 + false)",
           unchecked "assert!(true)"))
    val _ =
      audit_assert "ignored panic arguments entered the term"
        (Term.aconv
          (unchecked "panic!(\"kept\", unknown_ignored, { return missing; })",
           unchecked "panic!(\"kept\")"))
    val _ =
      audit_assert "debug_assert! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert!(true)",
           unchecked "assert!(true)"))
    val _ =
      audit_assert "debug_assert_eq! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert_eq!(1, 1)",
           unchecked "assert_eq!(1, 1)"))
    val _ =
      audit_assert "debug_assert_ne! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert_ne!(1, 2)",
           unchecked "assert_ne!(1, 2)"))
    val _ =
      audit_assert "todo! stopped aliasing unimplemented!"
        (Term.aconv
          (unchecked "todo!(\"later\")",
           unchecked "unimplemented!(\"later\")"))
    val _ =
      audit_assert "unreachable! stopped aliasing panic!"
        (Term.aconv
          (unchecked "unreachable!(\"never\")",
           unchecked "panic!(\"never\")"))
    val _ =
      audit_assert "vec! stopped reusing the array builder"
        (Term.aconv
          (unchecked "vec![1, 2, 3]",
           unchecked "[1, 2, 3]"))
    val legacy_ref_address =
      Term.map_types (K dummyT) \<^term>\<open>ref_address\<close>
    fun address_target source =
      (case unchecked source of
         Const (name, _) $ target $ _
           => if name = \<^const_name>\<open>bindlift1\<close> then target
              else error "legacy macro regression audit: address macro stopped using bindlift1"
       | _ =>
           error "legacy macro regression audit: address macro term shape changed")
    val _ =
      audit_assert "addr_of! stopped using the exact legacy ref_address target"
        (Term.aconv
          (address_target "addr_of!(macro_audit_ref)",
           legacy_ref_address))
    val _ =
      audit_assert "addr_of_mut! stopped using the exact legacy ref_address target"
        (Term.aconv
          (address_target "addr_of_mut!(macro_audit_ref)",
           legacy_ref_address))

    fun is_recovered_full_body expression =
      (case expression of
         UE_Macro
           (path, _,
            MP_Arguments
              [UE_Let
                (P_Ident ("recovered", _),
                 UE_Literal (LP_Bool (true, _)),
                 UE_If
                   (UE_Path condition_path,
                    UE_Block (UE_Path then_path, _),
                    SOME (UE_Block _), _))],
            _) =>
           render_path path = "debug_assert" andalso
           render_path condition_path = "recovered" andalso
           render_path then_path = "recovered"
       | _ => false)
    fun reject_then_recover bad =
      let
        val _ =
          (case Exn.result parse_text bad of
             Exn.Res _ =>
               error
                 ("legacy macro regression audit: malformed full body " ^
                  quote bad ^ " unexpectedly parsed")
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else ())
        val recovered =
          parse_text
            ("debug_assert!(let recovered = true; " ^
             "if recovered { recovered } else { false })")
      in
        audit_assert
          ("malformed full body leaked parser state after " ^ quote bad)
          (is_recovered_full_body recovered)
      end
    val _ =
      List.app reject_then_recover
        ["debug_assert!(let flag = true;)",
         "assert_eq!(let left = true; left,, false)",
         "debug_assert!(let flag = true; if flag { true } else { false)",
         "debug_assert![let flag = true; flag)"]

    val matches_term =
      checked "matches!(macro_audit_scrutinee, Some(_))"
    val explicit_case =
      checked
        "match_case macro_audit_scrutinee { Some(_) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }"
    val _ =
      audit_assert "matches! stopped using ordinary case compilation"
        (Term.aconv (matches_term, explicit_case))
    val _ =
      audit_assert "matches! evaluated its scrutinee more than once"
        (count_constant
          \<^const_name>\<open>macro_audit_scrutinee\<close>
          matches_term = 1)
    val _ =
      audit_assert "matches! lost its requested-pattern true branch"
        (count_constant \<^const_name>\<open>True\<close> matches_term = 1)
    val _ =
      audit_assert "matches! lost its wildcard false fallback"
        (count_constant \<^const_name>\<open>False\<close> matches_term = 1)
  in
    val _ = writeln "Legacy macro structure, span, and markup regressions passed"
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
           (UC_Antiq source, [first, second], call_pos) =>
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
              (Position.offset_of call_pos =
                Position.offset_of ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (Position.end_offset_of call_pos =
                Position.offset_of call_stop);
            audit_assert "expression_position lost the complete call span"
              (Position.offset_of (expression_position ast) =
                 Position.offset_of call_pos andalso
               Position.end_offset_of (expression_position ast) =
                 Position.end_offset_of call_pos))
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
These checks pin the function-literal boundary independently of same-source conformance: exact HOL and
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
              (source, 14, suffix_pos,
               SOME
                 (Generic_Args
                   ([Generic_Arg (canonical, generic_source)], _))),
            [first, second], call_pos) =>
           (audit_assert "runtime argument order changed"
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
              (same_start call_pos ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (same_stop call_pos call_stop);
            audit_assert "expression_position lost the complete call span"
              (same_start (expression_position ast) ast_start andalso
               same_stop (expression_position ast) call_stop))
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

section\<open> Closure AST, lowering, and binder-navigation audit \<close>

consts
  closure_audit_marker ::
    \<open>(unit, nat, nat, unit, unit, unit) expression\<close>

text\<open>
These checks pin the second-class closure boundary below the source-level examples. They retain
ordered pattern-shaped formals and the complete closure span, prove that grouping alone re-enters
ordinary expression positions, and inspect the checked shallow term for the exact frontend shape.
The markup checks lock definition/reference navigation across ordinary, duplicate, nested, and
shadowed formals.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("closure regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "closure regression audit: empty parse")

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

    fun count_abstractions (Abs (_, _, body)) =
          1 + count_abstractions body
      | count_abstractions (left $ right) =
          count_abstractions left + count_abstractions right
      | count_abstractions _ = 0

    fun is_grouped_closure (UE_Group (UE_Closure _, _)) = true
      | is_grouped_closure _ = false

    val ast_text = "|first, second| second"
    val ast_start =
      Position.make0 5 20 100 "" "" "closure-ast-audit"
    val ast_stop =
      Position.symbol_explode ast_text ast_start
    val ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          ast_text ast_start)
    val _ =
      (case ast of
         UE_Closure
           ([P_Ident ("first", _), P_Ident ("second", _)],
            UE_Path body_path, closure_pos) =>
           (audit_assert "closure body path changed"
              (render_path body_path = "second");
            audit_assert "full closure span start moved"
              (Position.offset_of closure_pos =
                Position.offset_of ast_start);
            audit_assert "full closure span end moved"
              (Position.end_offset_of closure_pos =
                Position.offset_of ast_stop);
            audit_assert "expression_position lost the closure span"
              (Position.offset_of (expression_position ast) =
                 Position.offset_of closure_pos andalso
               Position.end_offset_of (expression_position ast) =
                 Position.end_offset_of closure_pos))
       | _ =>
           error "closure regression audit: closure AST changed")

    val _ =
      (case parse_text "let f = (|| 1); ()" of
         UE_Let (_, initializer, _) =>
           audit_assert "grouped closure initializer stopped parsing"
             (is_grouped_closure initializer)
       | _ =>
           error "closure regression audit: grouped initializer AST changed")
    val _ =
      (case parse_text "target = (|| 1)" of
         UE_Assign (_, _, rhs, _) =>
           audit_assert "grouped closure assignment RHS stopped parsing"
             (is_grouped_closure rhs)
       | _ =>
           error "closure regression audit: grouped assignment AST changed")
    val _ =
      (case parse_text "1 + (|| 2)" of
         UE_Bin (_, _, rhs, _) =>
           audit_assert "grouped closure binary operand stopped parsing"
             (is_grouped_closure rhs)
       | _ =>
           error "closure regression audit: grouped binary AST changed")
    val _ =
      (case parse_text "if (|| true) { () }" of
         UE_If (condition, _, _, _) =>
           audit_assert "grouped closure condition stopped parsing"
             (is_grouped_closure condition)
       | _ =>
           error "closure regression audit: grouped condition AST changed")
    val _ =
      (case parse_text "match (|| true) { _ \<Rightarrow> () }" of
         UE_Match (_, scrutinee, _, _) =>
           audit_assert "grouped closure scrutinee stopped parsing"
             (is_grouped_closure scrutinee)
       | _ =>
           error "closure regression audit: grouped scrutinee AST changed")
    val _ =
      (case parse_text "for item in (|| []) { () }" of
         UE_For (_, iterable, _, _) =>
           audit_assert "grouped closure iterable stopped parsing"
             (is_grouped_closure iterable)
       | _ =>
           error "closure regression audit: grouped iterable AST changed")
    val _ =
      (case
          parse_text
            "match true { true \<Rightarrow> (|| true), false \<Rightarrow> (|| false) }" of
         UE_Match
           (_, _, [UR_Arm (_, _, first), UR_Arm (_, _, second)], _) =>
           (audit_assert "first grouped closure arm stopped parsing"
              (is_grouped_closure first);
            audit_assert "second grouped closure arm stopped parsing"
              (is_grouped_closure second))
       | _ =>
           error "closure regression audit: grouped arm AST changed")
    val _ =
      (case parse_text "(|| 1); ()" of
         UE_Seq (left, _) =>
           audit_assert "grouped closure sequencing-left stopped parsing"
             (is_grouped_closure left)
       | _ =>
           error "closure regression audit: grouped sequence AST changed")
    val _ =
      (case parse_text "|| (|| 1)" of
         UE_Closure (_, body, _) =>
           audit_assert "grouped nested closure body stopped parsing"
             (is_grouped_closure body)
       | _ =>
           error "closure regression audit: grouped nested closure AST changed")

    val guard =
      parse_text
        "match_case Some(()) { Some(_) if || true \<Rightarrow> (), None \<Rightarrow> () }"
    val _ =
      (case guard of
         UE_Match
           (_, _,
            UR_Arm
              (_, SOME (UE_Closure ([], UE_Literal (LP_Bool (true, _)), _), _), _) :: _,
            _) =>
           ()
       | _ =>
           error
             "closure regression audit: a closure stopped parsing as a complete guard body")

    val shape =
      checked
        "|first, second| \<epsilon>\<open>closure_audit_marker\<close>"
    val _ =
      audit_assert "closure did not lower to exactly one literal"
        (count_constant \<^const_name>\<open>literal\<close> shape = 1)
    val _ =
      audit_assert "closure did not lower to exactly one FunctionBody"
        (count_constant \<^const_name>\<open>FunctionBody\<close> shape = 1)
    val _ =
      audit_assert "closure did not lower to one abstraction per formal"
        (count_abstractions shape = 2)
    val _ =
      audit_assert "closure body was lowered more than once"
        (count_constant
          \<^const_name>\<open>closure_audit_marker\<close> shape = 1)

    fun closure_payload
        (Const (name, _) $ payload) =
          if name = \<^const_name>\<open>literal\<close>
          then payload
          else error
            "closure regression audit: closure wrapper stopped using literal"
      | closure_payload _ =
          error "closure regression audit: closure wrapper shape changed"

    val ordered =
      checked
        "|first, second| \<llangle>(first :: nat, second :: bool)\<rrangle>"
    val (ordered_formals, _) =
      Term.strip_abs (closure_payload ordered)
    val _ =
      audit_assert "closure abstraction order changed"
        (map #2 ordered_formals = [HOLogic.natT, HOLogic.boolT])

    val duplicate =
      checked "|same, same, same| same"
    val (duplicate_formals, duplicate_body) =
      Term.strip_abs (closure_payload duplicate)
    val _ =
      audit_assert "duplicate closure formals stopped producing abstractions"
        (length duplicate_formals = 3)
    val _ =
      (case duplicate_body of
         Const (function_body_name, _) $
           (Const (literal_name, _) $ Bound 0) =>
           (audit_assert "duplicate closure body lost FunctionBody"
              (function_body_name =
                \<^const_name>\<open>FunctionBody\<close>);
            audit_assert "duplicate closure body lost literal lowering"
              (literal_name = \<^const_name>\<open>literal\<close>))
       | _ =>
           error
             "closure regression audit: innermost duplicate no longer shadows earlier formals")

    val allocator_start =
      Position.make0 9 30 300 "" "" "closure-allocator-audit"
    val allocator_positions =
      [allocator_start,
       Position.symbol_explode "first " allocator_start,
       Position.symbol_explode "first second " allocator_start]
    val (allocated, allocated_environment) =
      URust_Resolution.allocate_closure_formals ctxt
        URust_Resolution.empty_environment
        (map2 pair ["first", "second", "first"] allocator_positions)
    val allocated_names =
      map
        (fn Free (name, _) => name
          | _ =>
              error
                "closure regression audit: allocator returned a non-Free formal")
        allocated
    val _ =
      audit_assert "closure allocator reused a formal identity"
        (length (distinct (op =) allocated_names) = 3)
    val _ =
      audit_assert "closure allocator did not preserve source order"
        (length allocated = 3)
    val _ =
      audit_assert "later duplicate did not win in the final environment"
        (case URust_Resolution.lookup_local
            allocated_environment "first" of
           SOME selected => Term.aconv (selected, List.last allocated)
         | NONE => false)

    val resolved_dispatch =
      checked "|closureRole| closureRole(closureRole)"
    val _ =
      audit_assert "checked closure retained an unresolved dispatch marker"
        (count_constant
          \<^const_name>\<open>urust_dispatch\<close>
          resolved_dispatch = 0)

    fun find_from text needle offset =
      if offset + size needle > size text
      then error
        ("closure regression audit: missing " ^ quote needle)
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

    val ordinary_text = "|alpha| alpha"
    val ordinary_start =
      Position.make0 11 40 400 "" "" "closure-markup-ordinary"
    val duplicate_text = "|dup, dup| dup"
    val duplicate_start =
      Position.make0 13 50 500 "" "" "closure-markup-duplicate"
    val nested_text =
      "|outer| (|inner| if true { outer } else { inner })"
    val nested_start =
      Position.make0 17 60 600 "" "" "closure-markup-nested"
    val shadow_text =
      "|shadow| { let shadow = shadow; shadow }"
    val shadow_start =
      Position.make0 19 70 700 "" "" "closure-markup-shadow"

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) ())
          ())
    val _ = capture_elaboration ordinary_text ordinary_start
    val _ = capture_elaboration duplicate_text duplicate_start
    val _ = capture_elaboration nested_text nested_start
    val _ = capture_elaboration shadow_text shadow_start

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_bound position =
      exists
        (fn (name, properties) =>
          name = Markup.boundN andalso
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
               "closure regression audit: binder entity markup changed")
      end
    fun audit_navigation label definition reference =
      (audit_assert (label ^ " definition lost bound markup")
         (has_bound definition);
       audit_assert (label ^ " reference lost bound markup")
         (has_bound reference);
       audit_assert (label ^ " reference stopped targeting its formal")
         (entity_id Markup.defN definition =
          entity_id Markup.refN reference))

    val (ordinary_def_offset, ordinary_definition) =
      token_position ordinary_text ordinary_start "alpha" 0
    val (_, ordinary_reference) =
      token_position ordinary_text ordinary_start "alpha"
        (ordinary_def_offset + size "alpha")
    val _ =
      audit_navigation
        "ordinary closure formal"
        ordinary_definition ordinary_reference

    val (duplicate_first_offset, duplicate_first_definition) =
      token_position duplicate_text duplicate_start "dup" 0
    val (duplicate_second_offset, duplicate_second_definition) =
      token_position duplicate_text duplicate_start "dup"
        (duplicate_first_offset + size "dup")
    val (_, duplicate_reference) =
      token_position duplicate_text duplicate_start "dup"
        (duplicate_second_offset + size "dup")
    val duplicate_first_id =
      entity_id Markup.defN duplicate_first_definition
    val duplicate_second_id =
      entity_id Markup.defN duplicate_second_definition
    val _ =
      audit_assert "duplicate formal definitions reused an entity ID"
        (duplicate_first_id <> duplicate_second_id)
    val _ =
      audit_navigation
        "duplicate closure formal"
        duplicate_second_definition duplicate_reference
    val _ =
      audit_assert "duplicate body reference targeted the first formal"
        (entity_id Markup.refN duplicate_reference <>
          duplicate_first_id)

    val (nested_outer_offset, nested_outer_definition) =
      token_position nested_text nested_start "outer" 0
    val (nested_inner_offset, nested_inner_definition) =
      token_position nested_text nested_start "inner" 0
    val (_, nested_outer_reference) =
      token_position nested_text nested_start "outer"
        (nested_outer_offset + size "outer")
    val (_, nested_inner_reference) =
      token_position nested_text nested_start "inner"
        (nested_inner_offset + size "inner")
    val _ =
      audit_navigation
        "nested outer closure formal"
        nested_outer_definition nested_outer_reference
    val _ =
      audit_navigation
        "nested inner closure formal"
        nested_inner_definition nested_inner_reference
    val _ =
      audit_assert "nested closure formals reused an entity ID"
        (entity_id Markup.defN nested_outer_definition <>
          entity_id Markup.defN nested_inner_definition)

    val (shadow_outer_offset, shadow_outer_definition) =
      token_position shadow_text shadow_start "shadow" 0
    val (shadow_inner_offset, shadow_inner_definition) =
      token_position shadow_text shadow_start "shadow"
        (shadow_outer_offset + size "shadow")
    val (shadow_outer_reference_offset, shadow_outer_reference) =
      token_position shadow_text shadow_start "shadow"
        (shadow_inner_offset + size "shadow")
    val (_, shadow_inner_reference) =
      token_position shadow_text shadow_start "shadow"
        (shadow_outer_reference_offset + size "shadow")
    val _ =
      audit_navigation
        "shadowed closure formal"
        shadow_outer_definition shadow_outer_reference
    val _ =
      audit_navigation
        "shadowing let binder"
        shadow_inner_definition shadow_inner_reference
    val _ =
      audit_assert "shadowing let binder reused the closure formal entity ID"
        (entity_id Markup.defN shadow_outer_definition <>
          entity_id Markup.defN shadow_inner_definition)
  in
    val _ =
      writeln
        "Closure AST, lowering, allocator, dispatch, and markup regressions passed"
end
\<close>


section\<open> Cast AST, lowering, markup, and recovery \<close>

text\<open>
The cast audit pins the closed target representation, left association,
cast-before-prefix precedence, source position, exact lowering table, semantic
collapses, reserved-word markup, and parser-state recovery after malformed
targets.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("cast regression audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "cast regression audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun path_named expected (UE_Path path) =
          render_path path = expected
      | path_named _ _ = false

    fun target_is expected actual = expected = actual

    val positioned_text = "operand as *mut usize"
    val positioned_start =
      Position.make0 9 14 0 "" "" ""
    val positioned_ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          positioned_text positioned_start)
    val as_offset = size "operand "
    val expected_as =
      Position.symbol_explode
        (String.substring (positioned_text, 0, as_offset))
        positioned_start
    val _ =
      (case positioned_ast of
         UE_Cast
           (operand,
            CT_RawPointer (RPM_Mut, UT_Usize),
            as_position) =>
           (audit_assert "cast operand changed"
              (path_named "operand" operand);
            audit_assert "as position moved"
              (Position.offset_of as_position =
                Position.offset_of expected_as))
       | _ => error "cast regression audit: positioned cast AST changed")

    val _ =
      (case parse "source.field.method()[0]? as i64" of
         UE_Cast
           (UE_Unary
             (U_Propagate,
              UE_Index
                (UE_Call
                  (UC_Method
                    (UE_Field (source, "field", _),
                     Path_Segment ("method", _, NONE)),
                   [], _),
                 UE_Literal (LP_Integer ("0", _)), _),
              _),
            CT_Signed ST_I64, _) =>
           audit_assert "cast lost its complete postfix operand"
             (path_named "source" source)
       | _ =>
           error
             "cast regression audit: postfix operand AST changed")

    val _ =
      (case parse "value as u8 as u16 as i32" of
         UE_Cast
           (UE_Cast
             (UE_Cast
               (value, first, _),
              second, _),
            third, _) =>
           (audit_assert "cast chain lost its operand"
              (path_named "value" value);
            audit_assert "first cast target changed"
              (target_is (CT_Unsigned UT_U8) first);
            audit_assert "second cast target changed"
              (target_is (CT_Unsigned UT_U16) second);
            audit_assert "third cast target changed"
              (target_is (CT_Signed ST_I32) third))
       | _ =>
           error "cast regression audit: cast chain is not left-associated")

    val _ =
      (case parse "!value as u8" of
         UE_Unary
           (U_Not,
            UE_Cast
              (value, CT_Unsigned UT_U8, _),
            _) =>
           audit_assert "not/cast operand changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: cast-before-not precedence changed")

    val _ =
      (case parse "*raw as *const u8" of
         UE_Unary
           (U_Deref,
            UE_Cast
              (raw,
               CT_RawPointer (RPM_Const, UT_U8), _),
            _) =>
           audit_assert "deref/cast operand changed"
             (path_named "raw" raw)
       | _ =>
           error "cast regression audit: cast-before-deref precedence changed")

    val _ =
      (case parse "(!value) as u8" of
         UE_Cast
           (UE_Group
             (UE_Unary (U_Not, value, _), _),
            CT_Unsigned UT_U8, _) =>
           audit_assert "grouped opposite interpretation changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: grouped prefix/cast AST changed")

    val _ =
      (case parse "(value as u32).field.method()[0]?" of
         UE_Unary
           (U_Propagate,
            UE_Index
              (UE_Call
                (UC_Method
                  (UE_Field
                    (UE_Group
                      (UE_Cast
                        (value, CT_Unsigned UT_U32, _), _),
                     "field", _),
                   Path_Segment ("method", _, NONE)),
                 [], _),
               UE_Literal (LP_Integer ("0", _)), _),
            _) =>
           audit_assert "grouped cast postfix chain changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: grouped cast postfix AST changed")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    datatype lowering_kind =
        Unsigned_Lowering
      | Signed_Lowering
      | Pointer_Lowering

    val lowering_cases =
      [("value as u8", Unsigned_Lowering,
        \<^term>\<open>ucastu8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as u16", Unsigned_Lowering,
        \<^term>\<open>ucastu16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as u32", Unsigned_Lowering,
        \<^term>\<open>ucastu32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as u64", Unsigned_Lowering,
        \<^term>\<open>ucastu64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as usize", Unsigned_Lowering,
        \<^term>\<open>ucastu64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as i32", Signed_Lowering,
        \<^term>\<open>ucasti32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as i64", Signed_Lowering,
        \<^term>\<open>ucasti64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *const u8", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as *const u16", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as *const u32", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as *const u64", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *const usize", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *mut u8", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as *mut u16", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as *mut u32", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as *mut u64", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *mut usize", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>)]

    fun count_constant expected term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)
        term 0

    fun cast_count term =
      count_constant \<^const_name>\<open>bind1\<close> term +
      count_constant \<^const_name>\<open>raw_ptr_cast\<close> term

    fun cast_result_type typ =
      Term.map_atyps
        (fn TFree _ => dummyT
          | TVar _ => dummyT
          | atomic => atomic)
        typ

    fun expected_lowering target_function =
      Type.constraint
        (cast_result_type
          (Term.range_type (fastype_of target_function)))
        (Term.list_comb
          (Term.map_types (K dummyT) target_function,
           [unchecked "value"]))

    fun checked text =
      Syntax.check_term ctxt (unchecked text)

    val reference_type_name =
      (case \<^typ>\<open>('address, 'global, 'value) Global_Store.ref\<close> of
         Type (name, _) => name
       | _ => error "cast regression audit: reference type abbreviation changed")

    fun result_width Pointer_Lowering term =
          (case fastype_of term of
             Type (expression_name, [_, value_type, _, _, _, _]) =>
               if expression_name = \<^type_name>\<open>expression\<close>
               then
                 (case value_type of
                    Type (reference_name, [_, _, width]) =>
                      if reference_name = reference_type_name
                      then width
                      else error "cast regression audit: pointer cast result is not a reference"
                  | _ =>
                      error "cast regression audit: pointer cast result is not a reference")
               else error "cast regression audit: cast result is not an expression"
           | _ => error "cast regression audit: cast result type changed")
      | result_width _ term =
          (case fastype_of term of
             Type (expression_name, [_, value_type, _, _, _, _]) =>
               if expression_name = \<^type_name>\<open>expression\<close>
               then value_type
               else error "cast regression audit: cast result is not an expression"
           | _ => error "cast regression audit: cast result type changed")

    fun check_lowering
      (source, kind, target_function, expected_width) =
      let
        val term = unchecked source
        val checked_term = checked source
      in
        audit_assert
          ("wrong lowering for " ^ quote source)
          (Term.aconv (term, expected_lowering target_function));
        audit_assert
          ("source cast did not lower exactly once for " ^ quote source)
          (cast_count term = 1);
        audit_assert
          ("wrong result width for " ^ quote source)
          (result_width kind checked_term = expected_width)
      end

    val _ = List.app check_lowering lowering_cases

    val _ =
      audit_assert "usize stopped collapsing to u64"
        (Term.aconv
          (unchecked "value as usize",
           unchecked "value as u64"))

    val _ =
      audit_assert "pointer usize stopped collapsing to pointer u64"
        (Term.aconv
          (unchecked "value as *const usize",
           unchecked "value as *const u64"))

    val _ =
      List.app
        (fn target =>
          audit_assert
            ("pointer mutability changed lowering for " ^ target)
            (Term.aconv
              (unchecked ("value as *const " ^ target),
               unchecked ("value as *mut " ^ target))))
        ["u8", "u16", "u32", "u64", "usize"]

    val chain = unchecked "value as u8 as u32 as i64"
    val _ =
      audit_assert "three-stage chain did not lower three casts"
        (cast_count chain = 3)
    val _ =
      audit_assert "three-stage lowering lost left nesting"
        (count_constant \<^const_name>\<open>bind1\<close> chain = 3 andalso
         result_width Signed_Lowering
           (checked "value as u8 as u32 as i64") =
             \<^typ>\<open>64 word\<close>)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("cast regression audit: missing " ^ quote needle)
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
      "value as u8; value as u16; value as u32; " ^
      "value as u64; value as usize; value as i32; " ^
      "value as i64; raw as *const u8; raw as *mut usize"
    val markup_start =
      Position.make0 11 3 0 "" "" "cast-markup-audit"
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse_source
                  (Parser_Lex_Util.positioned_content_source
                    markup_text markup_start)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
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
    fun has_entity_markup position =
      has_markup Markup.defN position orelse
      has_markup Markup.refN position

    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size markup_text then rev positions
          else
            (case try (find_from markup_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position markup_text markup_start needle raw
                 in collect (raw + size needle) (position :: positions) end
             | NONE => rev positions)
      in collect 0 [] end

    val keyword_spellings =
      ["as", "u8", "u16", "u32", "u64", "usize", "i32", "i64",
       "const", "mut"]
    val type_spellings =
      ["u8", "u16", "u32", "u64", "usize", "i32", "i64"]
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              (audit_assert
                 (spelling ^ " lost keyword markup")
                 (has_markup Markup.keyword1N position);
               audit_assert
                 (spelling ^ " lost typing markup")
                 (has_markup Markup.typingN position)))
            (all_token_positions spelling))
        keyword_spellings
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                (spelling ^ " received identifier entity markup")
                (not (has_entity_markup position)))
            (all_token_positions spelling))
        type_spellings
    val _ =
      List.app
        (fn position =>
          audit_assert "* stopped being operator markup in cast targets"
            (has_markup Markup.operatorN position))
        (all_token_positions "*")

    val malformed =
      ["as u8",
       "value as",
       "value as *",
       "value as *const",
       "value as *mut",
       "value as u128",
       "value as i8",
       "value as i16",
       "value as i128",
       "value as isize",
       "value as f32",
       "value as f64",
       "value as char",
       "value as bool",
       "value as Target",
       "value as Target::Word",
       "value as Vec::<u8>",
       "value as *const i32",
       "value as *mut i64",
       "value as *const bool",
       "value as *mut Target",
       "value as *mut u128",
       "value as **const u8",
       "value as *const *const u8",
       "value as *const const u8",
       "value as *mut mut u8",
       "value as &u8",
       "value as as u8",
       "value as u8 as",
       "value as u8 as *const",
       "value as ()",
       "value as [u8]",
       "value as u8,",
       "value as u8 trailing",
       "value asu8",
       "value as U8",
       "value as u8_u16",
       "value as u32.field",
       "value as u32.method()",
       "value as u32[0]",
       "value as u32?",
       "value as u32()",
       "value as u8 as u32.field"]

    fun reject_then_recover bad =
      let
        val _ =
          (case Exn.result parse bad of
             Exn.Res _ =>
               error
                 ("cast regression audit: malformed cast accepted: " ^
                   quote bad)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else ())
        val _ =
          (case parse "value as u8" of
             UE_Cast (_, CT_Unsigned UT_U8, _) => ()
           | _ =>
               error
                 ("cast regression audit: parser did not recover after " ^
                   quote bad))
      in () end

    val _ = List.app reject_then_recover malformed
  in
    val _ =
      writeln "Cast AST, lowering, markup, and recovery regressions passed"
  end
\<close>


section\<open> Struct-expression AST, lowering, markup, and recovery \<close>

definition d21_audit_identity1 ::
    \<open>'a \<Rightarrow> (unit, 'a, unit, unit, unit) function_body\<close>
  where \<open> d21_audit_identity1 \<equiv> lift_fun1 (\<lambda>value. value) \<close>

definition d21_audit_first2 ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> d21_audit_first2 \<equiv> lift_fun2 (\<lambda>first second. first) \<close>

definition d21_audit_truth :: bool
  where \<open> d21_audit_truth \<equiv> True \<close>

consts
  d21_audit_marker_a :: nat
  d21_audit_marker_b :: nat
  d21_audit_marker_c :: nat

micro_rust_notation (call) d21_audit_identity1 ("D21AuditOne")
micro_rust_notation (call) d21_audit_first2 ("D21AuditPair")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("struct-expression regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "struct-expression regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun frontend text =
      Syntax.read_term ctxt ("\<lbrakk> " ^ text ^ " \<rbrakk>")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_named_atom name term =
      Term.fold_aterms
        (fn Free (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | Const (candidate, _) =>
              if Long_Name.base_name candidate = name
              then Integer.add 1
              else I
          | _ => I)
        term 0

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("struct-expression regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
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

    val structural_text =
      "D21AuditPair {\n" ^
      "  alpha: \<llangle>d21_audit_marker_a\<rrangle>, // retained comment\n" ^
      "  beta: D21AuditPair { gamma: \<llangle>d21_audit_marker_b\<rrangle>, " ^
        "delta: \<llangle>d21_audit_marker_c\<rrangle> }\n" ^
      "}"
    val structural_start =
      Position.make0 31 700 0 "" "" "struct-expression-audit"
    val structural_stop =
      Position.symbol_explode structural_text structural_start
    val structural_source =
      Parser_Lex_Util.positioned_content_source
        structural_text structural_start
    val structural_ast = parse structural_source

    val control_text =
      "match (D21AuditOne { value: Some(()) }) {\n" ^
      "  Some(_) \<Rightarrow> (),\n" ^
      "  None \<Rightarrow> ()\n" ^
      "}"
    val control_start =
      Position.make0 41 900 0 "" "" "struct-control-head-audit"
    val control_stop =
      Position.symbol_explode control_text control_start
    val control_source =
      Parser_Lex_Util.positioned_content_source
        control_text control_start
    val control_ast = parse control_source

    val (outer_head_raw, outer_head_pos) =
      token_position structural_text structural_start "D21AuditPair" 0
    val (alpha_raw, alpha_pos) =
      token_position structural_text structural_start "alpha" 0
    val (_, marker_a_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_a" alpha_raw
    val (beta_raw, beta_pos) =
      token_position structural_text structural_start "beta" 0
    val (nested_head_raw, nested_head_pos) =
      token_position structural_text structural_start "D21AuditPair"
        (outer_head_raw + size "D21AuditPair")
    val (gamma_raw, gamma_pos) =
      token_position structural_text structural_start "gamma" nested_head_raw
    val (_, marker_b_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_b" gamma_raw
    val (delta_raw, delta_pos) =
      token_position structural_text structural_start "delta" gamma_raw
    val (_, marker_c_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_c" delta_raw
    val (nested_close_raw, nested_close_pos) =
      token_position structural_text structural_start "}" delta_raw
    val (_, outer_close_pos) =
      token_position structural_text structural_start "}"
        (nested_close_raw + 1)
    val nested_span =
      Position.range_position
        (nested_head_pos,
         Position.symbol_explode "}" nested_close_pos)

    val (_, control_match_pos) =
      token_position control_text control_start "match" 0
    val (control_group_raw, control_group_left_pos) =
      token_position control_text control_start "(" 0
    val (control_head_raw, control_head_pos) =
      token_position control_text control_start "D21AuditOne"
        control_group_raw
    val (control_label_raw, control_label_pos) =
      token_position control_text control_start "value" control_head_raw
    val (control_struct_close_raw, control_struct_close_pos) =
      token_position control_text control_start "}" control_label_raw
    val (_, control_group_right_pos) =
      token_position control_text control_start ")"
        (control_struct_close_raw + 1)
    val control_struct_span =
      Position.range_position
        (control_head_pos,
         Position.symbol_explode "}" control_struct_close_pos)
    val control_group_span =
      Position.range_position
        (control_group_left_pos,
         Position.symbol_explode ")" control_group_right_pos)

    val _ =
      (case structural_ast of
         UE_Struct
           (head,
            [SE_Field
               ("alpha", first_label_pos,
                UE_Literal (LP_ValAntiq _)),
             SE_Field
               ("beta", second_label_pos,
                nested as
                  UE_Struct
                    (nested_head,
                     [SE_Field
                        ("gamma", third_label_pos,
                         UE_Literal (LP_ValAntiq _)),
                      SE_Field
                        ("delta", fourth_label_pos,
                         UE_Literal (LP_ValAntiq _))],
                     nested_pos))],
            outer_pos) =>
           (audit_assert "outer head changed"
              (render_path head = "D21AuditPair");
            audit_assert "nested head changed"
              (render_path nested_head = "D21AuditPair");
            audit_assert "outer label order or positions changed"
              (same_range first_label_pos alpha_pos andalso
               same_range second_label_pos beta_pos);
            audit_assert "nested label order or positions changed"
              (same_range third_label_pos gamma_pos andalso
               same_range fourth_label_pos delta_pos);
            audit_assert "outer span no longer covers head through closing brace"
              (Position.offset_of outer_pos =
                 Position.offset_of outer_head_pos andalso
               Position.end_offset_of outer_pos =
                 Position.offset_of structural_stop);
            audit_assert "nested struct span changed"
              (same_range nested_pos nested_span);
            audit_assert "expression_position lost the nested struct boundary"
              (same_range (expression_position nested) nested_span))
       | _ =>
           error "struct-expression regression audit: structural AST changed")

    val _ =
      (case control_ast of
         UE_Match
           (MF_Auto,
            UE_Group
              (nested as
                 UE_Struct
                   (head,
                    [SE_Field ("value", label_pos, _)],
                    struct_pos),
               group_pos),
            _, match_pos) =>
           (audit_assert "grouped control-head struct changed"
              (render_path head = "D21AuditOne");
            audit_assert "grouped control-head label position changed"
              (same_range label_pos control_label_pos);
            audit_assert "grouped control-head struct span changed"
              (same_range struct_pos control_struct_span andalso
               same_range
                 (expression_position nested) control_struct_span);
            audit_assert "grouped control-head span changed"
              (same_range group_pos control_group_span);
            audit_assert "grouped control-head match span changed"
              (Position.offset_of match_pos =
                 Position.offset_of control_match_pos andalso
               Position.end_offset_of match_pos =
                 Position.offset_of control_stop))
       | _ =>
           error
             "struct-expression regression audit: grouped control-head AST changed")

    fun dest_funcall2 term =
      (case Term_Position.strip_positions term of
         Const (name, _) $ function $ first $ second =>
           if name = \<^const_name>\<open>funcall2\<close>
           then (function, first, second)
           else
             error
               ("struct-expression regression audit: expected funcall2, found " ^
                 quote name)
       | _ =>
           error "struct-expression regression audit: funcall2 shape changed")

    val structural_term =
      Parser_Test_Elaboration.expression ctxt structural_source
    val (outer_function, outer_first, outer_second) =
      dest_funcall2 structural_term
    val (nested_function, nested_first, nested_second) =
      dest_funcall2 outer_second
    val _ =
      audit_assert "registered wrapper head was not retained"
        (count_constant
          \<^const_name>\<open>d21_audit_first2\<close>
          outer_function = 1 andalso
         count_constant
          \<^const_name>\<open>d21_audit_first2\<close>
          nested_function = 1)
    val _ =
      audit_assert "first initializer left the first call argument"
        (count_constant
           \<^const_name>\<open>d21_audit_marker_a\<close>
           outer_first = 1 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_b\<close>
           outer_first = 0)
    val _ =
      audit_assert "nested initializer order changed"
        (count_constant
           \<^const_name>\<open>d21_audit_marker_b\<close>
           nested_first = 1 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_c\<close>
           nested_first = 0 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_c\<close>
           nested_second = 1)
    val _ =
      List.app
        (fn marker =>
          audit_assert
            ("initializer marker " ^ quote marker ^
              " was duplicated or dropped")
            (count_constant marker structural_term = 1))
        [\<^const_name>\<open>d21_audit_marker_a\<close>,
         \<^const_name>\<open>d21_audit_marker_b\<close>,
         \<^const_name>\<open>d21_audit_marker_c\<close>]
    val _ =
      List.app
        (fn label =>
          audit_assert
            ("label " ^ quote label ^ " leaked into the HOL term")
            (count_named_atom label structural_term = 0))
        ["alpha", "beta", "gamma", "delta"]

    val canonical =
      checked
        ("D21AuditPair { first: \<llangle>d21_audit_marker_a\<rrangle>, " ^
         "second: \<llangle>d21_audit_marker_b\<rrangle> }")
    val renamed =
      checked
        ("D21AuditPair { unknown: \<llangle>d21_audit_marker_a\<rrangle>, " ^
         "unknown: \<llangle>d21_audit_marker_b\<rrangle> }")
    val _ =
      audit_assert "labels stopped erasing completely"
        (Term.aconv (canonical, renamed))

    val parity_sources =
      ["let mut slot = 1_u64; " ^
         "D21AuditOne { value: slot = 2_u64 }",
       "D21AuditOne { value: " ^
         "[\<llangle>(\<lambda>left::nat. \<lambda>right::nat. " ^
           "FunctionBody (literal (left + right)))\<rrangle>, " ^
          "|left, right| \<llangle>left + right :: nat\<rrangle>] }",
       "for _ in (D21AuditOne { value: [1, 2] }) " ^
         "{ D21AuditOne { value: () }; () }",
       "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) = " ^
         "(D21AuditOne { value: Some(3) }) " ^
         "{ D21AuditOne { value: () }; () }",
       "match (D21AuditOne { value: Some(3) }) " ^
         "{ Some(_) \<Rightarrow> D21AuditOne { value: 1 }, None \<Rightarrow> 0 }",
       "match_case (D21AuditOne { value: Some(3) }) " ^
         "{ Some(_) \<Rightarrow> D21AuditOne { value: 1 }, None \<Rightarrow> 0 }",
       "match_switch (D21AuditOne { value: 42 }) " ^
         "{ 42 \<Rightarrow> D21AuditOne { value: () }, _ \<Rightarrow> () }"]
    val _ =
      List.app
        (fn source =>
          audit_assert
            ("direct frontend alpha parity failed for " ^ quote source)
            (Term.aconv (checked source, frontend source)))
        parity_sources

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                (ignore
                   (Parser_Test_Elaboration.expression ctxt structural_source);
                 ignore
                   (Parser_Test_Elaboration.expression ctxt control_source))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)
    fun has_markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun has_any_entity pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso has_position properties pos)
        markup
    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size structural_text then rev positions
          else
            (case try (find_from structural_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position structural_text structural_start
                       needle raw
                 in collect (raw + size needle) (position :: positions) end
             | NONE => rev positions)
      in collect 0 [] end

    val _ =
      List.app
        (fn head_pos =>
          (audit_assert "struct head lost function-role notation markup"
             (has_entity_markup
               Micro_Rust_Names.notationN head_pos);
           audit_assert "struct head lost registered-call styling"
             (has_markup Markup.keyword3N head_pos)))
        [outer_head_pos, nested_head_pos]
    val _ =
      (audit_assert
         "grouped control-head struct lost function-role notation markup"
         (has_entity_markup
           Micro_Rust_Names.notationN control_head_pos);
       audit_assert
         "grouped control-head struct lost registered-call styling"
         (has_markup Markup.keyword3N control_head_pos);
       audit_assert "grouped control-head label lost free markup"
         (has_markup Markup.freeN control_label_pos);
       audit_assert "grouped control-head label lost typing markup"
         (has_markup Markup.typingN control_label_pos);
       audit_assert "grouped control-head label received entity markup"
         (not (has_any_entity control_label_pos));
       audit_assert "grouped control-head opening parenthesis lost markup"
         (has_markup Markup.delimiterN control_group_left_pos);
       audit_assert "grouped control-head closing parenthesis lost markup"
         (has_markup Markup.delimiterN control_group_right_pos))
    val _ =
      List.app
        (fn (label, pos) =>
          (audit_assert
             ("label " ^ quote label ^ " lost free markup")
             (has_markup Markup.freeN pos);
           audit_assert
             ("label " ^ quote label ^ " lost typing markup")
             (has_markup Markup.typingN pos);
           audit_assert
             ("label " ^ quote label ^ " received entity/selector markup")
             (not (has_any_entity pos));
           audit_assert
             ("label " ^ quote label ^ " received call styling")
             (not (has_markup Markup.keyword3N pos))))
        [("alpha", alpha_pos), ("beta", beta_pos),
         ("gamma", gamma_pos), ("delta", delta_pos)]
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                ("delimiter " ^ quote spelling ^ " lost markup")
                (has_markup Markup.delimiterN position))
            (all_token_positions spelling))
        ["{", "}", ":", ","]
    val (_, comment_pos) =
      token_position structural_text structural_start
        "// retained comment" 0
    val _ =
      audit_assert "line comment lost comment markup"
        (has_markup Markup.comment1N comment_pos)
    val _ =
      List.app
        (fn position =>
          audit_assert "value-antiquotation opener lost delimiter markup"
            (has_markup Markup.delimiterN position))
        (all_token_positions "\<llangle>")
    val _ =
      List.app
        (fn (marker, position) =>
          audit_assert
            ("value-antiquotation body " ^ quote marker ^
              " lost constant entity markup")
            (has_entity_markup Markup.constantN position))
        [("d21_audit_marker_a", marker_a_pos),
         ("d21_audit_marker_b", marker_b_pos),
         ("d21_audit_marker_c", marker_c_pos)]

    val valid_struct =
      "D21AuditPair { first: \<llangle>d21_audit_marker_a\<rrangle>, " ^
      "second: \<llangle>d21_audit_marker_b\<rrangle> }"
    val ordinary_follower = "if d21_audit_truth { () }"
    val ordinary_arm_follower =
      "match d21_audit_truth { _ \<Rightarrow> () }"

    fun expect_failure operation source =
      (case Exn.result operation source of
         Exn.Res _ =>
           error
             ("struct-expression regression audit: expected rejection of " ^
               quote source)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())

    fun assert_recovered () =
      let
        val _ = ignore (checked valid_struct)
        val _ =
          (case parse_text ordinary_follower of
             UE_If
               (UE_Path path, UE_Block (UE_Unit _, _), NONE, _) =>
               audit_assert "ordinary block-followed path changed after failure"
                 (render_path path = "d21_audit_truth")
           | _ =>
               error
                 "struct-expression regression audit: ordinary block follower did not recover")
        val _ =
          (case parse_text ordinary_arm_follower of
             UE_Match (MF_Auto, UE_Path path, _, _) =>
               audit_assert "ordinary match-followed path changed after failure"
                 (render_path path = "d21_audit_truth")
           | _ =>
               error
                 "struct-expression regression audit: ordinary arm follower did not recover")
      in () end

    val _ =
      (expect_failure parse_text
         "if D21AuditOne { value: true } { () }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: $, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: 1, second: }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: \<llangle>1, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure checked
         "D21AuditPair { first: 0 = rhs, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure checked
         ("D21AuditPair { " ^
          "f00: 0, f01: 1, f02: 2, f03: 3, f04: 4, " ^
          "f05: 5, f06: 6, f07: 7, f08: 8, f09: 9, " ^
          "f10: 10, f11: 11, f12: 12, f13: 13, f14: 14 }");
       assert_recovered ())
  in
    val _ =
      writeln
        "Struct-expression AST, lowering, parity, markup, and recovery regressions passed"
  end
\<close>


section\<open> Structural call-arity preflight audit \<close>

consts
  arity_audit_marker_00 :: nat
  arity_audit_marker_01 :: nat
  arity_audit_marker_02 :: nat
  arity_audit_marker_03 :: nat
  arity_audit_marker_04 :: nat
  arity_audit_marker_05 :: nat
  arity_audit_marker_06 :: nat
  arity_audit_marker_07 :: nat
  arity_audit_marker_08 :: nat
  arity_audit_marker_09 :: nat
  arity_audit_marker_10 :: nat
  arity_audit_marker_11 :: nat
  arity_audit_marker_12 :: nat
  arity_audit_marker_13 :: nat

definition arity_audit_backend14 ::
  \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body
  \<close>
  where
    \<open>
      arity_audit_backend14 \<equiv>
        lift_fun14 (\<lambda>a b c d e f g h i j k l m n. a)
    \<close>

definition arity_audit_registered_value :: nat
  where \<open> arity_audit_registered_value = 0 \<close>

micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Call14")
micro_rust_notation (call) arity_audit_backend14 ("arity_audit_method14")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Struct14")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Over")
micro_rust_notation (call) arity_audit_backend14 ("arity_audit_over_method")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::StructOver")
micro_rust_notation (literal) arity_audit_registered_value ("ArityAudit::Value")

text\<open>
The shallow-term layer owns the single \<open>funcall0\<close>-through-\<open>funcall14\<close> table. Translation
preflights the AST's total runtime arity before resolving a callee, applying generic arguments,
parsing embedded HOL, reporting struct labels, or lowering a receiver, argument, or initializer.
The ordinary call constructor still checks the same private table defensively.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("structural call-arity preflight audit: " ^ message)

    fun comma arguments = space_implode ", " arguments
    fun integers first count =
      map string_of_int (first upto (first + count - 1))
    fun call head arguments =
      head ^ "(" ^ comma arguments ^ ")"
    fun method receiver head arguments =
      receiver ^ "." ^ head ^ "(" ^ comma arguments ^ ")"

    val marker_sources =
      ["arity_audit_marker_00", "arity_audit_marker_01",
       "arity_audit_marker_02", "arity_audit_marker_03",
       "arity_audit_marker_04", "arity_audit_marker_05",
       "arity_audit_marker_06", "arity_audit_marker_07",
       "arity_audit_marker_08", "arity_audit_marker_09",
       "arity_audit_marker_10", "arity_audit_marker_11",
       "arity_audit_marker_12", "arity_audit_marker_13"]
    val marker_constants =
      [\<^const_name>\<open>arity_audit_marker_00\<close>,
       \<^const_name>\<open>arity_audit_marker_01\<close>,
       \<^const_name>\<open>arity_audit_marker_02\<close>,
       \<^const_name>\<open>arity_audit_marker_03\<close>,
       \<^const_name>\<open>arity_audit_marker_04\<close>,
       \<^const_name>\<open>arity_audit_marker_05\<close>,
       \<^const_name>\<open>arity_audit_marker_06\<close>,
       \<^const_name>\<open>arity_audit_marker_07\<close>,
       \<^const_name>\<open>arity_audit_marker_08\<close>,
       \<^const_name>\<open>arity_audit_marker_09\<close>,
       \<^const_name>\<open>arity_audit_marker_10\<close>,
       \<^const_name>\<open>arity_audit_marker_11\<close>,
       \<^const_name>\<open>arity_audit_marker_12\<close>,
       \<^const_name>\<open>arity_audit_marker_13\<close>]

    fun checked elaboration_ctxt text =
      Parser_Test_Elaboration.expression elaboration_ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun marker_sequence term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if member (op =) marker_constants name
              then fn names => names @ [name]
              else I
          | _ => I)
        term []

    val valid_direct =
      call "ArityAudit::Call14" marker_sources
    val valid_method =
      method (hd marker_sources) "arity_audit_method14"
        (tl marker_sources)
    val valid_struct =
      "ArityAudit::Struct14 { " ^
      comma
        (map_index
          (fn (index, marker) =>
            "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
            ": " ^ marker)
          marker_sources) ^
      " }"

    fun check_supported_boundary label text =
      let
        val term = checked ctxt text
      in
        audit_assert (label ^ " selected the backend more than once")
          (count_constant
            \<^const_name>\<open>arity_audit_backend14\<close> term = 1);
        audit_assert (label ^ " changed source order or single evaluation")
          (marker_sequence term = marker_constants)
      end

    fun recovery () =
      (check_supported_boundary "direct arity-14 recovery" valid_direct;
       check_supported_boundary "method total-14 recovery" valid_method;
       check_supported_boundary "struct arity-14 recovery" valid_struct;
       ignore (checked ctxt "()"))

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("structural call-arity preflight audit: missing " ^ quote needle)
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

    fun complete_position text start =
      Position.range_position
        (start, Position.symbol_explode text start)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

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

    fun has_entity markup kind identity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            Properties.get properties Markup.nameN = SOME identity andalso
            has_position properties position)
        markup

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

    fun arity_message arity position =
      "urust_expr: unsupported call arity " ^ string_of_int arity ^
      " (max 14; the frontend's surface lowering caps here)" ^
      Position.here position

    fun capture_expression elaboration_ctxt source =
      let
        val captured =
          Synchronized.var "structural_call_arity_reports" ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        Parser_Test_Elaboration.expression
                          elaboration_ctxt source) ()) ())
              ())
      in
        (result,
         fold collect_markup
           (maps YXML.parse_body (Synchronized.value captured)) [])
      end

    fun expect_rejection elaboration_ctxt serial label text arity inspect =
      let
        val start =
          Position.make0 (130 + serial) (9000 + serial * 500) 0 "" ""
            ("structural-call-arity-" ^ label ^ "-audit")
        val position = complete_position text start
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (result, markup) =
          capture_expression elaboration_ctxt source
        val body =
          (case result of
             Exn.Res term =>
               error
                 (label ^ " unexpectedly elaborated to " ^
                   Syntax.string_of_term elaboration_ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = arity_message arity position);
                   YXML.parse_body actual
                 end)
        val expected_range =
          [(Value.print_int (the (Position.offset_of position)),
            Value.print_int (the (Position.end_offset_of position)))]
        val _ =
          audit_assert (label ^ " diagnostic range changed")
            (diagnostic_ranges body = expected_range)
        val _ = inspect text start markup
        val _ = recovery ()
      in () end

    fun no_inspection _ _ _ = ()

    fun assert_no_notation label key position markup =
      (audit_assert (label ^ " resolved notation before arity rejection")
         (not
           (has_entity markup Micro_Rust_Names.notationN key position));
       audit_assert (label ^ " emitted registered-call styling before rejection")
         (not (has_markup markup Markup.keyword3N position)))

    fun inspect_direct text start markup =
      let
        val (head_offset, _) =
          token_position text start "ArityAudit::Over" 0
        val (_, head_position) =
          token_position text start "Over"
            (head_offset + size "ArityAudit::")
        val (value_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, value_position) =
          token_position text start "Value"
            (value_offset + size "ArityAudit::")
      in
        assert_no_notation "direct head" "ArityAudit::Over"
          head_position markup;
        assert_no_notation "direct argument" "ArityAudit::Value"
          value_position markup
      end

    fun inspect_method text start markup =
      let
        val (receiver_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, receiver_position) =
          token_position text start "Value"
            (receiver_offset + size "ArityAudit::")
        val (_, method_position) =
          token_position text start "arity_audit_over_method" 0
      in
        assert_no_notation "method receiver" "ArityAudit::Value"
          receiver_position markup;
        assert_no_notation "method head" "arity_audit_over_method"
          method_position markup
      end

    fun inspect_struct text start markup =
      let
        val (head_offset, _) =
          token_position text start "ArityAudit::StructOver" 0
        val (_, head_position) =
          token_position text start "StructOver"
            (head_offset + size "ArityAudit::")
        val (_, label_position) =
          token_position text start "f00" 0
        val (value_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, value_position) =
          token_position text start "Value"
            (value_offset + size "ArityAudit::")
      in
        assert_no_notation "struct head" "ArityAudit::StructOver"
          head_position markup;
        assert_no_notation "struct initializer" "ArityAudit::Value"
          value_position markup;
        audit_assert "struct label was semantically reported before arity rejection"
          (not (has_markup markup Markup.freeN label_position))
      end

    val fifteen = integers 0 15
    val method_fifteen = integers 1 14
    val method_sixteen = integers 1 15
    val (fixed_names, fixed_ctxt) =
      Variable.add_fixes
        ["arity_audit_fixed", "arity_audit_fixed_method"] ctxt
    val (fixed_head, fixed_method) =
      (case fixed_names of
         [head, method_name] => (head, method_name)
       | _ => error "structural call-arity preflight audit: fixed-name allocation changed")

    val direct_report_text =
      call "ArityAudit::Over"
        ("ArityAudit::Value" :: integers 1 14)
    val method_report_text =
      method "ArityAudit::Value" "arity_audit_over_method"
        method_fifteen
    val struct_report_text =
      "ArityAudit::StructOver { " ^
      comma
        ("f00: ArityAudit::Value" ::
          map
            (fn index =>
              "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
              ": " ^ string_of_int index)
            (1 upto 14)) ^
      " }"

    val _ =
      expect_rejection ctxt 0 "direct-registered-reports"
        direct_report_text 15 inspect_direct
    val _ =
      expect_rejection ctxt 1 "direct-unregistered"
        (call "arity_audit_missing_direct" fifteen) 15 no_inspection
    val _ =
      expect_rejection fixed_ctxt 2 "direct-fixed"
        (call fixed_head fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 3 "direct-shallow"
        (call "cf1" fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 4 "direct-pure"
        (call "Suc" fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 5 "direct-antiquotation"
        (call "\<epsilon>\<open>arity_audit_missing_antiquotation\<close>" fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 6 "direct-function-literal"
        (call
          "\<llangle>arity_audit_missing_function_literal\<rrangle>\<^sub>1::<arity_audit_missing_generic>"
          fifteen)
        15 no_inspection

    val _ =
      expect_rejection ctxt 7 "method-registered-reports"
        method_report_text 15 inspect_method
    val _ =
      expect_rejection ctxt 8 "method-registered-16"
        (method "0" "arity_audit_over_method" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 9 "method-unregistered-15"
        (method "0" "arity_audit_missing_method" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 10 "method-unregistered-16"
        (method "0" "arity_audit_missing_method" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection fixed_ctxt 11 "method-fixed-15"
        (method "0" fixed_method method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection fixed_ctxt 12 "method-fixed-16"
        (method "0" fixed_method method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 13 "method-shallow-15"
        (method "0" "cf1" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 14 "method-shallow-16"
        (method "0" "cf1" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 15 "method-pure-15"
        (method "0" "Suc" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 16 "method-pure-16"
        (method "0" "Suc" method_sixteen)
        16 no_inspection

    val _ =
      expect_rejection ctxt 17 "struct-reports"
        struct_report_text 15 inspect_struct
    val _ =
      expect_rejection ctxt 18 "callee-and-argument-precedence"
        (call "Suc"
          ("unknown_arity_argument!()" :: integers 1 14))
        15 no_inspection
    val _ =
      expect_rejection ctxt 19 "receiver-and-method-precedence"
        (method "unknown_arity_receiver!()" "arity_audit_missing_method"
          ("unknown_arity_argument!()" :: integers 2 13))
        15 no_inspection
    val _ =
      expect_rejection ctxt 20 "struct-head-and-initializer-precedence"
        ("UnknownArityStruct { " ^
         comma
           ("f00: unknown_arity_initializer!()" ::
             map
               (fn index =>
                 "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
                 ": " ^ string_of_int index)
               (1 upto 14)) ^
         " }")
        15 no_inspection

    val _ =
      URust_Shallow_Terms.check_function_call_arity Position.none 14
    val _ =
      (case Exn.result
          (fn () =>
            URust_Shallow_Terms.function_call Position.none HOLogic.unit
              (replicate 15 HOLogic.unit)) () of
         Exn.Res _ =>
           error "structural call-arity preflight audit: defensive function_call accepted arity 15"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "defensive function_call diagnostic changed"
               (Runtime.exn_message exn =
                 arity_message 15 Position.none))
  in
    val _ =
      writeln
        "Structural call-arity preflight, precedence, reports, ranges, recovery, order, and single-evaluation regressions passed"
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
           (macro_path, _, MP_Arguments
             [UE_Unary
               (U_Not,
                UE_Call
                  (UC_Method
                    (UE_Path receiver_path,
                     Path_Segment
                       ("is_none", method_pos, NONE)),
                   [], call_pos),
                _)],
            _) =>
           (audit_assert "assert macro wrapper changed"
              (render_path macro_path = "assert");
            audit_assert "method receiver changed"
              (render_path receiver_path = "o");
            audit_assert "method identifier range moved"
              (same_range method_pos expected_method);
            audit_assert "method call span moved"
              (same_range call_pos expected_call);
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


definition integration_registered_value_audit :: nat
  where \<open> integration_registered_value_audit = 42 \<close>

micro_rust_notation (literal)
  integration_registered_value_audit
  ("IntegrationAudit::Value")


section\<open> Concealed registered-constructor lookup boundary \<close>

experiment
begin

datatype concealed_constructor_audit =
    ConcealedRegistered
  | ConcealedUnregistered

micro_rust_notation (literal)
  concealed_constructor_audit.ConcealedRegistered
  ("ConcealedAudit::Registered")
micro_rust_notation (literal)
  concealed_constructor_audit.ConcealedUnregistered
  ("ConcealedAudit::Unregistered")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("concealed constructor lookup audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source source) of
         SOME expression => expression
       | NONE => error "concealed constructor lookup audit: empty parse")

    fun path_of source =
      (case parse source of
         UE_Path path => path
       | _ => error ("expected path " ^ quote source))

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked source =
      checked_source (Parser_Lex_Util.text_source source)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex = Const (name, _), ...} => name
         | _ =>
             error
               ("concealed constructor lookup audit: missing case metadata for " ^
                 quote type_name))
      end

    val theory = Proof_Context.theory_of ctxt
    val registered_name =
      \<^const_name>\<open>ConcealedRegistered\<close>
    val unregistered_name =
      \<^const_name>\<open>ConcealedUnregistered\<close>
    val concealed_case_name =
      case_constant_name \<^term>\<open>ConcealedRegistered\<close>
    val _ =
      audit_assert "fixture constructor unexpectedly entered Code.is_constr"
        (not (Code.is_constr theory registered_name) andalso
         not (Code.is_constr theory unregistered_name))

    val resolver =
      URust_Resolution.make_constructor_resolver ctxt Position.none
    val registered_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "ConcealedAudit::Registered"))
    val _ =
      (case URust_Resolution.classify_registered_literal ctxt resolver
          (path_of "ConcealedAudit::Registered") of
         URust_Resolution.Registered_Constructor_Literal => ()
       | _ =>
           error
             "concealed constructor lookup audit: registered concealed literal was not classified as a constructor")
    val _ =
      audit_assert "registered concealed identity was not recovered"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term registered_info,
           \<^term>\<open>ConcealedRegistered\<close>))
    val _ =
      audit_assert "registered concealed constructor leaked into basename lookup"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "ConcealedRegistered")))
    val _ =
      audit_assert "second concealed constructor leaked into basename lookup"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "ConcealedUnregistered")))

    val registered_match =
      checked
        ("match_case \<llangle>ConcealedRegistered\<rrangle> { " ^
         "ConcealedAudit::Registered \<Rightarrow> 0, " ^
         "ConcealedAudit::Unregistered \<Rightarrow> 1 }")
    val _ =
      audit_assert "registered concealed match lost its authentic case combinator"
        (count_constant concealed_case_name registered_match = 1)
    val _ =
      audit_assert "registered concealed exhaustive match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          registered_match = 0)

    val unregistered_binder =
      checked
        ("match_case \<llangle>ConcealedUnregistered\<rrangle> { " ^
         "ConcealedUnregistered \<Rightarrow> 0 }")
    val _ =
      audit_assert "unregistered concealed basename stopped being a binder"
        (count_constant unregistered_name unregistered_binder = 1)

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

    val concealed_mixed_text =
      "match \<llangle>ConcealedRegistered\<rrangle> { " ^
      "0 \<Rightarrow> (), ConcealedAudit::Registered \<Rightarrow> () }"
    val concealed_mixed_start =
      Position.make0 64 900 0 "" ""
        "concealed-constructor-mixed-match-audit"
    val concealed_mixed_position =
      Position.range_position
        (concealed_mixed_start,
         Position.symbol_explode concealed_mixed_text concealed_mixed_start)
    val concealed_mixed_source =
      Parser_Lex_Util.positioned_content_source
        concealed_mixed_text concealed_mixed_start
    val concealed_mixed_expected =
      "urust_expr: mixed numeral and constructor patterns in bare `match`" ^
      Position.here concealed_mixed_position
    val concealed_mixed_range =
      (Value.print_int
        (the (Position.offset_of concealed_mixed_position)),
       Value.print_int
        (the (Position.end_offset_of concealed_mixed_position)))
    val concealed_mixed_body =
      (case Exn.result (fn () => checked_source concealed_mixed_source) () of
         Exn.Res term =>
           error
             ("concealed constructor lookup audit: mixed numeral match " ^
              "unexpectedly elaborated to " ^
              Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val actual = Runtime.exn_message exn
             in
               audit_assert
                 "concealed constructor mixed-match diagnostic changed"
                 (actual = concealed_mixed_expected);
               YXML.parse_body actual
             end)
    val _ =
      audit_assert
        "concealed constructor mixed-match range changed"
        (diagnostic_ranges concealed_mixed_body =
          [concealed_mixed_range])

    val recovered_switch =
      checked
        ("match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, " ^
         "_ \<Rightarrow> 2 }")
    val recovered_case =
      checked
        ("match_case \<llangle>ConcealedRegistered\<rrangle> { " ^
         "ConcealedAudit::Registered \<Rightarrow> 0, " ^
         "ConcealedAudit::Unregistered \<Rightarrow> 1 }")
    val recovered_unit = checked "()"
    val _ =
      audit_assert "concealed rejection lost switch recovery"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          recovered_switch = 1)
    val _ =
      audit_assert "concealed rejection lost constructor recovery"
        (count_constant concealed_case_name recovered_case = 1)
    val _ =
      audit_assert "concealed rejection lost unit recovery"
        (count_constant \<^const_name>\<open>Product_Type.Unity\<close>
          recovered_unit = 1)
  in
    val _ =
      writeln
        "Concealed registered identity, mixed-match rejection, recovery, and filtered unregistered lookup regressions passed"
  end
\<close>

end


section\<open> Registered constructor identity audit \<close>

consts
  registered_constructor_scrutinee :: registered_constructor_fixture
  registered_constructor_guard_marker :: bool
  registered_constructor_first_marker :: nat
  registered_constructor_second_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("registered constructor identity audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source source)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "empty parse")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun constant_name term =
      (case Term.head_of term of
         Const (name, _) => name
       | _ => error "expected constant")

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex, ...} => constant_name casex
         | NONE =>
             error
               ("registered constructor identity audit: missing case metadata for " ^
                 quote type_name))
      end

    val nullary_name =
      constant_name \<^term>\<open>RegisteredNullary\<close>
    val unary_name =
      constant_name \<^term>\<open>RegisteredUnary\<close>
    val other_name =
      constant_name \<^term>\<open>RegisteredOther\<close>
    val registered_type_name =
      fst (dest_Type \<^typ>\<open>registered_constructor_fixture\<close>)
    val phantom_a_name =
      constant_name
        \<^term>\<open>RegisteredPhantomA :: nat registered_phantom\<close>
    val phantom_b_name =
      constant_name
        \<^term>\<open>RegisteredPhantomB :: nat registered_phantom\<close>
    val negative_nullary_name =
      constant_name \<^term>\<open>NegativeRegisteredNullary\<close>
    val negative_other_name =
      constant_name \<^term>\<open>NegativeRegisteredOther\<close>
    val negative_phantom_name =
      constant_name
        \<^term>\<open>
          NegativeRegisteredPhantom ::
            nat negative_registered_phantom
        \<close>
    val registered_case_name =
      case_constant_name \<^term>\<open>RegisteredNullary\<close>
    val negative_case_name =
      case_constant_name \<^term>\<open>NegativeRegisteredNullary\<close>
    val negative_phantom_case_name =
      case_constant_name
        \<^term>\<open>
          NegativeRegisteredPhantom ::
            nat negative_registered_phantom
        \<close>

    val exhaustive =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Nullary \<Rightarrow> \<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "Registered::Unary(value) \<Rightarrow> value, " ^
         "Registered::Other \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val partial =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Unary(value) \<Rightarrow> value }")
    val guarded =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Unary(value) if " ^
         "\<llangle>registered_constructor_guard_marker\<rrangle> \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val nonconstructor =
      checked
        ("match_case IntegrationAudit::Value { IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val applied_nonconstructor =
      checked
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         "NegativeRegistered::Applied \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val duplicate_constructor =
      checked
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         "NegativeRegistered::Duplicate \<Rightarrow> 0, " ^
         "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
         "NegativeRegistered::Other \<Rightarrow> 1 }")
    val duplicate_phantom =
      checked
        ("match_case " ^
         "\<llangle>NegativeRegisteredPhantom :: " ^
         "nat negative_registered_phantom\<rrangle> { " ^
         "NegativeRegistered::Phantom \<Rightarrow> 0 }")

    val _ =
      audit_assert "exhaustive match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          exhaustive = 1)
    val _ =
      audit_assert "partial match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          partial = 1)
    val _ =
      audit_assert "guarded match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          guarded = 1)
    val _ =
      audit_assert "exhaustive match lost its authentic case combinator"
        (count_constant registered_case_name exhaustive = 1)
    val _ =
      audit_assert "exhaustive constructor match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close> exhaustive = 0)
    val _ =
      audit_assert "exhaustive constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> exhaustive = 0)
    val _ =
      audit_assert "exhaustive constructor match used generated conditional"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close> exhaustive = 0)
    val _ =
      audit_assert "partial constructor match lost its case combinator"
        (count_constant registered_case_name partial = 1)
    val _ =
      audit_assert "partial constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> partial = 0)
    val _ =
      audit_assert "partial constructor match lost its unmatched fallback"
        (count_constant \<^const_name>\<open>undefined\<close> partial > 0)
    val _ =
      audit_assert "guard marker was duplicated or dropped"
        (count_constant
          \<^const_name>\<open>registered_constructor_guard_marker\<close>
          guarded = 1)
    val _ =
      audit_assert "guarded constructor match lost its authentic case combinator"
        (count_constant registered_case_name guarded = 1)
    val _ =
      audit_assert "guarded constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> guarded = 0)
    val _ =
      audit_assert "guarded match with wildcard fallback retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close> guarded = 0)
    val _ =
      audit_assert "guarded false fall-through lost the next source arm"
        (count_constant
          \<^const_name>\<open>registered_constructor_second_marker\<close>
          guarded > 0)
    val _ =
      audit_assert "registered nonconstructor value-key count changed"
        (count_constant \<^const_name>\<open>integration_registered_value_audit\<close>
          nonconstructor = 2)
    val _ =
      audit_assert "registered nonconstructor lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          nonconstructor > 0)
    val _ =
      audit_assert "registered nonconstructor lost conditional lowering"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close>
          nonconstructor > 0)
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("registered nonconstructor acquired constructor classification " ^
              quote name)
            (count_constant name nonconstructor = 0))
        [nullary_name, unary_name, other_name]
    val _ =
      audit_assert "constructor-headed registered application lost its two values"
        (count_constant
          \<^const_name>\<open>NegativeRegisteredUnary\<close>
          applied_nonconstructor = 2)
    val _ =
      audit_assert "constructor-headed registered application lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          applied_nonconstructor > 0)
    val _ =
      audit_assert "constructor-headed registered application lost conditional lowering"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close>
          applied_nonconstructor > 0)
    val _ =
      audit_assert "duplicate same-constructor registrations became ambiguous"
        (count_constant negative_case_name duplicate_constructor = 1)
    val _ =
      audit_assert "phantom type-instantiated registrations became ambiguous"
        (count_constant negative_phantom_case_name duplicate_phantom = 1)

    fun path_of source =
      (case parse (Parser_Lex_Util.text_source source) of
         UE_Path path => path
       | _ => error ("expected path " ^ quote source))

    val resolver =
      URust_Resolution.make_constructor_resolver
        ctxt Position.none
    val unary_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "Registered::Unary"))
    val phantom_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "RegisteredPhantom::A"))
    val duplicate_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "NegativeRegistered::Duplicate"))
    val duplicate_phantom_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "NegativeRegistered::Phantom"))
    val _ =
      audit_assert "registered nonconstructor became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "IntegrationAudit::Value")))
    val _ =
      audit_assert "constructor-equal definition became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "NegativeRegistered::Value")))
    val _ =
      audit_assert "constructor-headed application became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "NegativeRegistered::Applied")))
    val _ =
      audit_assert "registered unary did not return catalogue identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term unary_info,
           \<^term>\<open>RegisteredUnary\<close>))
    val _ =
      (case URust_Resolution.constructor_family unary_info of
         SOME (_, members) =>
           audit_assert "registered constructor family is incomplete"
             (sort_strings (map constant_name members) =
              sort_strings [nullary_name, unary_name, other_name])
       | NONE => error "registered constructor lost family metadata")
    val _ =
      audit_assert "polymorphic phantom registration lost constructor identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term phantom_info,
           \<^term>\<open>RegisteredPhantomA :: bool registered_phantom\<close>))
    val _ =
      (case URust_Resolution.constructor_family phantom_info of
         SOME (_, members) =>
           audit_assert "phantom constructor family is incomplete"
             (sort_strings (map constant_name members) =
              sort_strings [phantom_a_name, phantom_b_name])
       | NONE => error "phantom constructor lost family metadata")
    val _ =
      audit_assert "duplicate identical registrations lost constructor identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term duplicate_info,
           \<^term>\<open>NegativeRegisteredNullary\<close>))
    val _ =
      audit_assert "phantom registrations did not deduplicate by untyped identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term duplicate_phantom_info,
           \<^term>\<open>
             NegativeRegisteredPhantom ::
               bool negative_registered_phantom
           \<close>))

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

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val markup_text =
      "match_case \<llangle>RegisteredUnary 1\<rrangle> { " ^
      "Registered::Unary(value) \<Rightarrow> (), _ \<Rightarrow> () }"
    val markup_start =
      Position.make0 29 700 0 "" ""
        "registered-constructor-markup-audit"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        markup_text markup_start
    val (path_raw, expected_path) =
      token_position markup_text markup_start
        "Registered::Unary" 0
    val (_, expected_qualifier) =
      token_position markup_text markup_start
        "Registered" path_raw
    val (_, expected_terminal) =
      token_position markup_text markup_start
        "Unary" (path_raw + size "Registered::")
    val pattern_path =
      (case parse markup_source of
         UE_Match
           (_, _, UR_Arm (P_Constr (path, [_]), NONE, _) :: _, _) =>
           path
       | _ => error "registered constructor pattern AST changed")
    val (_, terminal_position) =
      segment_identifier (final_segment pattern_path)
    val _ =
      audit_assert "registered constructor path span changed"
        (same_range (path_position pattern_path) expected_path)
    val _ =
      audit_assert "registered constructor terminal range changed"
        (same_range terminal_position expected_terminal)

    val captured_reports =
      Synchronized.var "registered_constructor_reports"
        ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression
                    ctxt markup_source)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body
          (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun count_markup markup_name position =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)
    fun count_entity kind identity position =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val _ =
      audit_assert "constructor qualifier retained free markup"
        (count_markup Markup.freeN expected_qualifier = 0)
    val _ =
      audit_assert "constructor qualifier datatype entity duplicated or disappeared"
        (count_entity Markup.type_nameN registered_type_name
          expected_qualifier = 1)
    val _ =
      audit_assert "constructor qualifier tconst styling duplicated or disappeared"
        (count_markup Markup.tconstN expected_qualifier = 1)
    val _ =
      audit_assert "constructor terminal constant entity duplicated or disappeared"
        (count_entity Markup.constantN unary_name expected_terminal = 1)
    val _ =
      audit_assert "constructor terminal was reported as a free binder"
        (count_markup Markup.freeN expected_terminal = 0)
    val _ =
      audit_assert "constructor terminal notation entity duplicated or disappeared"
        (count_entity Micro_Rust_Names.notationN
          "Registered::Unary" expected_terminal = 1)
    val _ =
      audit_assert "constructor terminal keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_terminal = 1)

    fun recovery_checks () =
      let
        val constructor_recovery =
          checked
            ("match_case \<llangle>NegativeRegisteredUnary 3\<rrangle> { " ^
             "NegativeRegistered::Nullary \<Rightarrow> 0, " ^
             "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
             "NegativeRegistered::Other \<Rightarrow> 1 }")
        val nonconstructor_recovery =
          checked
            ("match_case \<llangle>negative_registered_nonconstructor\<rrangle> { " ^
             "NegativeRegistered::Value \<Rightarrow> " ^
             "NegativeRegisteredNullary, " ^
             "_ \<Rightarrow> NegativeRegisteredOther }")
      in
        audit_assert "constructor recovery lost authentic identity"
          (count_constant
            \<^const_name>\<open>NegativeRegisteredUnary\<close>
            constructor_recovery > 0);
        audit_assert "nonconstructor recovery lost equality lowering"
          (count_constant \<^const_name>\<open>urust_eq\<close>
            nonconstructor_recovery > 0)
      end

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

    fun expect_exact_rejection serial label text path terminal expected =
      let
        val start =
          Position.make0 (40 + serial) (900 + serial * 200) 0 "" ""
            ("registered-constructor-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (path_raw, _) =
          token_position text start path 0
        val terminal_raw =
          path_raw + size path - size terminal
        val (_, expected_position) =
          token_position text start terminal terminal_raw
        val qualifier_length = find_from path "::" 0
        val qualifier =
          String.substring (path, 0, qualifier_length)
        val (_, expected_qualifier_position) =
          token_position text start qualifier path_raw
        val expected_message =
          expected ^ Position.here expected_position
        val expected_range =
          (Value.print_int (the (Position.offset_of expected_position)),
           Value.print_int (the (Position.end_offset_of expected_position)))
        val captured =
          Synchronized.var
            ("registered_constructor_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Exn.result
                  (fn () =>
                    Parser_Test_Elaboration.expression ctxt source) ())
              ())
        val body =
          (case result of
             Exn.Res term =>
               error
                 ("registered constructor identity audit: " ^ label ^
                  " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = expected_message);
                   YXML.parse_body actual
                 end)
        val rejection_markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
        val _ =
          audit_assert (label ^ " YXML offset/end_offset changed")
            (diagnostic_ranges body = [expected_range])
        val _ =
          audit_assert (label ^ " emitted premature qualifier free markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.freeN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier tconst markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.tconstN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier type entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Markup.type_nameN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal free markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.freeN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal keyword3 markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.keyword3N andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal notation entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Micro_Rust_Names.notationN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal constant entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Markup.constantN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ = recovery_checks ()
      in () end

    val unary_path = "NegativeRegistered::Unary"
    val value_path = "NegativeRegistered::Value"
    val ambiguous_path = "NegativeRegistered::Ambiguous"
    val applied_path = "NegativeRegistered::Applied"
    val _ =
      expect_exact_rejection 0 "zero-arity"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         unary_path ^ " \<Rightarrow> 0, _ \<Rightarrow> 1 }")
        unary_path "Unary"
        ("urust_expr: constructor " ^ quote "Unary" ^
         " expects 1 pattern argument(s), but got 0")
    val _ =
      expect_exact_rejection 1 "excess-arity"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         unary_path ^ "(left, right) \<Rightarrow> left, _ \<Rightarrow> 0 }")
        unary_path "Unary"
        ("urust_expr: constructor " ^ quote unary_path ^
         " expects 1 pattern argument(s), but got 2")
    val _ =
      expect_exact_rejection 2 "nonconstructor-application"
        ("match_case \<llangle>negative_registered_nonconstructor\<rrangle> { " ^
         value_path ^ "(value) \<Rightarrow> value, _ \<Rightarrow> " ^
         "NegativeRegisteredNullary }")
        value_path "Value"
        ("urust_expr: `" ^ value_path ^ "` is not a known constructor")
    val _ =
      expect_exact_rejection 3 "distinct-constructor-ambiguity"
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         ambiguous_path ^ " \<Rightarrow> 0, _ \<Rightarrow> 1 }")
        ambiguous_path "Ambiguous"
        ("urust_expr: constructor pattern " ^ quote ambiguous_path ^
         " is ambiguous; candidates: " ^
         space_implode ", "
           (sort_strings [negative_nullary_name, negative_other_name]))
    val _ =
      expect_exact_rejection 4 "constructor-headed-application"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         applied_path ^ "(value) \<Rightarrow> value, _ \<Rightarrow> 0 }")
        applied_path "Applied"
        ("urust_expr: `" ^ applied_path ^ "` is not a known constructor")
  in
    val _ =
      writeln
        "Registered constructor identity, diagnostics, recovery, lowering, range, markup, and single-evaluation regressions passed"
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

    fun assert_constructor_qualifier label expected_type position markup =
      (audit_assert (label ^ " retained free markup")
         (count_markup Markup.freeN position markup = 0);
       audit_assert (label ^ " lost datatype navigation")
         (count_entity Markup.type_nameN expected_type position markup = 1);
       audit_assert (label ^ " lost tconst styling")
         (count_markup Markup.tconstN position markup = 1))

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
        fixture_type_name direct_value_qualifier direct_markup
    val _ =
      assert_constructor_qualifier "pattern qualifier"
        fixture_type_name direct_pattern_qualifier direct_markup
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
          (audit_assert (label ^ " lost module-like free markup")
             (count_markup Markup.freeN position module_markup = 1);
           audit_assert (label ^ " acquired datatype styling")
             (count_markup Markup.tconstN position module_markup = 0);
           audit_assert (label ^ " acquired datatype navigation")
             (count_entity_kind Markup.type_nameN position
               module_markup = 0)))
        [("value outer qualifier", module_value_outer),
         ("pattern outer qualifier", module_pattern_outer)]
    val _ =
      assert_constructor_qualifier "value nearest qualifier"
        fixture_type_name module_value_type module_markup
    val _ =
      assert_constructor_qualifier "pattern nearest qualifier"
        fixture_type_name module_pattern_type module_markup

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
          (audit_assert (label ^ " lost free markup")
             (count_markup Markup.freeN position value_markup = 1);
           audit_assert (label ^ " acquired tconst styling")
             (count_markup Markup.tconstN position value_markup = 0);
           audit_assert (label ^ " acquired datatype navigation")
             (count_entity_kind Markup.type_nameN position
               value_markup = 0)))
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
          (audit_assert (label ^ " lost free markup")
             (count_markup Markup.freeN position call_markup = 1);
           audit_assert (label ^ " acquired tconst styling")
             (count_markup Markup.tconstN position call_markup = 0);
           audit_assert (label ^ " acquired datatype navigation")
             (count_entity_kind Markup.type_nameN position
               call_markup = 0)))
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
      audit_assert "multi-backend datatype styling did not cover both families"
        (count_markup Markup.tconstN families_qualifier
          families_markup = 2)
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


section\<open> Contextual bare-match classification audit \<close>

consts
  mixed_match_scrutinee_marker :: nat
  mixed_match_first_body_marker :: nat
  mixed_match_second_body_marker :: nat
  mixed_match_fallback_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("contextual bare-match classification audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE =>
           error "contextual bare-match classification audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked text =
      checked_source (Parser_Lex_Util.text_source text)

    fun path_of_source source =
      (case parse_source source of
         UE_Path path => path
       | _ => error "contextual bare-match classification audit: expected path")

    fun path_of text =
      path_of_source (Parser_Lex_Util.text_source text)

    fun class_matches expected actual =
      (case (expected, actual) of
         (URust_Resolution.Unregistered_Literal,
          URust_Resolution.Unregistered_Literal) => true
       | (URust_Resolution.Registered_Value_Literal,
          URust_Resolution.Registered_Value_Literal) => true
       | (URust_Resolution.Registered_Constructor_Literal,
          URust_Resolution.Registered_Constructor_Literal) => true
       | _ => false)

    fun class_name URust_Resolution.Unregistered_Literal = "unregistered"
      | class_name URust_Resolution.Registered_Value_Literal = "value"
      | class_name URust_Resolution.Registered_Constructor_Literal =
          "constructor"

    fun expect_class label expected path =
      let
        val resolver =
          URust_Resolution.make_constructor_resolver
            ctxt (path_position path)
        val actual =
          URust_Resolution.classify_registered_literal
            ctxt resolver path
      in
        if class_matches expected actual
        then ()
        else
          error
            ("contextual bare-match classification audit: " ^ label ^
              " classification changed from " ^ class_name expected ^
              " to " ^ class_name actual)
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun expect_report_free_class serial label expected text =
      let
        val start =
          Position.make0 (96 + serial) (33000 + serial * 500) 0 "" ""
            ("contextual-match-" ^ label ^ "-classification-audit")
        val path =
          path_of_source
            (Parser_Lex_Util.positioned_content_source text start)
        val resolver =
          URust_Resolution.make_constructor_resolver
            ctxt (path_position path)
        val captured =
          Synchronized.var
            ("contextual_match_" ^ label ^ "_classification_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val actual =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    URust_Resolution.classify_registered_literal
                      ctxt resolver path) ())
              ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
        val segment_positions =
          map (#2 o segment_identifier) (path_segments path)
        val reported_at_path =
          exists
            (fn (_, properties) =>
              exists (has_position properties) segment_positions)
            markup
      in
        audit_assert (label ^ " classification changed")
          (class_matches expected actual);
        audit_assert (label ^ " classification emitted path reports")
          (not reported_at_path)
      end

    val _ =
      expect_class "qualified registered value"
        URust_Resolution.Registered_Value_Literal
        (path_of "IntegrationAudit::Value")
    val _ =
      expect_class "single-segment registered value"
        URust_Resolution.Registered_Value_Literal
        (path_of "registered_seven")
    val _ =
      expect_report_free_class 0 "merged constructor/value exact key"
        URust_Resolution.Registered_Constructor_Literal
        "Color::Red"
    val _ =
      expect_class "registered constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "Registered::Nullary")
    val _ =
      expect_class "registered phantom constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "RegisteredPhantom::A")
    val _ =
      expect_class "duplicate registered constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "NegativeRegistered::Duplicate")
    val _ =
      expect_report_free_class 1 "constructor-wins exact key"
        URust_Resolution.Registered_Constructor_Literal
        "NegativeRegistered::ConstructorWins"
    val _ =
      expect_report_free_class 2 "two-constructor exact key"
        URust_Resolution.Registered_Constructor_Literal
        "NegativeRegistered::Ambiguous"
    val _ =
      expect_class "constructor-equal definition"
        URust_Resolution.Registered_Value_Literal
        (path_of "NegativeRegistered::Value")
    val _ =
      expect_class "constructor-headed application"
        URust_Resolution.Registered_Value_Literal
        (path_of "NegativeRegistered::Applied")
    val _ =
      expect_class "unregistered qualified path"
        URust_Resolution.Unregistered_Literal
        (path_of "Unregistered::Value")

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

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val ast_text =
      "match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, 7 \<Rightarrow> 2, _ \<Rightarrow> 3 }"
    val ast_start =
      Position.make0 71 1700 0 "" ""
        "contextual-match-ast-audit"
    val ast_source =
      Parser_Lex_Util.positioned_content_source ast_text ast_start
    val ast_stop = Position.symbol_explode ast_text ast_start
    val expected_match =
      Position.range_position (ast_start, ast_stop)
    val (first_numeral_raw, expected_first_numeral) =
      token_position ast_text ast_start "0" (size "match 42 { ")
    val (_, expected_value_path) =
      token_position ast_text ast_start "IntegrationAudit::Value"
        (first_numeral_raw + 1)
    val (value_raw, expected_qualifier) =
      token_position ast_text ast_start "IntegrationAudit"
        (first_numeral_raw + 1)
    val (_, expected_terminal) =
      token_position ast_text ast_start "Value"
        (value_raw + size "IntegrationAudit::")
    val (_, expected_second_numeral) =
      token_position ast_text ast_start "7"
        (value_raw + size "IntegrationAudit::Value")
    val _ =
      (case parse_source ast_source of
         UE_Match
           (MF_Auto, _,
            [UR_Arm (P_Literal (LP_Integer (_, first_pos)), NONE, _),
             UR_Arm (P_Path path, NONE, _),
             UR_Arm (P_Literal (LP_Integer (_, second_pos)), NONE, _),
             UR_Arm (P_Wild _, NONE, _)],
            match_pos) =>
           let
             val (_, terminal_pos) =
               segment_identifier (final_segment path)
             val qualifier_pos =
               #2
                 (segment_identifier
                   (hd (path_segments path)))
           in
             audit_assert "contextual classification rewrote MF_Auto"
               true;
             audit_assert "bare match span changed"
               (same_range match_pos expected_match);
             audit_assert "first numeral range changed"
               (same_range first_pos expected_first_numeral);
             audit_assert "second numeral range changed"
               (same_range second_pos expected_second_numeral);
             audit_assert "registered path range changed"
               (same_range (path_position path) expected_value_path);
             audit_assert "registered qualifier range changed"
               (same_range qualifier_pos expected_qualifier);
             audit_assert "registered terminal range changed"
               (same_range terminal_pos expected_terminal)
           end
       | _ => error "contextual bare-match classification audit: AST changed")

    val identifier_text =
      "match 7 { 0 \<Rightarrow> 0, registered_seven \<Rightarrow> 1, _ \<Rightarrow> 2 }"
    val identifier_start =
      Position.make0 72 1900 0 "" ""
        "contextual-match-identifier-ast-audit"
    val (_, expected_identifier) =
      token_position identifier_text identifier_start
        "registered_seven" 0
    val _ =
      (case parse_source
          (Parser_Lex_Util.positioned_content_source
            identifier_text identifier_start) of
         UE_Match
           (_, _,
            [_,
             UR_Arm (P_Ident (_, identifier_pos), NONE, _),
             _],
            _) =>
           audit_assert "single-segment registered key range changed"
             (same_range identifier_pos expected_identifier)
       | _ =>
           error
             "contextual bare-match classification audit: identifier AST changed")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex = Const (name, _), ...} => name
         | _ =>
             error
               ("contextual bare-match classification audit: missing case metadata for " ^
                 quote type_name))
      end

    val registered_case_name =
      case_constant_name \<^term>\<open>RegisteredNullary\<close>
    val negative_case_name =
      case_constant_name \<^term>\<open>NegativeRegisteredNullary\<close>

    val auto =
      checked
        ("match \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "0 \<Rightarrow> \<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_second_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val explicit =
      checked
        ("match_switch \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "0 \<Rightarrow> \<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_second_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "auto registered-value mixture differs from explicit switch"
        (Term.aconv (auto, explicit))
    val _ =
      audit_assert "auto registered-value mixture lost ncase_selector"
        (count_constant \<^const_name>\<open>ncase_selector\<close> auto = 1)
    val _ =
      audit_assert "auto registered-value mixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>mixed_match_scrutinee_marker\<close>
          auto = 1)
    val _ =
      audit_assert "registered backend was duplicated or dropped"
        (count_constant
          \<^const_name>\<open>integration_registered_value_audit\<close>
          auto = 1)
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("switch body marker was duplicated or dropped: " ^ name)
            (count_constant name auto = 1))
        [\<^const_name>\<open>mixed_match_first_body_marker\<close>,
         \<^const_name>\<open>mixed_match_second_body_marker\<close>,
         \<^const_name>\<open>mixed_match_fallback_marker\<close>]
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("switch lowering introduced " ^ quote name)
            (count_constant name auto = 0))
        [\<^const_name>\<open>case_guard\<close>,
         \<^const_name>\<open>urust_eq\<close>,
         \<^const_name>\<open>two_armed_conditional\<close>,
         \<^const_name>\<open>undefined\<close>,
         \<^const_name>\<open>RegisteredNullary\<close>]

    val case_preferred =
      checked
        ("match \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "registered value without numeral selected switch"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          case_preferred = 0)
    val _ =
      audit_assert "registered value without numeral lost case equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          case_preferred > 0)
    val _ =
      audit_assert "registered value without numeral lost case conditional"
        (count_constant \<^const_name>\<open>two_armed_conditional\<close>
          case_preferred > 0)

    val constructor_wins =
      checked
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         "NegativeRegistered::ConstructorWins \<Rightarrow> 0, " ^
         "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
         "NegativeRegistered::Other \<Rightarrow> 1 }")
    val _ =
      audit_assert "constructor/nonconstructor exact key did not select the constructor"
        (count_constant negative_case_name constructor_wins = 1)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_markup label source =
      let
        val captured =
          Synchronized.var
            ("contextual_match_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () => ignore (checked_source source)) ())
              ())
      in
        fold collect_markup
          (maps YXML.parse_body (Synchronized.value captured)) []
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

    fun count_entity kind identity position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val qualified_markup = capture_markup "qualified" ast_source
    val _ =
      audit_assert "first numeral markup duplicated or disappeared"
        (count_markup Markup.numeralN expected_first_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "second numeral markup duplicated or disappeared"
        (count_markup Markup.numeralN expected_second_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "first numeral typing markup duplicated or disappeared"
        (count_markup Markup.typingN expected_first_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "second numeral typing markup duplicated or disappeared"
        (count_markup Markup.typingN expected_second_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "registered qualifier free markup duplicated or disappeared"
        (count_markup Markup.freeN expected_qualifier
          qualified_markup = 1)
    val _ =
      audit_assert "registered terminal notation report duplicated"
        (count_entity Micro_Rust_Names.notationN "IntegrationAudit::Value"
          expected_terminal qualified_markup = 1)
    val _ =
      audit_assert "registered terminal keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_terminal
          qualified_markup = 1)
    val _ =
      audit_assert "registered terminal acquired typing markup"
        (count_markup Markup.typingN expected_terminal
          qualified_markup = 0)
    val _ =
      audit_assert "registered nonconstructor constant entity count changed"
        (count_entity Markup.constantN
          \<^const_name>\<open>integration_registered_value_audit\<close>
          expected_terminal qualified_markup = 1)

    val identifier_source =
      Parser_Lex_Util.positioned_content_source
        identifier_text identifier_start
    val identifier_markup =
      capture_markup "identifier" identifier_source
    val _ =
      audit_assert "single-segment notation report duplicated"
        (count_entity Micro_Rust_Names.notationN "registered_seven"
          expected_identifier identifier_markup = 1)
    val _ =
      audit_assert "single-segment keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_identifier
          identifier_markup = 1)
    val _ =
      audit_assert "single-segment registration acquired typing markup"
        (count_markup Markup.typingN expected_identifier
          identifier_markup = 0)

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

    fun recovery_checks () =
      let
        val recovered_switch =
          checked
            ("match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, " ^
             "_ \<Rightarrow> 2 }")
        val recovered_case =
          checked
            ("match \<llangle>RegisteredNullary\<rrangle> { " ^
             "Registered::Nullary \<Rightarrow> 0, " ^
             "Registered::Unary(value) \<Rightarrow> value, " ^
             "Registered::Other \<Rightarrow> 1 }")
        val recovered_unit = checked "()"
      in
        audit_assert "registered-value switch recovery failed"
          (count_constant \<^const_name>\<open>ncase_selector\<close>
            recovered_switch = 1);
        audit_assert "registered-constructor case recovery failed"
          (count_constant registered_case_name recovered_case = 1);
        audit_assert "unit recovery failed"
          (count_constant \<^const_name>\<open>Product_Type.Unity\<close>
            recovered_unit = 1)
      end

    fun expect_exact_rejection serial label text expected_position expected =
      let
        val start =
          Position.make0 (80 + serial) (2300 + serial * 300) 0 "" ""
            ("contextual-match-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val position = expected_position text start
        val expected_message = expected ^ Position.here position
        val expected_range =
          (Value.print_int (the (Position.offset_of position)),
           Value.print_int (the (Position.end_offset_of position)))
        val body =
          (case Exn.result (fn () => checked_source source) () of
             Exn.Res term =>
               error
                 ("contextual bare-match classification audit: " ^
                  label ^ " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = expected_message);
                   YXML.parse_body actual
                 end)
        val _ =
          audit_assert (label ^ " YXML offset/end_offset changed")
            (diagnostic_ranges body = [expected_range])
        val _ = recovery_checks ()
      in () end

    fun complete_range text start =
      Position.range_position
        (start, Position.symbol_explode text start)

    fun token_range needle offset text start =
      #2 (token_position text start needle offset)

    val constructor_mixed_text =
      "match \<llangle>RegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), Registered::Nullary \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 0 "registered-constructor-mix"
        constructor_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"

    val guarded_text =
      "match 42 { 0 if True \<Rightarrow> (), IntegrationAudit::Value \<Rightarrow> (), " ^
      "_ \<Rightarrow> () }"
    val guarded_numeral_offset =
      find_from guarded_text "0" (size "match 42 { ")
    val _ =
      expect_exact_rejection 1 "guard-forced-case"
        guarded_text (token_range "0" guarded_numeral_offset)
        "urust_expr: numeric patterns are not supported in case patterns"

    val switch_guard_text =
      "match_switch 42 { IntegrationAudit::Value if True \<Rightarrow> (), _ \<Rightarrow> () }"
    val switch_guard_offset =
      find_from switch_guard_text "if" 0
    val _ =
      expect_exact_rejection 2 "explicit-switch-guard"
        switch_guard_text (token_range "if" switch_guard_offset)
        "urust_expr: guards are not supported in explicit `match_switch`"

    val identifier_failure_text =
      "match 0 { 0 \<Rightarrow> (), unregistered_key \<Rightarrow> () }"
    val identifier_failure_offset =
      find_from identifier_failure_text "unregistered_key" 0
    val _ =
      expect_exact_rejection 3 "unregistered-identifier"
        identifier_failure_text
        (token_range "unregistered_key" identifier_failure_offset)
        ("urust_expr: unsupported match_switch key " ^
         quote "unregistered_key" ^
         " (numeral or `_` only; const-id / path keys not yet supported)")

    val constructor_wins_mixed_text =
      "match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), NegativeRegistered::ConstructorWins \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 4 "constructor-wins-mix"
        constructor_wins_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"

    val ambiguous_mixed_text =
      "match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), NegativeRegistered::Ambiguous \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 5 "two-constructor-mix"
        ambiguous_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"
  in
    val _ =
      writeln
        "Contextual bare-match classification, lowering, range, markup, diagnostics, recovery, and single-evaluation regressions passed"
  end
\<close>


section\<open> Or-pattern binder-set validation \<close>

datatype binder_or_audit_fixture =
    BinderAuditA nat nat
  | BinderAuditB nat nat
  | BinderAuditC nat nat
  | BinderAuditSliceA \<open>nat list\<close>
  | BinderAuditSliceB \<open>nat list\<close>

text\<open>
The first alternative is the canonical binder signature. Every alternative is recursively checked
for duplicates before the name sets are compared; rejection precedes local allocation and guard/body
lowering. Successful alternatives share the first signature's entity identities even when source
order and structural positions differ.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("or-pattern binder audit: " ^ message)

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked text =
      checked_source (Parser_Lex_Util.text_source text)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("or-pattern binder audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun nth_raw text needle index =
      let
        fun seek 0 offset = find_from text needle offset
          | seek remaining offset =
              let val found = find_from text needle offset
              in seek (remaining - 1) (found + size needle) end
      in seek index 0 end

    fun token_position text start needle index =
      let
        val raw = nth_raw text needle index
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (token_start, Position.symbol_explode needle token_start)
      end

    fun position_range position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

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

    fun same_ranges left right =
      length left = length right andalso
        List.all (fn range => member (op =) right range) left

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun markup_of reports =
      fold collect_markup (maps YXML.parse_body reports) []

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup_name position markup =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup

    fun has_urust_entity position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            has_position properties position)
        markup

    fun entity_id property position markup =
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
               ("or-pattern binder audit: entity markup changed" ^
                 Position.here position))
      end

    fun has_entity_property property position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            is_some (Properties.get properties property) andalso
            has_position properties position)
        markup

    fun capture_expression text start =
      let
        val captured =
          Synchronized.var "or_pattern_binder_reports" ([]: string list)
        fun capture_reports chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture_reports
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        checked_source
                          (Parser_Lex_Util.positioned_content_source
                            text start)) ()) ())
              ())
      in (result, markup_of (Synchronized.value captured)) end

    val recovery_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | " ^
      "BinderAuditC(x, y) \<Rightarrow> x }"

    fun recover label =
      (ignore (checked recovery_text);
       ignore (checked "()");
       writeln ("or-pattern recovery passed after " ^ label))

    fun expect_rejection serial label text expected positions forbidden =
      let
        val start =
          Position.make0 (110 + serial) (7000 + serial * 400) 0 "" ""
            ("or-pattern-" ^ label ^ "-audit")
        val (result, markup) = capture_expression text start
        val actual =
          (case result of
             Exn.Res term =>
               error
                 ("or-pattern binder audit: " ^ label ^
                  " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else Runtime.exn_message exn)
        val _ =
          audit_assert (label ^ " exact diagnostic changed")
            (actual = expected start)
        val actual_ranges = diagnostic_ranges (YXML.parse_body actual)
        val expected_ranges =
          map (position_range o (fn position => position start)) positions
        val _ =
          audit_assert (label ^ " diagnostic ranges changed")
            (same_ranges actual_ranges expected_ranges)
        val _ =
          List.app
            (fn unexpected =>
              audit_assert
                (label ^ " elaborated " ^ quote unexpected)
                (not (String.isSubstring unexpected actual)))
            forbidden
        val _ = recover label
      in (start, markup) end

    fun missing_message name primary secondary start =
      "urust_expr: or-pattern alternative is missing binder " ^ quote name ^
      Position.here (primary start) ^
      "\nThe first alternative binds it here" ^
      Position.here (secondary start)

    fun extra_message name primary start =
      "urust_expr: or-pattern alternative has extra binder " ^ quote name ^
      Position.here (primary start)

    fun duplicate_message name repeated original start =
      "urust_expr: duplicate pattern binder " ^ quote name ^
      Position.here (repeated start) ^
      "\nThe original binder is here" ^
      Position.here (original start)

    val missing_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x }"
    fun missing_bar start = token_position missing_text start "|" 0
    fun missing_first_x start = token_position missing_text start "x" 0
    fun missing_body_x start = token_position missing_text start "x" 1
    val (missing_start, missing_markup) =
      expect_rejection 0 "missing" missing_text
        (missing_message "x" missing_bar missing_first_x)
        [missing_bar, missing_first_x] []
    val _ =
      audit_assert "missing-binder bar lost operator markup"
        (has_markup Markup.operatorN
          (missing_bar missing_start) missing_markup)
    val _ =
      audit_assert "missing-binder bar lost typing markup"
        (has_markup Markup.typingN
          (missing_bar missing_start) missing_markup)
    val _ =
      List.app
        (fn position =>
          (audit_assert "rejected binder acquired bound markup"
             (not (has_markup Markup.boundN position missing_markup));
           audit_assert "rejected binder acquired an entity"
             (not (has_urust_entity position missing_markup))))
        [missing_first_x missing_start, missing_body_x missing_start]

    val extra_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { None | Some(x) \<Rightarrow> 0 }"
    fun extra_x start = token_position extra_text start "x" 0
    val (extra_start, extra_markup) =
      expect_rejection 1 "extra" extra_text
        (extra_message "x" extra_x) [extra_x] []
    val _ =
      audit_assert "extra rejected binder acquired bound markup"
        (not (has_markup Markup.boundN (extra_x extra_start) extra_markup))
    val _ =
      audit_assert "extra rejected binder acquired an entity"
        (not (has_urust_entity (extra_x extra_start) extra_markup))

    val deterministic_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(z, x) | BinderAuditB(_, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun deterministic_bar start =
      token_position deterministic_text start "|" 0
    fun deterministic_x start =
      token_position deterministic_text start "x" 0
    val _ =
      expect_rejection 2 "deterministic-missing" deterministic_text
        (missing_message "x" deterministic_bar deterministic_x)
        [deterministic_bar, deterministic_x] []

    val third_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, _) | BinderAuditB(x, _) | " ^
      "BinderAuditC(_, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun third_first_bar start = token_position third_text start "|" 0
    fun third_first_x start = token_position third_text start "x" 0
    val _ =
      expect_rejection 3 "third-alternative" third_text
        (missing_message "x" third_first_bar third_first_x)
        [third_first_bar, third_first_x] []

    val nested_missing_text =
      "match_case \<llangle>Some (Ok (1 :: nat))\<rrangle> { " ^
      "Some(Ok(x) | Err(y)) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun nested_missing_bar start =
      token_position nested_missing_text start "|" 0
    fun nested_missing_x start =
      token_position nested_missing_text start "x" 0
    val _ =
      expect_rejection 4 "nested-missing-before-extra" nested_missing_text
        (missing_message "x" nested_missing_bar nested_missing_x)
        [nested_missing_bar, nested_missing_x] []

    val nested_extra_text =
      "match_case \<llangle>Some (Some (1 :: nat))\<rrangle> { " ^
      "Some(None | Some(x)) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun nested_extra_x start =
      token_position nested_extra_text start "x" 0
    val _ =
      expect_rejection 5 "nested-extra" nested_extra_text
        (extra_message "x" nested_extra_x) [nested_extra_x] []

    val guarded_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { " ^
      "Some(x) | None if unknown_binder_guard!() \<Rightarrow> " ^
      "unknown_binder_body!(), _ \<Rightarrow> 0 }"
    fun guarded_bar start = token_position guarded_text start "|" 0
    fun guarded_x start = token_position guarded_text start "x" 0
    val _ =
      expect_rejection 6 "guarded" guarded_text
        (missing_message "x" guarded_bar guarded_x)
        [guarded_bar, guarded_x]
        ["unknown_binder_guard", "unknown_binder_body"]

    val slice_missing_text =
      "match_case \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
      "BinderAuditSliceA([x, ..]) | BinderAuditSliceB([]) \<Rightarrow> 0, " ^
      "_ \<Rightarrow> 0 }"
    fun slice_missing_bar start =
      token_position slice_missing_text start "|" 0
    fun slice_missing_x start =
      token_position slice_missing_text start "x" 0
    val _ =
      expect_rejection 7 "slice-missing" slice_missing_text
        (missing_message "x" slice_missing_bar slice_missing_x)
        [slice_missing_bar, slice_missing_x] []

    val slice_extra_text =
      "match_case \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
      "BinderAuditSliceA([]) | BinderAuditSliceB([.., x]) \<Rightarrow> 0, " ^
      "_ \<Rightarrow> 0 }"
    fun slice_extra_x start =
      token_position slice_extra_text start "x" 0
    val _ =
      expect_rejection 8 "slice-extra" slice_extra_text
        (extra_message "x" slice_extra_x) [slice_extra_x] []

    val duplicate_first_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, x) | BinderAuditB(y, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun duplicate_first_original start =
      token_position duplicate_first_text start "x" 0
    fun duplicate_first_repeated start =
      token_position duplicate_first_text start "x" 1
    val _ =
      expect_rejection 9 "duplicate-first" duplicate_first_text
        (duplicate_message "x"
          duplicate_first_repeated duplicate_first_original)
        [duplicate_first_repeated, duplicate_first_original] []

    val duplicate_later_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, _) | BinderAuditB(y, y) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun duplicate_later_original start =
      token_position duplicate_later_text start "y" 0
    fun duplicate_later_repeated start =
      token_position duplicate_later_text start "y" 1
    val _ =
      expect_rejection 10 "duplicate-later" duplicate_later_text
        (duplicate_message "y"
          duplicate_later_repeated duplicate_later_original)
        [duplicate_later_repeated, duplicate_later_original] []

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "or-pattern binder audit: empty parse")

    fun callback_trace text =
      let
        val calls = Unsynchronized.ref ([]: string list)
        fun lower _ expression =
          let
            val label =
              (case expression of
                 UE_Path path => render_path path
               | _ => "<non-path>")
            val _ = calls := label :: !calls
          in Free ("_" ^ label, dummyT) end
        val result =
          (case parse text of
             UE_Match arguments =>
               Exn.result
                 (fn () =>
                   URust_Matching.lower_match lower ctxt
                     URust_Resolution.empty_environment arguments) ()
           | _ => error "or-pattern binder audit: callback fixture changed")
      in (result, rev (!calls)) end

    val invalid_callback_text =
      "match_case binder_or_scrutinee_probe { " ^
      "BinderAuditA(x, _) | BinderAuditB(_, _) " ^
      "if binder_or_guard_probe \<Rightarrow> binder_or_body_probe, " ^
      "_ \<Rightarrow> binder_or_fallback_probe }"
    val (invalid_callback_result, invalid_callback_calls) =
      callback_trace invalid_callback_text
    val _ =
      (case invalid_callback_result of
         Exn.Res _ =>
           error "or-pattern binder audit: invalid callback fixture elaborated"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "callback rejection changed"
               (String.isSubstring
                 "or-pattern alternative is missing binder \"x\""
                 (Runtime.exn_message exn)))
    val _ =
      audit_assert "rejected arm lowered its guard or body"
        (invalid_callback_calls = ["binder_or_scrutinee_probe"])

    val valid_callback_text =
      "match_case binder_or_scrutinee_probe { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | BinderAuditC(x, y) " ^
      "if binder_or_guard_probe \<Rightarrow> binder_or_body_probe, " ^
      "_ \<Rightarrow> binder_or_fallback_probe }"
    val (valid_callback_result, valid_callback_calls) =
      callback_trace valid_callback_text
    val _ =
      (case valid_callback_result of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)
    val _ =
      audit_assert "valid arm source expressions were not lowered once"
        (valid_callback_calls =
          ["binder_or_scrutinee_probe", "binder_or_guard_probe",
           "binder_or_body_probe", "binder_or_fallback_probe"])

    val valid_markup_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | BinderAuditC(x, y) " ^
      "if x < y \<Rightarrow> x, _ \<Rightarrow> 0 }"
    val valid_markup_start =
      Position.make0 140 14000 0 "" "" "or-pattern-valid-markup-audit"
    val (valid_markup_result, valid_markup) =
      capture_expression valid_markup_text valid_markup_start
    val _ =
      (case valid_markup_result of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)
    val x_positions =
      map (token_position valid_markup_text valid_markup_start "x")
        (0 upto 4)
    val y_positions =
      map (token_position valid_markup_text valid_markup_start "y")
        (0 upto 3)
    fun assert_shared name positions =
      let
        val definition = hd positions
        val references = tl positions
        val id = entity_id Markup.defN definition valid_markup
        val _ =
          audit_assert (name ^ " definition lost bound markup")
            (has_markup Markup.boundN definition valid_markup)
        val _ =
          List.app
            (fn position =>
              (audit_assert (name ^ " occurrence lost bound markup")
                 (has_markup Markup.boundN position valid_markup);
               audit_assert (name ^ " occurrence changed entity identity")
                 (entity_id Markup.refN position valid_markup = id)))
            references
        val _ =
          List.app
            (fn position =>
              audit_assert (name ^ " later alternative allocated a definition")
                (not
                  (has_entity_property Markup.defN
                    position valid_markup)))
            (tl positions)
      in () end
    val _ = assert_shared "x" x_positions
    val _ = assert_shared "y" y_positions

    val _ =
      ignore
        (checked
          ("match_case \<llangle>(Some (1 :: nat), " ^
           "(Some (2 :: nat), TNil))\<rrangle> { " ^
           "(Some(x), y) | (y, Some(x)) \<Rightarrow> x, _ \<Rightarrow> 0 }"))
    val _ =
      ignore
        (checked
          ("match \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
           "BinderAuditSliceA([x, ..]) | " ^
           "BinderAuditSliceB([.., x]) \<Rightarrow> x, _ \<Rightarrow> 0 }"))
  in
    val _ =
      writeln
        "Or-pattern binder diagnostics, ranges, precedence, markup, recovery, and shared-environment regressions passed"
  end
\<close>


section\<open> Standard code equations \<close>

urust_expr regression_code_literal
  \<open> 7_u32 \<close>

urust_expr regression_code_unit
  \<open> () \<close>

urust_expr regression_code_yield
  \<open> \<y>\<i>\<e>\<l>\<d> \<close>

urust_expr regression_code_primitive_log
  \<open> \<l>\<o>\<g> \<llangle>Info\<rrangle> \<llangle>[]\<rrangle> \<close>

urust_expr regression_code_log_data
  \<open> l\<llangle>True\<rrangle> \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun audit_assert message condition =
      if condition then ()
      else error ("parser code-equation audit: " ^ message)

    val generated =
      [\<^const_name>\<open>regression_code_literal\<close>,
       \<^const_name>\<open>regression_code_unit\<close>,
       \<^const_name>\<open>regression_code_yield\<close>,
       \<^const_name>\<open>regression_code_primitive_log\<close>,
       \<^const_name>\<open>regression_code_log_data\<close>]

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
      in
        audit_assert
          ("expected one default equation for " ^ quote constant)
          (length equations = 1);
        audit_assert
          ("default equation differs from the definition for " ^
            quote constant)
          (Thm.equiv_thm thy
            (the_single equations,
             Axclass.unoverload ctxt definition))
      end

    val _ = List.app check_generated generated
  in
    val _ = writeln "Parser-generated default code equations passed"
  end
\<close>


chapter\<open>Turbofish\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

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
         UE_Call
           (UC_Path
             (UR_Path
               ([Path_Segment
                  ("f", _, SOME (Generic_Args (arguments, _)))], _)),
            [], _) => arguments
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
         UE_Call
           (UC_Path
             (UR_Path
               ([Path_Segment
                  ("f", _,
                   SOME (Generic_Args
                     ([Generic_Arg (first_canonical, first_source),
                       Generic_Arg (second_canonical, second_source)],
                      generic_pos)))], _)),
            [], _) =>
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


chapter\<open>Term hook\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

section\<open> Experimental term-position parser hook \<close>

text\<open>
The reusable hook is defined by \<open>Micro_Rust_Parser_Impl.Parser_Term_Hook\<close>. This theory covers its
markup, contextual elaboration, binder hygiene, nesting, scoped conformance configuration, positioned
failures, marker erasure, and detached legacy reporting.
\<close>

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("term-hook markup normalization: " ^ message)

    val source_text = "\<mu>\<open> let _ = 1; True \<close>"
    val source_start =
      Position.make0 7 100 0 "" "urust-term-hook-markup"
        "urust-term-hook-markup"
    val source =
      Input.source false source_text
        (Position.range
          (source_start,
           Position.symbol_explode source_text source_start))
    fun capture enabled =
      let
        val captured =
          Synchronized.var
            ("urust_term_hook_markup_" ^
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

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun count_entity kind position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              has_position properties position)
          markup)

    fun find_from needle offset =
      if offset + size needle > size source_text then
        error ("term-hook markup normalization: missing " ^ quote needle)
      else if String.substring (source_text, offset, size needle) = needle
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
      Position.symbol_explode "\<mu>" source_start
    val cartouche_pos =
      Position.range_position
        (Position.range
          (cartouche_start,
           Position.symbol_explode
             "\<open> let _ = 1; True \<close>" cartouche_start))
    val (_, underscore_pos) =
      token_position "_" 0
    val (numeral_offset, numeral_pos) =
      token_position "1" 0
    val (_, constant_pos) =
      token_position "True" (numeral_offset + 1)

    val _ =
      assert "inner-syntax cartouche classification disappeared"
        (has_markup Markup.inner_cartoucheN cartouche_pos)
    val _ =
      assert "ordinary cartouche normalization is absent or has the wrong range"
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
      assert "detached legacy parsing duplicated wildcard typing reports"
        (count_markup Markup.typingN underscore_pos enabled_markup =
          count_markup Markup.typingN underscore_pos disabled_markup)
    val _ =
      assert "detached legacy parsing duplicated constant reports"
        (count_entity Markup.constantN constant_pos enabled_markup =
          count_entity Markup.constantN constant_pos disabled_markup)
  in
    val _ = ()
  end
\<close>

lemma closed_conformance:
  "\<mu>\<open> 1 + 2 \<close> = \<lbrakk> 1 + 2 \<rbrakk>"
  by (rule refl)

lemma expected_result_type:
  "(\<mu>\<open> 0 \<close> ::
      ('s, nat, 'r, 'abort, 'input, 'output) expression) =
   (\<lbrakk> 0 \<rbrakk> ::
      ('s, nat, 'r, 'abort, 'input, 'output) expression)"
  by (rule refl)

lemma outer_lambda_plain_identifier:
  "(\<lambda>x :: nat. \<mu>\<open> x \<close>) =
   (\<lambda>x :: nat. \<lbrakk> x \<rbrakk>)"
  by (rule refl)

lemma outer_lambda_antiquotation:
  "(\<lambda>x :: nat. \<mu>\<open> \<llangle>x\<rrangle> \<close>) =
   (\<lambda>x :: nat. \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>)"
  by (rule refl)

lemma outer_let_antiquotation:
  "(\<lambda>x :: nat. let y = x in \<mu>\<open> \<llangle>y\<rrangle> \<close>) =
   (\<lambda>x :: nat. let y = x in \<lbrakk> \<llangle>y\<rrangle> \<rbrakk>)"
  by (rule refl)

lemma outer_case_antiquotation:
  "(\<lambda>x :: nat option.
      case x of
        Some y \<Rightarrow> \<mu>\<open> \<llangle>y\<rrangle> \<close>
      | None \<Rightarrow> \<mu>\<open> 0 \<close>) =
   (\<lambda>x :: nat option.
      case x of
        Some y \<Rightarrow> \<lbrakk> \<llangle>y\<rrangle> \<rbrakk>
      | None \<Rightarrow> \<lbrakk> 0 \<rbrakk>)"
  by (rule refl)

lemma parser_local_binder:
  "\<mu>\<open> let x = 1; \<llangle>x\<rrangle> \<close> =
   \<lbrakk> let x = 1; \<llangle>x\<rrangle> \<rbrakk>"
  by (rule refl)

lemma nested_hol_shadowing_antiquotation:
  "(\<lambda>x :: nat.
      \<mu>\<open>
        let x = \<llangle>x\<rrangle>;
        \<llangle>(\<lambda>x :: nat. x) x\<rrangle>
      \<close>) =
   (\<lambda>x :: nat.
      \<lbrakk>
        let x = \<llangle>x\<rrangle>;
        \<llangle>(\<lambda>x :: nat. x) x\<rrangle>
      \<rbrakk>)"
  by (rule refl)

context
begin

private definition private_term_hook_value :: nat where
  \<open>private_term_hook_value = 7\<close>

lemma private_constant_not_captured:
  "(\<lambda>private_term_hook_value :: nat.
      \<mu>\<open> \<llangle>CONST private_term_hook_value\<rrangle> \<close>) =
   (\<lambda>private_term_hook_value :: nat.
      \<lbrakk> \<llangle>CONST private_term_hook_value\<rrangle> \<rbrakk>)"
  by (rule refl)

end

context
  fixes x :: nat
begin

lemma fixed_context_antiquotation:
  "\<mu>\<open> \<llangle>x\<rrangle> \<close> = \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>"
  by (rule refl)

end

lemma nested_term_hook:
  "\<mu>\<open> \<epsilon>\<open> \<mu>\<open> 1 \<close> \<close> \<close> =
   \<lbrakk> \<epsilon>\<open> \<lbrakk> 1 \<rbrakk> \<close> \<rbrakk>"
  by (rule refl)


section\<open> Scoped delayed conformance \<close>

lemma disabled_accepts_parser_only_source:
  "\<mu>\<open>
      // accepted only by the dedicated parser
      ()
    \<close> =
   \<lbrakk> () \<rbrakk>"
  by (rule refl)

declare [[urust_term_hook_conformance_check = true]]

term
  "(\<mu>\<open> 0 \<close> ::
    ('s, nat, 'r, 'abort, 'input, 'output) expression)"

declare [[urust_term_hook_conformance_check = false]]

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("term-hook delayed conformance: " ^ message)

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
             ("term-hook delayed conformance: " ^ label ^
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
             ("term-hook delayed conformance: " ^ label ^
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
        "term-hook-shared-source"
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
             "term-hook delayed conformance: missing marker head")
    val position_payload =
      (case marker_arguments of
         [_, _, payload] => payload
       | _ =>
           error
             "term-hook delayed conformance: malformed generated marker")

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
            (Abs ("x", \<^typ>\<open>nat\<close>, \<^term>\<open>True\<close>),
             Abs ("x", \<^typ>\<open>nat\<close>, \<^term>\<open>True\<close>)),
          HOLogic.mk_eq
            (Abs ("x", \<^typ>\<open>bool\<close>, \<^term>\<open>True\<close>),
             Abs ("x", \<^typ>\<open>bool\<close>, \<^term>\<open>True\<close>)),
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
          Syntax.check_term enabled_ctxt
            malformed_marker)

    val rejected_text =
      "\<mu>\<open> () // legacy rejects this source \<close>"
    val rejected_start =
      Position.make0 13 700 0 "" ""
        "term-hook-legacy-rejection"
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
  in
    val _ = ()
  end
\<close>


chapter\<open>Logging\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

declare [[urust_conformance_check = true]]

text\<open>
This suite is evaluated after \<open>Parser_Tests_Expr\<close>, so the logging import does not affect that theory's built-in macro coverage.
The \<open>StdLib_Logging\<close> import supplies the legacy frontend syntax used as the
oracle for \<open>l\<llangle>...\<rrangle>\<close>, and it also registers \<open>fatal!\<close>,
\<open>info!\<close>, and the other logger calls. In particular, registered
\<open>fatal!\<close> takes precedence over the built-in macro in this context.
Keeping the import isolated preserves the main suite's built-in \<open>fatal!\<close>
coverage.
\<close>

section\<open> Logging-data expressions \<close>

urust_expr log_data_one_string
  \<open> l\<llangle>"one"\<rrangle> \<close>

context
  fixes context_value :: nat
begin

urust_expr log_data_one_identifier
  \<open> l\<llangle>context_value\<rrangle> \<close>

urust_expr log_data_mixed
  \<open> l\<llangle>"value = ", context_value, "."\<rrangle> \<close>

urust_expr log_data_repeated_identifier
  \<open> l\<llangle>context_value, context_value, context_value\<rrangle> \<close>

end

urust_expr log_data_long
  \<open>
    l\<llangle>
      "a", True, "b", False, "c", True,
      "d", False, "e", True, "f", False
    \<rrangle>
  \<close>

urust_expr log_data_empty_string
  \<open> l\<llangle>""\<rrangle> \<close>

urust_expr log_data_multiline
  \<open>
    l\<llangle>
      "first",
      True,
      "second",
      False
    \<rrangle>
  \<close>

subsection\<open> String-token boundaries \<close>

urust_expr log_data_escaped_quote
  \<open> l\<llangle>"say: \"hello\""\<rrangle> \<close>

urust_expr log_data_escaped_backslash
  \<open> l\<llangle>"left\\right"\<rrangle> \<close>

urust_expr log_data_comma_in_string
  \<open> l\<llangle>"left, right"\<rrangle> \<close>

urust_expr log_data_comment_text
  \<open> l\<llangle>"https://example.invalid//path"\<rrangle> \<close>

urust_expr log_data_keyword_text
  \<open> l\<llangle>"true false let const return log yield l"\<rrangle> \<close>

subsection\<open> Identifier resolution and lexical scope \<close>

definition logging_collision :: nat
  where \<open> logging_collision = 17 \<close>

definition logging_notation_target :: nat
  where \<open> logging_notation_target = 99 \<close>

micro_rust_notation (literal) logging_notation_target ("logging_collision")

urust_expr log_data_hol_constant
  \<open> l\<llangle>logging_collision\<rrangle> \<close>

urust_expr log_data_boolean_constant
  \<open> l\<llangle>True, False\<rrangle> \<close>

urust_expr log_data_local
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    l\<llangle>"value = ", value\<rrangle>
  \<close>

urust_expr log_data_nested_shadowing
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    let outer = l\<llangle>value\<rrangle>;
    let value = \<llangle>7 :: nat\<rrangle>;
    (outer, l\<llangle>value\<rrangle>)
  \<close>

urust_expr log_data_constant_named_binder
  \<open>
    let Some = \<llangle>11 :: nat\<rrangle>;
    l\<llangle>Some, Some\<rrangle>
  \<close>

subsection\<open> Registered logging calls \<close>

urust_expr registered_fatal_logger
  \<open> fatal!(l\<llangle>"fatal", True\<rrangle>) \<close>

urust_expr registered_info_logger
  \<open> info!(l\<llangle>"info", True\<rrangle>) \<close>

urust_expr registered_error_logger
  \<open> error!(l\<llangle>"error", True\<rrangle>) \<close>

urust_expr registered_debug_logger
  \<open> debug!(l\<llangle>"debug", False\<rrangle>) \<close>

urust_expr registered_trace_logger
  \<open> trace!(l\<llangle>"trace", True\<rrangle>) \<close>

text\<open>
The first row specifically checks that the adjacent registered \<open>fatal!\<close> call wins over the
built-in message macro in this import context. The main conformance theory intentionally does not
import \<open>StdLib_Logging\<close>, so its built-in \<open>fatal!\<close> coverage remains unchanged.
\<close>


chapter\<open>Negative logging\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

section\<open> Malformed logging-data expressions \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>, True\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True,\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True,, False\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True False\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>1\<rrangle> \<close>
  \<open> unexpected input "1" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>\<llangle>True\<rrangle>\<rrangle> \<close>
  \<open> unexpected input \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>Foo::Bar\<rrangle> \<close>
  \<open> unexpected input ":" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True()\<rrangle> \<close>
  \<open> unexpected input "(" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True + False\<rrangle> \<close>
  \<open> unexpected input "+" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>l\<llangle>True\<rrangle>\<rrangle> \<close>
  \<open> unexpected input \<close>

urust_expr_rejects fidelity
  \<open> l \<llangle>True\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<rrangle> \<close>
  \<open> unexpected input \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>"unterminated \<close>
  \<open> malformed or unterminated string literal \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>"text", True \<close>
  \<open> unterminated log data \<close>


chapter\<open>Yield and logging audits\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

section\<open> Yield and logging structural audit \<close>

text\<open>
This theory audits parser properties that equation-based conformance tests cannot expose directly:
the yield, primitive-log, and log-data ASTs and source spans; exact lowering shape; local-first
identifier resolution; editor markup; positioned diagnostics; and lexer/parser recovery after
malformed input.
\<close>

definition yield_logging_audit_collision :: nat
  where \<open> yield_logging_audit_collision = 17 \<close>

definition yield_logging_audit_notation_target :: nat
  where \<open> yield_logging_audit_notation_target = 99 \<close>

micro_rust_notation (literal) yield_logging_audit_notation_target
  ("yield_logging_audit_collision")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("yield/logging regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "yield/logging regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("yield/logging regression audit: missing " ^ quote needle)
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

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun dest_application expected term =
      (case Term.strip_comb (Term_Position.strip_positions term) of
         (Const (name, _), arguments) =>
           if name = expected then arguments
           else
             error
               ("yield/logging regression audit: expected " ^ quote expected ^
                ", found " ^ quote name)
       | _ =>
           error
             ("yield/logging regression audit: expected application of " ^
              quote expected))

    fun append_entries term =
      (case Term.strip_comb (Term_Position.strip_positions term) of
         (Const (name, _), [first, rest]) =>
           if name = \<^const_name>\<open>List.append\<close>
           then first :: append_entries rest
           else [term]
       | _ => [term])

    val yield_text = "\<y>\<i>\<e>\<l>\<d>"
    val yield_start =
      Position.make0 11 100 0 "" "" "yield-logging-yield-ast"
    val yield_source =
      Parser_Lex_Util.positioned_content_source yield_text yield_start
    val yield_span =
      Position.range_position
        (yield_start, Position.symbol_explode yield_text yield_start)
    val _ =
      (case parse yield_source of
         UE_Yield pos =>
           audit_assert "yield AST span changed"
             (same_range pos yield_span)
       | _ => error "yield/logging regression audit: yield AST changed")

    val primitive_text =
      "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 1]\<rrangle>"
    val primitive_start =
      Position.make0 21 200 0 "" "" "yield-logging-log-ast"
    val primitive_stop =
      Position.symbol_explode primitive_text primitive_start
    val primitive_source =
      Parser_Lex_Util.positioned_content_source
        primitive_text primitive_start
    val _ =
      (case parse primitive_source of
         UE_Log (priority, data, pos) =>
           (audit_assert "primitive-log priority source changed"
              (Symbol.trim_blanks (Input.string_of priority) = "Error");
            audit_assert "primitive-log data source changed"
              (Symbol.trim_blanks (Input.string_of data) = "[LogNat 1]");
            audit_assert "primitive-log span changed"
              (Position.offset_of pos =
                 Position.offset_of primitive_start andalso
               Position.end_offset_of pos =
                 Position.offset_of primitive_stop))
       | _ => error "yield/logging regression audit: primitive-log AST changed")

    val data_text =
      "l\<llangle>\"left, // \<rrangle> text\", True\<rrangle>"
    val data_start =
      Position.make0 31 300 0 "" "" "yield-logging-data-ast"
    val data_stop =
      Position.symbol_explode data_text data_start
    val data_source =
      Parser_Lex_Util.positioned_content_source data_text data_start
    val (string_raw, string_pos, identifier_pos, data_pos) =
      (case parse data_source of
         UE_LogData
           ([LDE_String (raw, first_pos),
             LDE_Identifier ("True", second_pos)],
            pos) =>
           (raw, first_pos, second_pos, pos)
       | _ => error "yield/logging regression audit: log-data AST changed")
    val _ =
      audit_assert "log-data string terminated at embedded syntax"
        (string_raw = "\"left, // \<rrangle> text\"")
    val _ =
      audit_assert "log-data span changed"
        (Position.offset_of data_pos = Position.offset_of data_start andalso
         Position.end_offset_of data_pos = Position.offset_of data_stop)
    val (_, expected_string_pos) =
      token_position data_text data_start
        "\"left, // \<rrangle> text\"" 0
    val (_, expected_identifier_pos) =
      token_position data_text data_start "True" 0
    val _ =
      audit_assert "log-data entry spans changed"
        (same_range string_pos expected_string_pos andalso
         same_range identifier_pos expected_identifier_pos)

    val yield_term = checked yield_text
    val _ =
      audit_assert "yield no longer lowers directly to pause"
        (case Term_Position.strip_positions yield_term of
           Const (name, _) => name = \<^const_name>\<open>pause\<close>
         | _ => false)

    val primitive_term = checked primitive_text
    val primitive_arguments =
      dest_application \<^const_name>\<open>log\<close> primitive_term
    val _ =
      audit_assert "primitive log is not a direct two-argument log"
        (length primitive_arguments = 2)
    val _ =
      audit_assert "primitive-log operands gained literal wrappers"
        (count_constant \<^const_name>\<open>literal\<close> primitive_term = 0)

    val singleton_string = checked "l\<llangle>\"only\"\<rrangle>"
    val singleton_string_value =
       (case dest_application \<^const_name>\<open>literal\<close>
          singleton_string of
         [value] => value
       | _ => error "yield/logging regression audit: string literal arity changed")
    val _ =
      audit_assert "singleton string gained List.append"
        (count_constant \<^const_name>\<open>List.append\<close>
           singleton_string = 0)
    val singleton_elements =
      dest_application \<^const_name>\<open>List.Cons\<close>
        singleton_string_value
    val _ =
      audit_assert "singleton string lost its LogString list"
        (case singleton_elements of
           [head, tail] =>
             length
               (dest_application \<^const_name>\<open>LogString\<close>
                 head) = 1 andalso
             (case Term_Position.strip_positions tail of
                Const (name, _) =>
                  name = \<^const_name>\<open>List.Nil\<close>
              | _ => false)
         | _ => false)

    val singleton_identifier = checked "l\<llangle>True\<rrangle>"
    val _ =
      audit_assert "singleton identifier gained List.append"
        (count_constant \<^const_name>\<open>List.append\<close>
           singleton_identifier = 0)
    val _ =
      audit_assert "singleton identifier did not lower once through generate_debug"
        (count_constant \<^const_name>\<open>generate_debug\<close>
           singleton_identifier = 1)

    val mixed =
      checked "l\<llangle>\"a\", True, \"b\", False\<rrangle>"
    val mixed_value =
      (case dest_application \<^const_name>\<open>literal\<close> mixed of
         [value] => value
       | _ => error "yield/logging regression audit: mixed literal arity changed")
    val source_entries = append_entries mixed_value
    val _ =
      audit_assert "log data did not use a right-associated append tree"
        (length source_entries = 4 andalso
         count_constant \<^const_name>\<open>List.append\<close> mixed = 3)
    val _ =
      (case source_entries of
         [first, second, third, fourth] =>
           (audit_assert "first source entry changed"
              (count_constant \<^const_name>\<open>LogString\<close> first = 1);
            audit_assert "second source entry changed"
              (count_constant \<^const_name>\<open>generate_debug\<close> second = 1 andalso
               count_constant \<^const_name>\<open>True\<close> second = 1);
            audit_assert "third source entry changed"
              (count_constant \<^const_name>\<open>LogString\<close> third = 1);
            audit_assert "fourth source entry changed"
              (count_constant \<^const_name>\<open>generate_debug\<close> fourth = 1 andalso
               count_constant \<^const_name>\<open>False\<close> fourth = 1))
       | _ => error "yield/logging regression audit: mixed source order changed")
    val _ =
      audit_assert "log data no longer has exactly one literal wrapper"
        (count_constant \<^const_name>\<open>literal\<close> mixed = 1)

    val collision = checked "l\<llangle>yield_logging_audit_collision\<rrangle>"
    val _ =
      audit_assert "log-data identifier used micro_rust_notation dispatch"
        (count_constant \<^const_name>\<open>yield_logging_audit_collision\<close>
           collision = 1 andalso
         count_constant \<^const_name>\<open>yield_logging_audit_notation_target\<close>
           collision = 0 andalso
         count_constant \<^const_name>\<open>urust_dispatch\<close>
           collision = 0)

    val shadowed =
      checked
        ("let yield_logging_audit_collision = \<llangle>5 :: nat\<rrangle>; " ^
         "l\<llangle>yield_logging_audit_collision, yield_logging_audit_collision\<rrangle>")
    val _ =
      audit_assert "lexical log-data identifier did not shadow the HOL constant"
        (count_constant \<^const_name>\<open>yield_logging_audit_collision\<close>
           shadowed = 0 andalso
         count_constant \<^const_name>\<open>yield_logging_audit_notation_target\<close>
           shadowed = 0 andalso
         count_constant \<^const_name>\<open>generate_debug\<close>
           shadowed = 2)

    val markup_text =
      "let local = \<llangle>True\<rrangle>; " ^
      "{ \<y>\<i>\<e>\<l>\<d>; " ^
      "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[]\<rrangle>; " ^
      "l\<llangle>\"text, //\", local, True\<rrangle> }"
    val markup_start =
      Position.make0 41 400 0 "" "" "yield-logging-markup"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        markup_text markup_start
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
                  (Parser_Test_Elaboration.expression ctxt markup_source)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)
    fun has_markup name pos =
      exists
        (fn (candidate, properties) =>
          candidate = name andalso has_position properties pos)
        markup
    fun has_any_entity pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun entity_id property pos =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties pos
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ => error "yield/logging regression audit: binder entity markup changed")
      end

    val (local_def_raw, local_definition) =
      token_position markup_text markup_start "local" 0
    val (yield_raw, yield_keyword) =
      token_position markup_text markup_start yield_text 0
    val (log_raw, log_keyword) =
      token_position markup_text markup_start
        "\<l>\<o>\<g>" yield_raw
    val (data_open_raw, data_l) =
      token_position markup_text markup_start
        "l\<llangle>" log_raw
    val data_open_symbol =
      Position.range_position
        (Position.symbol_explode "l" data_l,
         Position.symbol_explode "l\<llangle>" data_l)
    val data_l_symbol =
      Position.range_position
        (data_l, Position.symbol_explode "l" data_l)
    val (string_token_raw, string_token_pos) =
      token_position markup_text markup_start "\"text, //\"" data_open_raw
    val (first_separator_raw, first_separator_pos) =
      token_position markup_text markup_start ","
        (string_token_raw + size "\"text, //\"")
    val (local_ref_raw, local_reference) =
      token_position markup_text markup_start "local"
        (local_def_raw + size "local")
    val (_, second_separator_pos) =
      token_position markup_text markup_start ","
        (local_ref_raw + size "local")
    val (true_ref_raw, true_reference) =
      token_position markup_text markup_start "True"
        (local_ref_raw + size "local")
    val (_, data_close_pos) =
      token_position markup_text markup_start "\<rrangle>" true_ref_raw
    val (_, internal_comma_pos) =
      token_position markup_text markup_start "," string_token_raw

    val _ =
      List.app
        (fn (label, pos) =>
          (audit_assert (label ^ " lost role markup")
             (has_markup Markup.keyword1N pos);
           audit_assert (label ^ " lost typing markup")
             (has_markup Markup.typingN pos);
           audit_assert (label ^ " received identifier entity markup")
             (not (has_any_entity pos))))
        [("yield keyword", yield_keyword),
         ("log keyword", log_keyword),
         ("log-data l", data_l_symbol)]
    val _ =
      List.app
        (fn (label, pos) =>
          (audit_assert (label ^ " lost delimiter markup")
             (has_markup Markup.delimiterN pos);
           audit_assert (label ^ " lost typing markup")
             (has_markup Markup.typingN pos)))
        [("log-data opener", data_open_symbol),
         ("log-data closer", data_close_pos),
         ("first separator", first_separator_pos),
         ("second separator", second_separator_pos)]
    val _ =
      (audit_assert "log-data string lost inner-string markup"
         (has_markup Markup.inner_stringN string_token_pos);
       audit_assert "log-data string lost typing markup"
         (has_markup Markup.typingN string_token_pos);
       audit_assert "comma inside a string received delimiter markup"
         (not (has_markup Markup.delimiterN internal_comma_pos)))
    val _ =
      (audit_assert "local log-data reference lost bound markup"
         (has_markup Markup.boundN local_reference);
       audit_assert "local log-data reference lost typing markup"
         (has_markup Markup.typingN local_reference);
       audit_assert "local log-data reference stopped targeting its binder"
         (entity_id Markup.defN local_definition =
          entity_id Markup.refN local_reference);
       audit_assert "ordinary HOL log-data identifier lost typing markup"
         (has_markup Markup.typingN true_reference);
       audit_assert "ordinary HOL log-data identifier lost constant markup"
         (has_entity_markup Markup.constantN true_reference))

    fun expect_failure operation source =
      (case Exn.result operation source of
         Exn.Res _ =>
           error
             ("yield/logging regression audit: expected rejection of " ^
              quote source)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())

    fun assert_recovered () =
      (case parse_text yield_text of
         UE_Yield _ => ()
       | _ => error "yield/logging regression audit: yield did not recover";
       case parse_text primitive_text of
         UE_Log _ => ()
       | _ => error "yield/logging regression audit: primitive log did not recover";
       case parse_text "l\<llangle>\"ok\", True\<rrangle>" of
         UE_LogData _ => ()
       | _ => error "yield/logging regression audit: log data did not recover";
       ignore (checked yield_text);
       ignore (checked primitive_text);
       ignore (checked "l\<llangle>True\<rrangle>"))

    val malformed =
      ["l\<llangle>\<rrangle>",
       "l\<llangle>, True\<rrangle>",
       "l\<llangle>True,\<rrangle>",
       "l\<llangle>True,, False\<rrangle>",
       "l\<llangle>True False\<rrangle>",
       "l\<llangle>1\<rrangle>",
       "l\<llangle>\<llangle>True\<rrangle>\<rrangle>",
       "l\<llangle>Foo::Bar\<rrangle>",
       "l\<llangle>True()\<rrangle>",
       "l\<llangle>True + False\<rrangle>",
       "l\<llangle>l\<llangle>True\<rrangle>\<rrangle>",
       "l \<llangle>True\<rrangle>",
       "\<rrangle>",
       "l\<llangle>\"unterminated",
       "l\<llangle>\"text\", True",
       "\<l>\<o>\<g>",
       "\<l>\<o>\<g> \<llangle>Error\<rrangle>",
       "\<l>\<o>\<g> \<epsilon>\<open>literal Error\<close> \<llangle>[]\<rrangle>",
       "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[]\<rrangle> \<llangle>[]\<rrangle>",
       "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[]"]
    val _ =
      List.app
        (fn source =>
          (expect_failure
             (fn text => parse_text text) source;
           assert_recovered ()))
        malformed

    fun failure_message source =
      (case Exn.result
         (fn () => parse source) () of
         Exn.Res _ =>
           error "yield/logging regression audit: positioned malformed source parsed"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else XML.content_of (YXML.parse_body (Runtime.exn_message exn)))

    val opener_source =
      Parser_Lex_Util.positioned_content_source
        "l\<llangle>\n\"text\", True"
        (Position.make0 101 1000 0 "" "" "yield-logging-opener-error")
    val _ =
      audit_assert "unterminated log data moved away from its opener"
        (String.isSubstring "unterminated log data"
           (failure_message opener_source) andalso
         String.isSubstring "line 101"
           (failure_message opener_source))

    val grammar_source =
      Parser_Lex_Util.positioned_content_source
        "l\<llangle>\n, True\<rrangle>"
        (Position.make0 201 2000 0 "" "" "yield-logging-grammar-error")
    val _ =
      audit_assert "log-data grammar error moved away from the bad separator"
        (String.isSubstring "line 202"
           (failure_message grammar_source))

    val string_source =
      Parser_Lex_Util.positioned_content_source
        "l\<llangle>\n\"unterminated"
        (Position.make0 301 3000 0 "" "" "yield-logging-string-error")
    val _ =
      audit_assert "log-data string error moved away from its quote"
        (String.isSubstring "malformed or unterminated string literal"
           (failure_message string_source) andalso
         String.isSubstring "line 302"
           (failure_message string_source))
  in
    val _ =
      writeln
        "Yield/log AST, term-shape, scope, markup, diagnostics, and recovery regressions passed"
  end
\<close>


chapter\<open>Isabelle comments\<close>

declare [[urust_conformance_check = false]]
declare [[urust_verbose = 0]]
declare [[urust_abbrev = false]]
declare [[urust_term_hook_conformance_check = false]]

declare [[urust_conformance_check = true]]

section\<open> Isabelle formal comments \<close>

text\<open>
Formal comments are layout for the dedicated parser. Isabelle's command-span processing remains
responsible for checking document antiquotations and producing formal-comment markup.
\<close>

subsection\<open> Expression and function parity \<close>

urust_expr isabelle_comment_standalone
  \<open>
    \<comment> \<open>Standalone comment before the expression.\<close>
    ()
  \<close>

urust_expr isabelle_comment_inline
  \<open>
    1_u64\<comment>\<open>Comment between operands: + - * / { } [ ] ( ) , ; :: =>.\<close>+2_u64
  \<close>

urust_expr isabelle_comment_trailing
  \<open>
    ();
    () \<comment> \<open>Trailing comment after the complete expression.\<close>
  \<close>

urust_expr isabelle_comment_multiline_nested
  \<open>
    \<comment> \<open>
      Outer document text with \<open>nested { grammar } punctuation\<close> and
      \<open>another \<open>deeply nested\<close> cartouche\<close>.
      Escaped Isabelle symbols remain document text: \<alpha> \<Rightarrow> \<forall>.
    \<close>
    if true {
      \<comment> \<open>Then branch.\<close>
      3_u64
    } else {
      4_u64
    }
  \<close>

urust_expr isabelle_comment_document_antiquotations
  \<open>
    \<comment> \<open>
      Modern controls: \<^term>\<open>True\<close>, \<^const>\<open>False\<close>, and
      \<^verbatim>\<open>{ grammar punctuation, :: => }\<close>.
      Legacy antiquotations: @{term True} and
      @{verbatim \<open>[legacy punctuation; + - *]\<close>}.
    \<close>
    ()
  \<close>

declare [[urust_verbose = 1]]

urust_fn isabelle_comment_function ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    \<comment> \<open>Function-body comment with \<^term>\<open>item\<close> treated as document text.\<close>
    item \<comment> \<open>Inline function-body comment.\<close>
  \<close>

declare [[urust_verbose = 0]]


subsection\<open> Specialized lexer contexts \<close>

definition isabelle_comment_generic ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>isabelle_comment_generic parameter \<equiv>
      lift_fun1 (\<lambda>argument. parameter + argument)\<close>

micro_rust_notation (call) isabelle_comment_generic ("Comment::generic")

urust_expr isabelle_comment_generic_layout
  \<open>
    Comment::generic::<
      1 \<comment> \<open>Generic-state layout with \<open>> , + ::\<close>.\<close> + 2
    >(3)
  \<close>

urust_expr isabelle_comment_log_data_layout
  \<open>
    l\<llangle>
      \<comment> \<open>Log-data layout before the first entry.\<close>
      "value = ",
      \<comment> \<open>Log-data layout after a separator.\<close>
      True
    \<rrangle>
  \<close>


subsection\<open> Literal comment-shaped text \<close>

text\<open>
The structural audit below feeds complete comment-shaped text directly to the lexer and verifies that
quoted strings and both uRust antiquotation states retain it byte-for-byte.
\<close>


subsection\<open> Structural, markup, diagnostic, and recovery audit \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Isabelle-comment regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "Isabelle-comment regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("Isabelle-comment regression audit: missing " ^ quote needle)
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

    fun capture_reports action =
      let
        val captured =
          Synchronized.var
            "isabelle_comment_parser_test_reports" ([] : string list)
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

    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)

    fun has_markup markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup

    fun has_entity_markup markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup

    fun formal_comment body =
      Symbol.comment ^ " " ^ Symbol.open_ ^ body ^ Symbol.close

    val physical_lambda =
      Byte.bytesToString
        (Word8Vector.fromList [0wxCE, 0wxBB])
    val structural_text =
      "1_u64 " ^
      formal_comment
        ("physical Unicode " ^ physical_lambda ^
         "; nested " ^ Symbol.open_ ^ "{ [ ( + => :: ) ] }" ^
         Symbol.close ^ "; escaped \<alpha>") ^
      " + 2_u64"
    val structural_start =
      Position.make0 41 400 0 "" "" "isabelle-comment-structure"
    val structural_source =
      Parser_Lex_Util.positioned_content_source
        structural_text structural_start
    val (left_raw, left_pos) =
      token_position structural_text structural_start "1_u64" 0
    val (comment_raw, _) =
      token_position structural_text structural_start Symbol.comment left_raw
    val (inner_plus_raw, inner_plus_pos) =
      token_position structural_text structural_start "+"
        comment_raw
    val (outer_plus_raw, outer_plus_pos) =
      token_position structural_text structural_start "+"
        (inner_plus_raw + 1)
    val (_, right_pos) =
      token_position structural_text structural_start "2_u64"
        outer_plus_raw

    val structural_ast = parse structural_source
    val _ =
      (case structural_ast of
         UE_Bin
           (Add,
            UE_Literal (LP_Integer ("1_u64", actual_left)),
            UE_Literal (LP_Integer ("2_u64", actual_right)),
            actual_operator) =>
           (audit_assert "comment created or changed an AST node"
              (same_range actual_left left_pos andalso
               same_range actual_right right_pos);
            audit_assert "operator position moved across the comment"
              (same_range actual_operator outer_plus_pos))
       | _ =>
           error "Isabelle-comment regression audit: expression AST changed")

    val comment_free_term = checked "1_u64 + 2_u64"
    val commented_term =
      Parser_Test_Elaboration.expression ctxt structural_source
    val _ =
      audit_assert "formal comment changed the checked term"
        (Term.aconv
          (Term_Position.strip_positions comment_free_term,
           Term_Position.strip_positions commented_term))

    val (_, parser_markup) =
      capture_reports
        (fn () =>
          ignore
            (Parser_Test_Elaboration.expression ctxt structural_source))
    val _ =
      (audit_assert "left numeral lost markup"
         (has_markup parser_markup Markup.numeralN left_pos);
       audit_assert "operator after comment lost markup"
         (has_markup parser_markup Markup.operatorN outer_plus_pos);
       audit_assert "right numeral lost markup"
         (has_markup parser_markup Markup.numeralN right_pos);
       audit_assert "comment content received uRust operator markup"
         (not (has_markup parser_markup Markup.operatorN inner_plus_pos)))

    val document_body =
      "Modern \<^term>\<open>True\<close> and " ^
      "\<^const>\<open>False\<close>; legacy @{term True}; " ^
      "\<^verbatim>\<open>modern text\<close>; " ^
      "@{verbatim \<open>legacy text\<close>}."
    val document_text =
      formal_comment document_body
    val document_start =
      Position.make0 61 600 0 "" "" "isabelle-comment-document"
    val document_source =
      Parser_Lex_Util.positioned_content_source
        document_text document_start
    val (body_raw, body_pos) =
      token_position document_text document_start
        (Symbol.open_ ^ "Modern") 0
    val body_stop =
      Position.symbol_explode
        (String.extract (document_text, body_raw, NONE))
        (Position.no_range_position body_pos)
    val full_body_pos =
      Position.range_position
        (Position.no_range_position body_pos, body_stop)
    val (modern_true_raw, modern_true_pos) =
      token_position document_text document_start "True" body_raw
    val (false_raw, false_pos) =
      token_position document_text document_start "False"
        modern_true_raw
    val (_, legacy_true_pos) =
      token_position document_text document_start "True" false_raw
    val (_, document_markup) =
      capture_reports
        (fn () =>
          Document_Output.check_comments ctxt
            (Input.source_explode document_source))
    val _ =
      (audit_assert "Isabelle checker did not mark the formal-comment cartouche"
         (has_markup document_markup Markup.cartoucheN full_body_pos);
       audit_assert "modern term antiquotation lost constant markup"
         (has_entity_markup document_markup Markup.constantN modern_true_pos);
       audit_assert "modern const antiquotation lost constant markup"
         (has_entity_markup document_markup Markup.constantN false_pos);
       audit_assert "legacy term antiquotation lost constant markup"
         (has_entity_markup document_markup Markup.constantN legacy_true_pos))

    val string_text =
      "\"" ^ formal_comment "string literal" ^ "\""
    val value_aq_text =
      "\<llangle>''" ^ formal_comment "value literal" ^ "''\<rrangle>"
    val expression_aq_text =
      "\<epsilon>\<open>\<up>(''" ^
      formal_comment "expression literal" ^
      "'')\<close>"
    val _ =
      (case parse_text string_text of
         UE_Literal (LP_String (raw, _)) =>
           audit_assert "comment-shaped string text was consumed"
             (raw = string_text)
       | _ =>
           error "Isabelle-comment regression audit: string AST changed")
    val _ =
      (case parse_text value_aq_text of
         UE_Literal (LP_ValAntiq source) =>
           audit_assert "comment-shaped value antiquotation text was consumed"
             (Input.string_of source =
               "''" ^ formal_comment "value literal" ^ "''")
       | _ =>
           error
             "Isabelle-comment regression audit: value antiquotation AST changed")
    val _ =
      (case parse_text expression_aq_text of
         UE_ExprAntiq source =>
           audit_assert "comment-shaped expression antiquotation text was consumed"
             (Input.string_of source =
               "\<up>(''" ^ formal_comment "expression literal" ^ "'')")
       | _ =>
           error
             "Isabelle-comment regression audit: expression antiquotation AST changed")

    fun failure_message text start =
      (case Exn.result
          (fn () =>
            parse
              (Parser_Lex_Util.positioned_content_source text start)) () of
         Exn.Res _ =>
           error
             ("Isabelle-comment regression audit: malformed source parsed: " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else XML.content_of (YXML.parse_body (Runtime.exn_message exn)))

    fun recover_initial () =
      (case parse_text "()" of
         UE_Unit _ => ()
       | _ =>
           error "Isabelle-comment regression audit: initial state did not recover")

    fun recover_generic () =
      (case parse_text "Comment::generic::<1>(2)" of
         UE_Call _ => ()
       | _ =>
           error "Isabelle-comment regression audit: generic state did not recover")

    fun recover_log_data () =
      (case parse_text "l\<llangle>\"ok\", True\<rrangle>" of
         UE_LogData _ => ()
       | _ =>
           error "Isabelle-comment regression audit: log-data state did not recover")

    fun expect_positioned_failure
        label text start expected expected_line recover =
      let
        val message = failure_message text start
        val _ =
          audit_assert (label ^ " diagnostic changed")
            (String.isSubstring expected message)
        val _ =
          audit_assert (label ^ " diagnostic moved away from the comment opener")
            (String.isSubstring
              ("line " ^ string_of_int expected_line) message)
        val _ = recover ()
      in () end

    val _ =
      expect_positioned_failure
        "initial missing opener"
        ("\n" ^ Symbol.comment ^ " not-a-cartouche")
        (Position.make0 101 1000 0 "" ""
          "isabelle-comment-initial-missing")
        "opening cartouche expected after formal comment" 102
        recover_initial
    val _ =
      expect_positioned_failure
        "generic missing opener"
        ("Comment::generic::<\n  " ^
          Symbol.comment ^ " not-a-cartouche")
        (Position.make0 201 2000 0 "" ""
          "isabelle-comment-generic-missing")
        "opening cartouche expected after formal comment" 202
        recover_generic
    val _ =
      expect_positioned_failure
        "log-data missing opener"
        ("l\<llangle>\n  " ^ Symbol.comment ^ " not-a-cartouche")
        (Position.make0 301 3000 0 "" ""
          "isabelle-comment-log-missing")
        "opening cartouche expected after formal comment" 302
        recover_log_data
    val _ =
      expect_positioned_failure
        "initial unterminated cartouche"
        ("\n" ^ Symbol.comment ^ " " ^ Symbol.open_ ^
          "outer " ^ Symbol.open_ ^ "nested" ^ Symbol.close)
        (Position.make0 401 4000 0 "" ""
          "isabelle-comment-initial-unterminated")
        "unterminated formal comment" 402
        recover_initial
    val _ =
      expect_positioned_failure
        "generic unterminated cartouche"
        ("Comment::generic::<\n  " ^ Symbol.comment ^ " " ^
          Symbol.open_ ^ "outer " ^ Symbol.open_ ^ "nested" ^
          Symbol.close)
        (Position.make0 501 5000 0 "" ""
          "isabelle-comment-generic-unterminated")
        "unterminated formal comment" 502
        recover_generic
    val _ =
      expect_positioned_failure
        "log-data unterminated cartouche"
        ("l\<llangle>\n  " ^ Symbol.comment ^ " " ^ Symbol.open_ ^
          "outer " ^ Symbol.open_ ^ "nested" ^ Symbol.close)
        (Position.make0 601 6000 0 "" ""
          "isabelle-comment-log-unterminated")
        "unterminated formal comment" 602
        recover_log_data
  in
    val _ =
      writeln
        "Isabelle-comment AST, positions, markup, diagnostics, and recovery regressions passed"
  end
\<close>

end
