(* Parser command, declaration, option, and generated-artifact tests. *)

theory Parser_Command_Tests
  imports
    Parser_Improvements_Tests
    Parser_Struct_Ambiguity_Left_Fixtures
    Parser_Struct_Ambiguity_Right_Fixtures
    Parser_Registered_Constructor_Fixtures
    Parser_Logging_Fixtures
begin

chapter\<open>Parser facade\<close>

declare [[urust_pp_test = true]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]

section\<open> Parser facade smoke test \<close>

urust_expr smoke_num  \<open> 42 \<close>
urust_expr smoke_sfx  \<open> 1_u32 \<close>
urust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def



chapter\<open>Typed expression and shared command API\<close>

declare [[urust_pp_test = true]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]

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

urust_expr [application_def, attrs = [micro_rust_simps]]
  typed_application_expression ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, nat \<times> bool, unit, unit, unit, unit) expression\<close>
  (number, flag)
  \<open> \<llangle>(number, flag)\<rrangle> \<close>

urust_fn [application_def]
  typed_application_function ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr [application_def]
  typed_application_implicit_parameter
  (item)
  \<open> \<llangle>(item :: nat) + ambient_adjustment\<rrangle> \<close>

urust_expr typed_zero_expression_default ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

urust_expr [application_def] typed_zero_expression_application ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

urust_fn typed_zero_function_default ::
  \<open>(unit, nat, unit, unit, unit) function_body\<close>
  ()
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

urust_fn [application_def] typed_zero_function_application ::
  \<open>(unit, nat, unit, unit, unit) function_body\<close>
  ()
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

text\<open>
Parenthesized parameters use Isabelle liberal names. Minor keywords such as \<open>for\<close> are
available unquoted, while major command keywords must be string-quoted because command-span parsing
happens before the declaration parser. The collision example also checks that source parameters win
the literal role over an identically named HOL constant and parser registration; it is intentionally
parser-only because the lexical parameter deliberately takes precedence over the registered constant. The
parameter named \<open>zip\<close> shadows the real HOL \<open>List.zip\<close> constant. The callable case additionally checks that an unqualified direct call head uses the
parameter before an exact NFunction registration; the method case pins the retained
registration-first method policy. The internal-placeholder example checks that typed fixes use the
completed declaration type.
\<close>

definition command_parameter_collision :: nat
  where \<open> command_parameter_collision = 17 \<close>

urust_notation (literal)
  command_parameter_collision ("command_parameter_collision")

urust_expr [attrs = [micro_rust_simps]]
  attributed_expression ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr [attrs = []]
  empty_attributes_expression ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr parenthesized_minor_keyword_expression ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit, unit) expression\<close>
  (for)
  \<open> () \<close>

urust_fn [attrs = []]
  partial_collision_function ::
  \<open>nat \<Rightarrow> _\<close>
  (command_parameter_collision)
  \<open> command_parameter_collision \<close>

urust_fn [attrs = [micro_rust_simps]]
  partial_internal_placeholder ::
  \<open>_ \<Rightarrow> _\<close>
  (item)
  \<open> \<llangle>item :: nat\<rrangle> \<close>

urust_fn zip_parameter_value ::
  \<open>nat \<Rightarrow> _\<close>
  (zip)
  \<open> zip \<close>

definition command_registered_zip ::
    \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> command_registered_zip \<equiv> lift_fun1 (\<lambda>item. item + 1) \<close>

urust_notation (call) command_registered_zip ("zip")

urust_fn  zip_callable_parameter ::
  \<open>
    (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
    nat \<Rightarrow> _
  \<close>
  (zip, item)
  \<open> zip(item) \<close>

urust_fn  zip_method_registration ::
  \<open>
    (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
    nat \<Rightarrow> _
  \<close>
  (zip, item)
  \<open> item.zip() \<close>

urust_fn quoted_major_parameter ::
  \<open>nat \<Rightarrow> _\<close>
  ("lemma")
  \<open> lemma \<close>

text\<open>
A declaration wildcard consumes one argument type and contributes one anonymous abstraction without
entering lexical name resolution. Single, repeated, and mixed wildcard slots are accepted by both
commands; named slots retain their ordinary source-order scope.
\<close>

urust_expr wildcard_expression_single ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit, unit) expression\<close>
  (_)
  \<open> () \<close>

urust_expr wildcard_expression_mixed ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow>
    (unit, bool, unit, unit, unit, unit) expression\<close>
  (_, kept, _)
  \<open> kept \<close>

urust_fn wildcard_function_single ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit) function_body\<close>
  (_)
  \<open> () \<close>

urust_fn wildcard_function_mixed ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow>
    (unit, bool, unit, unit, unit) function_body\<close>
  (_, kept, _)
  \<open> kept \<close>

urust_expr  wildcard_expression_inferred
  (_)
  \<open> () \<close>

urust_fn  wildcard_function_inferred ::
  \<open>_ \<Rightarrow> _\<close>
  (_)
  \<open> \<llangle>0 :: nat\<rrangle> \<close>

urust_expr [application_def] wildcard_expression_application ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit, unit) expression\<close>
  (_)
  \<open> () \<close>

urust_fn [application_def] wildcard_function_application ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit) function_body\<close>
  (_)
  \<open> () \<close>

urust_expr [abbrev] wildcard_expression_abbreviation ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, bool, unit, unit, unit, unit) expression\<close>
  (_, kept)
  \<open> kept \<close>

urust_fn [abbrev] wildcard_function_abbreviation ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, bool, unit, unit, unit) function_body\<close>
  (_, kept)
  \<open> kept \<close>
ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val attributes =
      Named_Theorems.get ctxt \<^named_theorems>\<open>micro_rust_simps\<close>

    fun theorem name = Proof_Context.get_thm ctxt name
    fun has_attribute name =
      exists (Thm.equiv_thm thy o pair (theorem name)) attributes

    fun assert message condition =
      if condition then () else error ("command surface audit: " ^ message)

    fun definition_equation name =
      theorem name
      |> Thm.prop_of
      |> Logic.dest_equals

    fun definition_term name =
      let
        val (lhs, rhs) = definition_equation name
      in
        fold_rev Term.lambda (#2 (Term.strip_comb lhs)) rhs
      end

    val _ =
      assert "urust_expr attrs did not decorate its _def theorem"
        (has_attribute "attributed_expression_def")
    val _ =
      assert "urust_fn attrs did not decorate its _def theorem"
        (has_attribute "partial_internal_placeholder_def")
    val _ =
      assert "attrs = [] unexpectedly decorated an expression definition"
        (not (has_attribute "empty_attributes_expression_def"))
    val _ =
      assert "attrs = [] unexpectedly decorated a function definition"
        (not (has_attribute "partial_collision_function_def"))
    val _ =
      assert "application-shaped urust_expr lost its _def attributes"
        (has_attribute "typed_application_expression_def")

    val collision_body =
      definition_term "partial_collision_function_def"
    val registered_constant =
      \<^const_name>\<open>command_parameter_collision\<close>
    val _ =
      assert "registered/HOL collision did not resolve to the lexical parameter"
        (Term.exists_subterm (fn Bound 0 => true | _ => false) collision_body)
    val _ =
      assert "registered/HOL constant survived lexical parameter resolution"
        (not
          (Term.exists_subterm
            (fn Const (name, _) => name = registered_constant | _ => false)
            collision_body))

    val zip_value_body =
      definition_term "zip_parameter_value_def"
    val hol_zip = \<^const_name>\<open>List.zip\<close>
    val _ =
      assert "HOL zip collision did not resolve to the typed local fix"
        (Term.exists_subterm
          (fn Bound 0 => true | _ => false)
          zip_value_body)
    val _ =
      assert "List.zip survived typed-fix resolution"
        (not
          (Term.exists_subterm
            (fn Const (name, _) => name = hol_zip | _ => false)
            zip_value_body))

    val registered_zip = \<^const_name>\<open>command_registered_zip\<close>
    val callable_body =
      definition_term "zip_callable_parameter_def"
    val _ =
      assert "callable zip parameter did not survive as a lexical head"
        (Term.exists_subterm (fn Bound 1 => true | _ => false) callable_body)
    val _ =
      assert "List.zip survived direct callable-parameter resolution"
        (not
          (Term.exists_subterm
            (fn Const (name, _) => name = hol_zip | _ => false)
            callable_body))
    val _ =
      assert "registered zip survived direct callable-parameter resolution"
        (not
          (Term.exists_subterm
            (fn Const (name, _) => name = registered_zip | _ => false)
            callable_body))

    val method_body =
      theorem "zip_method_registration_def"
      |> Thm.prop_of
      |> Logic.dest_equals
      |> #2
    val _ =
      assert "method zip stopped using its exact registration"
        (Term.exists_subterm
          (fn Const (name, _) => name = registered_zip | _ => false)
          method_body)
    val _ =
      assert "HOL List.zip leaked into method registration resolution"
        (not
          (Term.exists_subterm
            (fn Const (name, _) => name = hol_zip | _ => false)
            method_body))

    val partial_type =
      Syntax.read_term ctxt "partial_internal_placeholder"
      |> fastype_of
    val (parameter_types, result_type) = Term.strip_type partial_type
    val _ =
      assert "internal argument placeholder did not infer nat"
        (parameter_types = [HOLogic.natT])
    val _ =
      (case result_type of
         Type (name, [stateT, valueT, returnT, abortT, inputT]) =>
           (assert "terminal placeholder did not become function_body"
              (name = \<^type_name>\<open>function_body\<close>);
            assert "function result value channel did not infer nat"
              (valueT = HOLogic.natT);
            assert "fresh function_body channels were accidentally identified"
              (length (distinct (op =) [stateT, returnT, abortT, inputT]) = 4))
       | _ =>
           error
             "command surface audit: terminal placeholder has malformed completed type")
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then ()
      else error ("declaration wildcard audit: " ^ message)

    fun definition_equation name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals

    fun strip_abstractions 0 term = ([], term)
      | strip_abstractions count (Abs (name, T, body)) =
          strip_abstractions (count - 1) body
          |>> cons (name, T)
      | strip_abstractions _ _ =
          error "declaration wildcard audit: missing abstraction"

    fun contains_bound index =
      Term.exists_subterm
        (fn Bound candidate => candidate = index | _ => false)

    fun count_constant expected =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)

    val (_, expression_term) =
      definition_equation "wildcard_expression_mixed"
    val (expression_abstractions, expression_body) =
      strip_abstractions 3 expression_term
    val (_, function_term) =
      definition_equation "wildcard_function_mixed"
    val (function_abstractions, function_body) =
      strip_abstractions 3 function_term
    val expected_types =
      [HOLogic.natT, HOLogic.boolT, \<^typ>\<open>32 word\<close>]

    val _ =
      assert "typed expression slots changed order"
        (map #2 expression_abstractions = expected_types)
    val _ =
      assert "typed function slots changed order"
        (map #2 function_abstractions = expected_types)
    val _ =
      assert "expression wildcards are not anonymous binders"
        (map #1 expression_abstractions
          |> (fn [first, _, third] =>
                first = Name.uu andalso third = Name.uu
               | _ => false))
    val _ =
      assert "function wildcards are not anonymous binders"
        (map #1 function_abstractions
          |> (fn [first, _, third] =>
                first = Name.uu andalso third = Name.uu
               | _ => false))
    val _ =
      assert "mixed expression lost the named middle argument"
        (contains_bound 1 expression_body andalso
         not (contains_bound 0 expression_body) andalso
         not (contains_bound 2 expression_body))
    val _ =
      assert "mixed function lost the named middle parameter"
        (contains_bound 1 function_body andalso
         not (contains_bound 0 function_body) andalso
         not (contains_bound 2 function_body))
    val _ =
      assert "urust_expr gained a FunctionBody wrapper"
        (count_constant \<^const_name>\<open>FunctionBody\<close>
          expression_term 0 = 0)
    val _ =
      assert "urust_fn does not contain exactly one FunctionBody"
        (count_constant \<^const_name>\<open>FunctionBody\<close>
          function_term 0 = 1)

    val (allocation, environment) =
      URust_Resolution.allocate_expression_arguments ctxt
        URust_Resolution.empty_environment
        [(("_", Position.none), HOLogic.natT)]
    val allocated =
      fold_rev (fn abstraction => fn term => abstraction term)
        allocation (Free ("wildcard_probe", HOLogic.boolT))
    val _ =
      assert "wildcard entered lexical lookup"
        (is_none (URust_Resolution.lookup_local environment "_"))
    val _ =
      assert "wildcard allocation lost its declared type"
        (case allocated of
           Abs (name, T, Free ("wildcard_probe", bodyT)) =>
             name = Name.uu andalso T = HOLogic.natT andalso
               bodyT = HOLogic.boolT
         | _ => false)

    fun reconstructed_application name =
      let
        val (lhs, rhs) = definition_equation name
      in
        fold_rev Term.lambda (#2 (Term.strip_comb lhs)) rhs
      end

    val (_, expression_single) =
      definition_equation "wildcard_expression_single"
    val (_, function_single) =
      definition_equation "wildcard_function_single"
    val _ =
      assert "application_def changed the anonymous expression slot"
        (Term.aconv
          (expression_single,
           reconstructed_application "wildcard_expression_application"))
    val _ =
      assert "application_def changed the anonymous function slot"
        (Term.aconv
          (function_single,
           reconstructed_application "wildcard_function_application"))

    fun declaration_type name =
      Syntax.read_term ctxt name |> fastype_of
    val (inferred_expression_arguments, _) =
      Term.strip_type (declaration_type "wildcard_expression_inferred")
    val (inferred_function_arguments, _) =
      Term.strip_type (declaration_type "wildcard_function_inferred")
    val _ =
      assert "untyped urust_expr did not infer one wildcard slot"
        (length inferred_expression_arguments = 1 andalso
         hd inferred_expression_arguments <> dummyT)
    val _ =
      assert "placeholder-typed urust_fn did not infer one wildcard slot"
        (length inferred_function_arguments = 1 andalso
         hd inferred_function_arguments <> dummyT)
  in
    val _ = ()
  end
\<close>


section\<open> Anonymous declarations \<close>

text\<open>
The dummy declaration name elaborates and checks a term without installing a constant, definition,
abbreviation, theorem, or code equation.
\<close>

urust_expr [application_def] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> item \<close>

urust_fn [application_def] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr [abbrev = true] _
  \<open> () \<close>

ML_val\<open>
  local
    val constants =
      Proof_Context.consts_of \<^context>
      |> Consts.dest
      |> #constants
      |> map #1

    fun anonymous_base command name =
      String.isPrefix (command ^ "_anonymous_")
        (Long_Name.base_name name)

    val _ =
      if not (exists (anonymous_base "urust_expr") constants) andalso
         not (exists (anonymous_base "urust_fn") constants)
      then ()
      else error "anonymous uRust command registered a constant"
  in
    val _ = ()
  end
\<close>


section\<open> Definitions, abbreviations, flags, and locales \<close>


urust_expr
  [verbosity = 0, abbrev = false]
  typed_flags_000 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, verbosity = 0]
  typed_flags_001 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 1, abbrev = false]
  typed_flags_010 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, verbosity = 1]
  typed_flags_011 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 0, abbrev = false]
  typed_flags_100 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev, verbosity = 0]
  typed_flags_101 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 2, abbrev = false]
  typed_flags_110 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 2, abbrev = true]
  typed_flags_111 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev, verbosity = 2]
  typed_function_abbrev_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn
  [abbrev, verbosity = 2]
  typed_function_abbrev_command ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr typed_parser_only ::
  \<open>32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit, unit) expression\<close>
  (operand)
  \<open> operand + 1u32 \<close>

locale typed_expression_locale =
  fixes offset :: nat
begin

urust_expr
  [abbrev]
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

  typed_ambient_tfree_function ::
  \<open>(unit, nat, unit, unit, unit) function_body\<close>
  \<open> \<llangle>typed_ambient_probe TYPE('ambient)\<rrangle> \<close>
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

definition wildcard_expression_abbreviation_client where
  \<open>
    wildcard_expression_abbreviation_client =
      wildcard_expression_abbreviation (0 :: nat) True
  \<close>

definition wildcard_function_abbreviation_client where
  \<open>
    wildcard_function_abbreviation_client =
      wildcard_function_abbreviation (0 :: nat) True
  \<close>

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
       "typed_function_common", "typed_application_expression",
       "typed_application_function", "typed_application_implicit_parameter",
       "typed_zero_expression_default", "typed_zero_expression_application",
       "typed_zero_function_default", "typed_zero_function_application",
       "attributed_expression",
       "empty_attributes_expression",
       "parenthesized_minor_keyword_expression",
       "partial_collision_function", "partial_internal_placeholder",
       "zip_parameter_value", "zip_callable_parameter",
       "zip_method_registration", "quoted_major_parameter",
       "wildcard_expression_single", "wildcard_expression_mixed",
       "wildcard_function_single", "wildcard_function_mixed",
       "wildcard_expression_inferred", "wildcard_function_inferred",
       "wildcard_expression_application", "wildcard_function_application",
       "typed_flags_000", "typed_flags_010",
       "typed_flags_100", "typed_flags_110", "typed_parser_only"]
    val abbreviations =
      ["typed_flags_001", "typed_flags_011",
       "typed_flags_101", "typed_flags_111",
       "typed_function_abbrev_common",
       "typed_function_abbrev_command",
       "wildcard_expression_abbreviation",
       "wildcard_function_abbreviation"]
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

    val _ = assert_expanded "typed_flags_abbrev_client" "typed_flags_001"
  in
    val _ = ()
  end
\<close>

section\<open> Pretty-printer roundtrip checking \<close>

urust_expr [pp_test = false] pp_expr_disabled
  (item)
  \<open> let value = \<llangle>item :: nat\<rrangle>; (value) \<close>

urust_expr [pp_test] pp_expr_enabled
  (item)
  \<open> let value = \<llangle>item :: nat\<rrangle>; (value) \<close>

lemma pp_expr_enabled_same:
  \<open>pp_expr_enabled = pp_expr_disabled\<close>
  unfolding pp_expr_enabled_def pp_expr_disabled_def
  by (rule refl)

urust_fn [pp_test = false] pp_fun_disabled ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn [pp_test] pp_fun_enabled ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

lemma pp_fun_enabled_same:
  \<open>pp_fun_enabled = pp_fun_disabled\<close>
  unfolding pp_fun_enabled_def pp_fun_disabled_def
  by (rule refl)


section\<open> Invalid flags and argument lists \<close>

ML_val\<open>
  local
    val unit_source = Symbol.open_ ^ " () " ^ Symbol.close
    val body_type =
      Symbol.open_ ^
      "(unit, unit, unit, unit, unit) function_body" ^
      Symbol.close

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
      (case Exn.result (run_command source_name command_text) () of
         Exn.Res _ =>
           error
             ("invalid uRust command was unexpectedly accepted" ^
               Position.here (Position.file source_name))
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else if String.isSubstring expected (Runtime.exn_message exn)
           then ()
           else
             error
               ("unexpected uRust command diagnostic:\n" ^
                 Runtime.exn_message exn ^ "\nexpected: " ^ quote expected))

    val _ =
      assert_rejected "unknown-option"
        ("urust_expr [urust_future_flag = true] unknown_flag " ^ unit_source)
        "unknown uRust command option"
    val _ =
      assert_rejected "duplicate-option"
        ("urust_expr [application_def, application_def = false] duplicate_flag " ^
          unit_source)
        "duplicate uRust command option"
    val _ =
      assert_rejected "invalid-verbosity"
        ("urust_expr [verbosity = 3] invalid_verbosity " ^ unit_source)
        "must be 0, 1, or 2"
    val _ =
      assert_rejected "invalid-pp-test"
        ("urust_expr [pp_test = 1] invalid_pp_test " ^ unit_source)
        "expects true or false"
    val _ =
      assert_rejected "invalid-pretty"
        ("urust_expr [pretty = 1] invalid_pretty " ^ unit_source)
        "expects true or false"
    val _ =
      assert_rejected "attributes-on-abbreviation"
        ("urust_expr [abbrev, attrs = []] attributed_abbreviation " ^ unit_source)
        "attrs is not supported in abbreviation mode"
    val _ =
      assert_rejected "missing-function-type"
        ("urust_fn missing_fun_type () " ^ unit_source)
        "function elaboration requires a declared type"
    val _ =
      assert_rejected "duplicate-expression-parameters"
        ("urust_expr duplicate_args (item, item) " ^ unit_source)
        "duplicate argument"
    val _ =
      assert_rejected "old-function-command"
        ("urust_fun old_function :: " ^ body_type ^ " () " ^ unit_source)
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



end
