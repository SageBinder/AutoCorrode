(* Parser command, declaration, option, and generated-artifact tests. *)

theory Parser_Command_Tests
  imports
    Parser_Improvements_Tests
    Parser_Struct_Ambiguity_Left_Fixtures
    Parser_Struct_Ambiguity_Right_Fixtures
    Parser_Registered_Constructor_Fixtures
    Micro_Rust_Std_Lib.StdLib_Logging
begin

chapter\<open>Parser facade\<close>

declare [[urust_conformance = false]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]

section\<open> Parser facade smoke test \<close>

urust_expr smoke_num  \<open> 42 \<close>
urust_expr smoke_sfx  \<open> 1_u32 \<close>
urust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def

ML_val\<open>
  val _ =
    if Global_Theory.defined_fact \<^theory> "smoke_num_conformance"
    then error "default urust_conformance unexpectedly generated a theorem"
    else ()
\<close>


chapter\<open>Typed expression and shared command API\<close>

declare [[urust_conformance = false]]
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

declare [[urust_conformance = true]]

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

urust_expr [application_def, conformance = false]
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
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

urust_fn [application_def] typed_zero_function_application ::
  \<open>(unit, nat, unit, unit, unit) function_body\<close>
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

text\<open>
Parenthesized parameters use Isabelle liberal names. Minor keywords such as \<open>for\<close> are
available unquoted, while major command keywords must be string-quoted because command-span parsing
happens before the declaration parser. The collision example also checks that source parameters win
the literal role over an identically named HOL constant and parser registration; it is intentionally
parser-only because the legacy frontend resolves that spelling as the registered constant. The
parameter named \<open>zip\<close> shadows the real HOL \<open>List.zip\<close> constant and closes its direct
conformance proof by reflexivity, demonstrating that the legacy frontend receives a typed local fix
before parsing. The callable case additionally checks that an unqualified direct call head uses the
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

urust_fn [attrs = [], conformance = false]
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

urust_fn [conformance = false] zip_callable_parameter ::
  \<open>
    (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
    nat \<Rightarrow> _
  \<close>
  (zip, item)
  \<open> zip(item) \<close>

urust_fn [conformance = false] zip_method_registration ::
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
commands; named slots retain their ordinary source-order scope and conformance behavior.
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

urust_expr [conformance = false] wildcard_expression_inferred
  (_)
  \<open> () \<close>

urust_fn [conformance = false] wildcard_function_inferred ::
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

thm typed_closed_conformance
thm typed_contextual_conformance
thm typed_heterogeneous_conformance
thm typed_higher_order_conformance
thm typed_polymorphic_conformance
thm typed_sort_constrained_conformance
thm typed_placeholders_conformance
thm typed_function_common_conformance
thm typed_application_expression_conformance
thm typed_application_function_conformance
thm typed_zero_expression_default_conformance
thm typed_zero_expression_application_conformance
thm typed_zero_function_default_conformance
thm typed_zero_function_application_conformance
thm attributed_expression_conformance
thm empty_attributes_expression_conformance
thm parenthesized_minor_keyword_expression_conformance
thm partial_internal_placeholder_conformance
thm zip_parameter_value_conformance
thm quoted_major_parameter_conformance
thm wildcard_expression_single_conformance
thm wildcard_expression_mixed_conformance
thm wildcard_function_single_conformance
thm wildcard_function_mixed_conformance
thm wildcard_expression_application_conformance
thm wildcard_function_application_conformance
thm wildcard_expression_abbreviation_conformance
thm wildcard_function_abbreviation_conformance

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
      assert "urust_expr attrs leaked to its conformance theorem"
        (not (has_attribute "attributed_expression_conformance"))
    val _ =
      assert "urust_fn attrs leaked to its conformance theorem"
        (not (has_attribute "partial_internal_placeholder_conformance"))
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
The dummy declaration name elaborates and optionally proves conformance without installing a
constant, definition, abbreviation, or code equation. Both command facades use an invented
fresh internal name for the conformance fact and informational output only.
\<close>

urust_expr [application_def, conformance = true] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> item \<close>

urust_expr [application_def, conformance = true] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> item \<close>

urust_fn [application_def, conformance = true] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn [application_def, conformance = true] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr [abbrev = true, conformance = false] _
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
      if length expression_facts = 2 andalso
         length function_facts = 2
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

declare [[urust_conformance = false]]

urust_expr
  [conformance = false, verbosity = 0, abbrev = false]
  typed_flags_000 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, conformance = false, verbosity = 0]
  typed_flags_001 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 1, abbrev = false, conformance = false]
  typed_flags_010 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [conformance = false, abbrev = true, verbosity = 1]
  typed_flags_011 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 0, conformance = true, abbrev = false]
  typed_flags_100 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev, verbosity = 0, conformance = true]
  typed_flags_101 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [conformance, verbosity = 2, abbrev = false]
  typed_flags_110 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 2, abbrev = true, conformance = true]
  typed_flags_111 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev, conformance, verbosity = 2]
  typed_function_abbrev_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn
  [abbrev, conformance, verbosity = 2]
  typed_function_abbrev_command ::
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
  [abbrev, conformance]
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
  [conformance = true]
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
       "typed_flags_100", "typed_flags_110", "typed_against"]
    val abbreviations =
      ["typed_flags_001", "typed_flags_011",
       "typed_flags_101", "typed_flags_111",
       "typed_function_abbrev_common",
       "typed_function_abbrev_command",
       "wildcard_expression_abbreviation",
       "wildcard_function_abbreviation"]
    val conforming =
      ["typed_closed", "typed_contextual", "typed_heterogeneous",
       "typed_higher_order", "typed_polymorphic",
       "typed_sort_constrained", "typed_placeholders",
       "typed_function_common", "typed_application_expression",
       "typed_application_function",
       "typed_zero_expression_default", "typed_zero_expression_application",
       "typed_zero_function_default", "typed_zero_function_application",
       "attributed_expression",
       "empty_attributes_expression",
       "parenthesized_minor_keyword_expression",
       "partial_internal_placeholder", "zip_parameter_value",
       "quoted_major_parameter",
       "wildcard_expression_single", "wildcard_expression_mixed",
       "wildcard_function_single", "wildcard_function_mixed",
       "wildcard_expression_application", "wildcard_function_application",
       "wildcard_expression_abbreviation",
       "wildcard_function_abbreviation",
       "typed_flags_100",
       "typed_flags_101", "typed_flags_110", "typed_flags_111",
       "typed_function_abbrev_common", "typed_function_abbrev_command",
       "typed_against"]
    val nonconforming =
      ["partial_collision_function", "zip_callable_parameter",
       "zip_method_registration", "typed_application_implicit_parameter",
       "wildcard_expression_inferred", "wildcard_function_inferred",
       "typed_flags_000", "typed_flags_001",
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

    fun assert_expanded client abbreviation =
      let
        val proposition =
          Thm.prop_of
            (Proof_Context.get_thm ctxt (client ^ "_def"))
        val abbreviation_name = constant_name abbreviation
      in
        assert (quote abbreviation ^ " survived in a checked client term")
          (not
            (Term.exists_subterm
              (fn Const (name, _) => name = abbreviation_name
                | _ => false)
              proposition))
      end

    val _ = assert_expanded "typed_flags_abbrev_client" "typed_flags_001"
    val _ =
      assert_expanded "wildcard_expression_abbreviation_client"
        "wildcard_expression_abbreviation"
    val _ =
      assert_expanded "wildcard_function_abbreviation_client"
        "wildcard_function_abbreviation"
  in
    val _ = ()
  end
\<close>


section\<open> Exact expression and function shape \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun definition_equation name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals

    val (default_expression_lhs, default_expression_rhs) =
      definition_equation "typed_heterogeneous"
    val (default_function_lhs, default_function_rhs) =
      definition_equation "typed_function_common"
    val (application_expression_lhs, application_expression_rhs) =
      definition_equation "typed_application_expression"
    val (application_function_lhs, application_function_rhs) =
      definition_equation "typed_application_function"
    val (implicit_lhs, implicit_rhs) =
      definition_equation "typed_application_implicit_parameter"
    val (zero_expression_default_lhs, zero_expression_default_rhs) =
      definition_equation "typed_zero_expression_default"
    val (zero_expression_application_lhs, zero_expression_application_rhs) =
      definition_equation "typed_zero_expression_application"
    val (zero_function_default_lhs, zero_function_default_rhs) =
      definition_equation "typed_zero_function_default"
    val (zero_function_application_lhs, zero_function_application_rhs) =
      definition_equation "typed_zero_function_application"
    val application_expression_arguments =
      #2 (Term.strip_comb application_expression_lhs)
    val application_function_arguments =
      #2 (Term.strip_comb application_function_lhs)
    val implicit_arguments =
      #2 (Term.strip_comb implicit_lhs)
    val application_expression =
      fold_rev Term.lambda
        application_expression_arguments application_expression_rhs
    val application_function =
      fold_rev Term.lambda
        application_function_arguments application_function_rhs
    val implicit_definition =
      fold_rev Term.lambda implicit_arguments implicit_rhs
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
    val expected_implicit_definition =
      Syntax.check_term ctxt
        (Syntax.parse_term ctxt
          "(\<lambda>(ambient_adjustment :: nat) (item :: nat). \
          \\<lbrakk> \<llangle>item + ambient_adjustment\<rrangle> \<rbrakk>)")

    fun count_constant expected =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)

    val _ =
      if null (#2 (Term.strip_comb default_expression_lhs)) then ()
      else error "typed urust_expr: default definition moved arguments to the lhs"
    val _ =
      if null (#2 (Term.strip_comb default_function_lhs)) then ()
      else error "typed function: default definition moved arguments to the lhs"
    val _ =
      if Term.aconv (default_expression_rhs, expected_expression) then ()
      else error "typed urust_expr: default curried definition changed"
    val _ =
      if Term.aconv (default_function_rhs, expected_function) then ()
      else error "typed function: default curried definition changed"
    val _ =
      if map fastype_of application_expression_arguments =
          [HOLogic.natT, HOLogic.boolT]
      then ()
      else error "typed urust_expr: application definition argument order changed"
    val _ =
      if map fastype_of application_function_arguments = [HOLogic.natT]
      then ()
      else error "typed function: application definition omitted its lhs argument"
    val _ =
      if Term.aconv (application_expression, expected_expression) then ()
      else error "typed urust_expr: application definition changed the curried value"
    val _ =
      if Term.aconv (application_function, expected_function) then ()
      else error "typed function: application definition changed the curried value"
    val _ =
      if map fastype_of implicit_arguments = [HOLogic.natT, HOLogic.natT] andalso
         Term.aconv_untyped
           (implicit_definition, expected_implicit_definition)
      then ()
      else
        error
          "typed urust_expr: implicit definition parameter did not precede the source argument"
    val _ =
      if null (#2 (Term.strip_comb zero_expression_default_lhs)) andalso
         null (#2 (Term.strip_comb zero_expression_application_lhs)) andalso
         Term.aconv
           (zero_expression_default_rhs, zero_expression_application_rhs)
      then ()
      else error "typed urust_expr: zero-argument application mode changed the definition"
    val _ =
      if null (#2 (Term.strip_comb zero_function_default_lhs)) andalso
         null (#2 (Term.strip_comb zero_function_application_lhs)) andalso
         Term.aconv
           (zero_function_default_rhs, zero_function_application_rhs)
      then ()
      else error "typed urust_fn: zero-argument application mode changed the definition"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close>
          application_expression_rhs 0 = 0
      then ()
      else error "typed urust_expr: expression gained a FunctionBody wrapper"
    val _ =
      if count_constant \<^const_name>\<open>FunctionBody\<close>
          application_function_rhs 0 = 1
      then ()
      else error "typed urust_expr: function wrapper count changed"
  in
    val _ = ()
  end
\<close>


section\<open> Migration-sensitive typed expressions \<close>

declare [[urust_conformance = true]]

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
    val ternary_expression_type =
      "nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> " ^
        expression_type
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
            (SOME ternary_expression_type)
            [argument 19 190 "same", argument 21 210 "_",
             argument 23 230 "same"] "same")
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
    val wildcard =
      elaborate URust_Command.Expression
        (SOME unary_expression_type)
        [argument 39 390 "_"] "0"
    val _ =
      if fastype_of recovered =
          Syntax.read_typ ctxt unary_expression_type
      then ()
      else fail "successful elaboration did not recover after failures"
    val _ =
      if fastype_of wildcard =
          Syntax.read_typ ctxt unary_expression_type
      then ()
      else fail "typed wildcard argument did not retain its type slot"
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    val unit_source = Symbol.open_ ^ " () " ^ Symbol.close
    val zero_source = Symbol.open_ ^ " 0 " ^ Symbol.close
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
      ignore
        (run_command "typed-wildcard-argument"
          ("urust_expr typed_wildcard_argument :: " ^
            unary_expression_type ^ " (_) " ^ zero_source) ())
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
    val first_wildcard =
      Position.make0 11 100 0 "" file document_id
    val first_definition =
      Position.make0 11 105 0 "" file document_id
    val second_wildcard =
      Position.make0 11 110 0 "" file document_id
    val second_definition =
      Position.make0 11 115 0 "" file document_id
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
                     [("_", first_wildcard),
                      ("first", first_definition),
                      ("_", second_wildcard),
                      ("second", second_definition)],
                   arguments_pos = Position.line_file 9 file,
                   declared_type =
                     SOME
                       ("unit \<Rightarrow> nat \<Rightarrow> 32 word \<Rightarrow> bool \<Rightarrow> " ^
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

    fun has_variable_entity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
          Properties.get properties Markup.kindN =
            SOME "urust_var" andalso
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
         has_markup Markup.typingN second_definition andalso
         has_markup Markup.typingN first_wildcard andalso
         has_markup Markup.typingN second_wildcard
      then ()
      else error "typed binder markup audit: typed definitions lost tooltips"
    val _ =
      if not (has_markup Markup.boundN first_wildcard) andalso
         not (has_markup Markup.boundN second_wildcard) andalso
         not (has_variable_entity first_wildcard) andalso
         not (has_variable_entity second_wildcard)
      then ()
      else
        error
          "typed binder markup audit: wildcard received bound-variable/entity markup"
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

declare [[urust_conformance = false]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]

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

declare [[urust_conformance = false]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]

section\<open>Signature term checks\<close>

term fun_heterogeneous
term fun_polymorphic
term fun_sort_constrained
term fun_type_placeholders
term fun_higher_order
term fun_nested_result
term fun_explicit_prompt_output

text\<open>
The field declaration retains registration-first selector resolution. The direct call declaration is
parser-only because its declaration parameter now wins over the same-named NFunction registration,
unlike the registration-first legacy frontend.
\<close>

ML_val\<open>
  local
    val body =
      Proof_Context.get_thm \<^context> "fun_parameter_call_wins_def"
      |> Thm.prop_of
      |> Logic.dest_equals
      |> #2
    val registered = \<^const_name>\<open>fun_registered_call\<close>
    val _ =
      if Term.exists_subterm (fn Bound 1 => true | _ => false) body then ()
      else error "direct call parameter did not survive as the lexical function head"
    val _ =
      if Term.exists_subterm
          (fn Const (name, _) => name = registered | _ => false) body
      then error "registered direct-call backend survived lexical parameter resolution"
      else ()
  in
    val _ = ()
  end
\<close>

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
            ("nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> " ^ body_type)
            [parameter 11 110 "value", parameter 12 120 "_",
             parameter 13 130 "value"]
            "value")
    val wildcard =
      elaborate unary_type [parameter 17 170 "_"] "0"
    val _ =
      if fastype_of wildcard = Syntax.read_typ ctxt unary_type then ()
      else fail "wildcard parameter did not retain its type slot"
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

declare [[urust_conformance = false]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]

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
        ["urust_conformance: bool = false",
         "urust_verbosity: int = 0",
         "urust_abbrev: bool = false",
         "urust_application_def: bool = false"]
  in
    val _ = ()
  end
\<close>

urust_expr default_expr_flags
  (item)
  \<open> \<llangle>item :: nat\<rrangle> \<close>

urust_fn default_fun_flags ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>


section\<open> Inline flag combinations \<close>

text\<open>
\<open>urust_expr\<close> exercises every conformance/abbreviation combination and all three verbosity
levels. \<open>urust_fn\<close> exercises both conformance settings at every verbosity level. The option order
is deliberately varied. Both commands exercise the omitted \<open>= true\<close> shorthand for their Boolean
options while retaining explicit true and false coverage.
\<close>

urust_expr
  [conformance = false, verbosity = 0, abbrev = false]
  inline_expr_000 \<open> () \<close>
urust_expr
  [abbrev = true, conformance = false, verbosity = 0]
  inline_expr_001 \<open> () \<close>
urust_expr
  [verbosity = 1, abbrev = false, conformance = false]
  inline_expr_010 \<open> () \<close>
urust_expr
  [conformance = false, abbrev = true, verbosity = 1]
  inline_expr_011 \<open> () \<close>
urust_expr
  [verbosity = 0, conformance = true, abbrev = false]
  inline_expr_100 \<open> () \<close>
urust_expr
  [abbrev, verbosity = 0, conformance = true]
  inline_expr_101 \<open> () \<close>
urust_expr
  [conformance, verbosity = 2, abbrev = false]
  inline_expr_110 \<open> () \<close>
urust_expr
  [verbosity = 2, abbrev, conformance]
  inline_expr_111 \<open> () \<close>

urust_fn
  [verbosity = 0, conformance = false]
  inline_fun_00 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [conformance = false, verbosity = 1]
  inline_fun_01 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [verbosity = 2, conformance = false]
  inline_fun_02 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [conformance, verbosity = 0]
  inline_fun_10 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [verbosity = 1, conformance = true]
  inline_fun_11 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [conformance = true, verbosity = 2]
  inline_fun_12 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>

urust_fn
  [abbrev, conformance = false, verbosity = 0]
  inline_fun_abbrev_00 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>
urust_fn
  [conformance, verbosity = 2, abbrev]
  inline_fun_abbrev_12 ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close> () \<open> () \<close>


section\<open> Scoped settings and overrides \<close>

declare [[urust_conformance = true]]
declare [[urust_verbosity = 2]]
declare [[urust_abbrev = true]]
declare [[urust_application_def = true]]

urust_expr [application_def = false]
  scoped_all_true_expr \<open> () \<close>

urust_fn [application_def = false] scoped_all_true_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

urust_expr
  [verbosity = 0, abbrev = false, conformance = false, application_def = false]
  scoped_all_false_expr
  (item)
  \<open> \<llangle>item :: nat\<rrangle> \<close>

urust_fn
  [conformance = false, verbosity = 0, abbrev = false, application_def = false]
  scoped_all_false_fun ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr [abbrev = false]
  scoped_application_expression
  (item)
  \<open> \<llangle>item :: nat\<rrangle> \<close>

urust_fn [abbrev = false] scoped_application_function ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr [abbrev = false]
  scoped_partial_definition_expr \<open> () \<close>

urust_fn [conformance = false, abbrev = false]
  scoped_partial_definition_fun ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

declare [[urust_conformance = false]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]

urust_expr reset_expr_flags \<open> () \<close>

urust_fn reset_fun_flags ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>


section\<open> Contextual expressions \<close>

urust_expr [conformance = true]
  contextual_order
  (first, second)
  \<open> \<llangle>(first :: nat, second :: bool)\<rrangle> \<close>

urust_expr [conformance = true]
  contextual_antiquotation
  (left, right)
  \<open> \<llangle>(left :: nat) + right\<rrangle> \<close>

urust_expr [conformance = true]
  contextual_shadowing
  (item, outer)
  \<open> let item = true; \<llangle>(item, outer :: nat)\<rrangle> \<close>

urust_expr
  [abbrev, conformance, verbosity = 2]
  nie_contextual_helper
  (address, size)
  \<open> \<llangle>(address :: nat) + size\<rrangle> \<close>

urust_expr contextual_definition_against
  (operand)
  \<open> operand + 1u32 \<close>
  against \<open> \<lbrakk> operand + 1_u32 \<rbrakk> \<close>

urust_expr [abbrev]
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

urust_expr [abbrev, conformance]
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

definition fun_abbrev_client where
  \<open> fun_abbrev_client = inline_fun_abbrev_00 \<close>

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
       "scoped_all_false_expr", "scoped_all_false_fun",
       "scoped_application_expression", "scoped_application_function",
       "scoped_partial_definition_expr", "scoped_partial_definition_fun",
       "reset_expr_flags", "reset_fun_flags",
       "contextual_order", "contextual_antiquotation",
       "contextual_shadowing", "contextual_definition_against",
       "fun_definition_against", "fun_definition_against_2"]

    val abbreviations =
      ["inline_expr_001", "inline_expr_011",
       "inline_expr_101", "inline_expr_111",
       "inline_fun_abbrev_00", "inline_fun_abbrev_12",
       "scoped_all_true_expr", "scoped_all_true_fun",
       "nie_contextual_helper",
       "contextual_abbrev_against"]

    val conforming =
      ["inline_expr_100", "inline_expr_101",
       "inline_expr_110", "inline_expr_111",
       "inline_fun_10", "inline_fun_11", "inline_fun_12",
       "inline_fun_abbrev_12",
       "scoped_all_true_expr", "scoped_all_true_fun",
       "scoped_application_expression", "scoped_application_function",
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
       "inline_fun_abbrev_00",
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

    fun definition_argument_count name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals
      |> #1
      |> Term.strip_comb
      |> #2
      |> length

    val _ =
      assert "default urust_expr definition did not retain its lambda-shaped rhs"
        (definition_argument_count "default_expr_flags" = 0)
    val _ =
      assert "default urust_fn definition did not retain its lambda-shaped rhs"
        (definition_argument_count "default_fun_flags" = 0)
    val _ =
      assert "scoped application_def did not affect urust_expr"
        (definition_argument_count "scoped_application_expression" = 1)
    val _ =
      assert "scoped application_def did not affect urust_fn"
        (definition_argument_count "scoped_application_function" = 1)
    val _ =
      assert "inline false did not override scoped application_def for urust_expr"
        (definition_argument_count "scoped_all_false_expr" = 0)
    val _ =
      assert "inline false did not override scoped application_def for urust_fn"
        (definition_argument_count "scoped_all_false_fun" = 0)

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
    val _ = assert_expanded "fun_abbrev_client" "inline_fun_abbrev_00"
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
            ("urust_expr [abbrev] recovered_" ^
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

    fun option_block _ abbreviation options =
      "[" ^
        commas
          (("abbrev = " ^ Bool.toString abbreviation) :: options) ^
        "]"

    val expression_cases = [(Expr, false), (Expr, true)]
    val command_cases = expression_cases @ [(Fn, false), (Fn, true)]

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

    fun test_legacy_inline legacy (case_ as (kind, abbreviation)) =
      let
        val label =
          "legacy-inline-" ^ legacy ^ "-" ^ case_label case_
        val value =
          if legacy = "verbose" then " = 1" else ""
        val options =
          option_block kind abbreviation [legacy ^ value]
      in
        assert_rejected label
          (command kind options "legacy_inline_flag" "")
          ("unknown uRust command option " ^ quote legacy)
      end

    fun test_duplicate flag (case_ as (kind, abbreviation)) =
      let
        val label =
          "duplicate-" ^ flag ^ "-" ^ case_label case_
        val value = Bool.toString abbreviation
        val (first, second) =
          if flag = "verbosity"
          then ("0", "1")
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
            ["conformance = false"]
        val suffix =
          " against " ^ Symbol.open_ ^ " \<lbrakk> () \<rbrakk> " ^ Symbol.close
      in
        assert_rejected label
          (command kind options "contradictory_flag" suffix)
          "[conformance = false] cannot be combined with `against`"
      end

    fun test_shorthand_duplicate flag (case_ as (kind, abbreviation)) =
      let
        val label =
          "shorthand-duplicate-" ^ flag ^ "-" ^ case_label case_
        val options =
          if flag = "abbrev" then
            "[abbrev, abbrev = false]"
          else
            option_block kind abbreviation
              [flag, flag ^ " = false"]
      in
        assert_rejected label
          (command kind options "shorthand_duplicate" "")
          ("duplicate uRust command option " ^ quote flag)
      end

    fun test_invalid_integer_option option
        (case_ as (kind, abbreviation)) =
      let
        val label =
          "invalid-" ^ option ^ "-" ^ case_label case_
        val options = option_block kind abbreviation [option ^ " = 3"]
      in
        assert_rejected label
          (command kind options ("invalid_" ^ option) "")
          "must be 0, 1, or 2, but found 3"
      end

    fun test_missing_integer_value option
        (case_ as (kind, abbreviation)) =
      let
        val label =
          "missing-" ^ option ^ "-value-" ^ case_label case_
      in
        assert_rejected label
          (command kind
            (option_block kind abbreviation [option])
            "missing_integer_value" "")
          "expects an integer from 0 to 2"
      end

    fun test_wrong_option_type (case_ as (kind, abbreviation)) =
      let
        val label =
          "wrong-option-type-" ^ case_label case_
      in
        assert_rejected (label ^ "-verbosity")
          (command kind
            (option_block kind abbreviation ["verbosity = true"])
            "Boolean_verbosity" "")
          "expects an integer from 0 to 2";
        assert_rejected (label ^ "-conformance")
          (command kind
            (option_block kind abbreviation
              ["conformance = 1"])
            "integer_conformance" "")
          "expects true or false";
        assert_rejected (label ^ "-application-definition")
          (command kind
            (option_block kind abbreviation
              ["application_def = 1"])
            "integer_application_definition" "")
          "expects true or false"
      end

    fun test_attribute_options (case_ as (kind, abbreviation)) =
      let
        val label = "attrs-" ^ case_label case_
      in
        assert_rejected (label ^ "-missing-value")
          (command kind
            (option_block kind abbreviation ["attrs"])
            "missing_attribute_value" "")
          "expects an Isabelle attribute list";
        assert_rejected (label ^ "-wrong-type")
          (command kind
            (option_block kind abbreviation ["attrs = true"])
            "Boolean_attributes" "")
          "expects an Isabelle attribute list";
        assert_rejected (label ^ "-duplicate")
          (command kind
            (option_block kind abbreviation
              ["attrs = []", "attrs = [micro_rust_simps]"])
            "duplicate_attributes" "")
          "duplicate uRust command option \"attrs\"";
        assert_rejected (label ^ "-list-as-Boolean")
          (command kind
            (option_block kind abbreviation
              ["conformance = [micro_rust_simps]"])
            "attribute_list_conformance" "")
          "expects true or false";
        assert_rejected (label ^ "-list-as-application-definition")
          (command kind
            (option_block kind abbreviation
              ["application_def = [micro_rust_simps]"])
            "attribute_list_application_definition" "")
          "expects true or false"
      end

    val _ = List.app test_unknown command_cases
    val _ =
      List.app
        (fn prefixed =>
          List.app (test_prefixed prefixed) command_cases)
        ["urust_conformance", "urust_verbosity",
         "urust_abbrev", "urust_application_def"]
    val _ =
      List.app
        (fn legacy =>
          List.app (test_legacy_inline legacy) command_cases)
        ["conformance_check", "verbose"]
    val _ =
      List.app
        (fn flag =>
          List.app (test_duplicate flag) command_cases)
        ["conformance", "verbosity", "application_def"]
    val _ =
      List.app (test_duplicate "abbrev") command_cases
    val _ =
      List.app (test_shorthand_duplicate "conformance") command_cases
    val _ =
      List.app (test_shorthand_duplicate "application_def") command_cases
    val _ =
      List.app (test_shorthand_duplicate "abbrev") command_cases
    val _ = List.app test_contradiction command_cases
    val _ =
      List.app
        (fn option =>
          List.app (test_invalid_integer_option option) command_cases)
        ["verbosity"]
    val _ =
      List.app
        (fn option =>
          List.app (test_missing_integer_value option) command_cases)
        ["verbosity"]
    val _ = List.app test_wrong_option_type command_cases
    val _ = List.app test_attribute_options command_cases
    val _ =
      assert_rejected "invalid-scoped-verbosity"
        ("declare [[urust_verbosity = 3]]\n" ^
          "urust_expr invalid_scoped_verbosity " ^ unit_source)
        "must be 0, 1, or 2, but found 3"
    val _ =
      assert_rejected "legacy-scoped-conformance"
        ("declare [[urust_conformance_check = true]]\n" ^
          "urust_expr legacy_scoped_conformance " ^ unit_source)
        "urust_conformance_check"
    val _ =
      assert_rejected "legacy-scoped-verbosity"
        ("declare [[urust_verbose = 1]]\n" ^
          "urust_expr legacy_scoped_verbosity " ^ unit_source)
        "urust_verbose"
    val _ =
      assert_rejected "attributes-on-expression-abbreviation"
        (command Expr
          "[abbrev = true, attrs = [micro_rust_simps]]"
          "attributed_abbreviation" "")
        "attrs is not supported in abbreviation mode"
    val _ =
      assert_rejected "attributes-on-function-abbreviation"
        (command Fn
          "[abbrev = true, attrs = [micro_rust_simps]]"
          "attributed_function_abbreviation" "")
        "attrs is not supported in abbreviation mode"
    val _ =
      assert_rejected "application-definition-on-expression-abbreviation"
        (command Expr
          "[abbrev = true, application_def]"
          "application_definition_abbreviation" "")
        "abbreviation mode cannot be combined with `application_def`"
    val _ =
      assert_rejected "application-definition-on-function-abbreviation"
        (command Fn
          "[abbrev = true, application_def]"
          "application_definition_function_abbreviation" "")
        "abbreviation mode cannot be combined with `application_def`"
    val _ =
      assert_rejected "scoped-application-definition-on-expression-abbreviation"
        ("declare [[urust_application_def = true]]\n" ^
          "urust_expr [abbrev] scoped_application_definition_abbreviation " ^
          unit_source)
        "abbreviation mode cannot be combined with `application_def`"
    val _ =
      assert_rejected "scoped-application-definition-on-function-abbreviation"
        ("declare [[urust_application_def = true]]\n" ^
          "urust_fn [abbrev] scoped_application_definition_function_abbreviation :: " ^
          body_type ^ " () " ^ unit_source)
        "abbreviation mode cannot be combined with `application_def`"
    val _ =
      assert_rejected "attributes-on-anonymous-expression"
        (command Expr "[abbrev = false, attrs = []]" "_" "")
        "attrs is not supported for anonymous declarations"
    val _ =
      assert_rejected "attributes-on-anonymous-function"
        (command Fn "[attrs = []]" "_" "")
        "attrs is not supported for anonymous declarations"
    val _ =
      assert_rejected "unknown-expression-attribute"
        (command Expr
          "[abbrev = false, attrs = [unknown_command_surface_attribute]]"
          "unknown_expression_attribute" "")
        "unknown_command_surface_attribute"
    val _ =
      assert_rejected "unknown-function-attribute"
        (command Fn
          "[attrs = [unknown_command_surface_attribute]]"
          "unknown_function_attribute" "")
        "unknown_command_surface_attribute"

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
      ignore
        (run_command "terminal-placeholder-function"
          ("urust_fn terminal_placeholder_fun :: " ^
            Symbol.open_ ^ "_" ^ Symbol.close ^
            " () " ^ unit_source) ())
    val _ =
      ignore
        (run_command "terminal-and-internal-placeholder-function"
          ("urust_fn internal_terminal_placeholder_fun :: " ^
            Symbol.open_ ^ "_ \<Rightarrow> _" ^ Symbol.close ^
            " (item) " ^
            Symbol.open_ ^ " \<llangle>item :: nat\<rrangle> " ^ Symbol.close) ())
    val _ =
      ignore
        (run_command "minor-keyword-function-parameter"
          ("urust_fn minor_keyword_fun :: " ^
            Symbol.open_ ^ "nat \<Rightarrow> _" ^ Symbol.close ^
            " (for) " ^ unit_source) ())
    val _ =
      ignore
        (run_command "quoted-major-expression-parameter"
          ("urust_expr quoted_major_expr :: " ^
            Symbol.open_ ^
            "nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression" ^
            Symbol.close ^ " (\"lemma\") " ^
            Symbol.open_ ^ " lemma " ^ Symbol.close) ())
    val _ =
      assert_rejected "missing-function-type"
        ("urust_fn missing_fun_type () " ^ unit_source)
        "function elaboration requires a declared type"
    val _ =
      assert_rejected "partial-function-parameter-count"
        ("urust_fn partial_parameter_count :: " ^
          Symbol.open_ ^ "nat \<Rightarrow> _" ^ Symbol.close ^
          " () " ^ unit_source)
        "expects 1 parameter"
    val _ =
      assert_rejected "named-terminal-function-type"
        ("urust_fn named_terminal_type :: " ^
          Symbol.open_ ^ "nat \<Rightarrow> 'result" ^ Symbol.close ^
          " (item) " ^ Symbol.open_ ^ " item " ^ Symbol.close)
        "result type must be function_body"
    val _ =
      assert_rejected "schematic-terminal-function-type"
        ("urust_fn schematic_terminal_type :: " ^
          Symbol.open_ ^ "nat \<Rightarrow> ?'result" ^ Symbol.close ^
          " (item) " ^ Symbol.open_ ^ " item " ^ Symbol.close)
        "Illegal schematic type variable"
    val _ =
      assert_rejected "expression-terminal-placeholder"
        ("urust_expr expression_terminal_placeholder :: " ^
          Symbol.open_ ^ "_" ^ Symbol.close ^
          " () " ^ unit_source)
        "declared result type must be expression"
    val _ =
      ignore
        (run_command "wildcard-expression-parameter"
          ("urust_expr wildcard_args (_) " ^ unit_source) ())
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
    val _ =
      assert_rejected "unquoted-major-command-parameter"
        ("urust_fn unquoted_major_parameter :: " ^
          unary_body_type ^ " (lemma) " ^
          Symbol.open_ ^ " lemma " ^ Symbol.close)
        "Outer syntax error"
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
