theory Parser_Function_Semantic_Type_Tests
  imports
    Parser_Function_Regression_Tests
    Micro_Rust_Std_Lib.StdLib_Contracts
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open> Full declaration types and kernel equalities \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun same_type name expected =
      require (name ^ ": full declaration type changed")
        (Sign.typ_equiv (Proof_Context.theory_of ctxt)
          (declared_type ctxt name, Logic.varifyT_global expected))
    val _ =
      same_type "semantic_identity"
        \<^typ>\<open>nat \<Rightarrow>
          ('s::cancellative_sepalg, nat, bool, nat prompt, unit prompt_output) function_body\<close>
    val _ =
      same_type "semantic_unused_callback"
        \<^typ>\<open>nat \<Rightarrow> (nat \<Rightarrow> ('s::cancellative_sepalg, unit, 'abort, 'i, 'o) function_body) \<Rightarrow>
          ('s, nat, 'abort, 'i, 'o) function_body\<close>
    val _ =
      same_type "semantic_fixed_caller"
        \<^typ>\<open>nat \<Rightarrow> (unit, nat, bool, nat prompt, unit prompt_output) function_body\<close>
    val (state, _, abort, input, output) =
      channels (declared_type ctxt "semantic_polymorphic_identity")
    val _ = independent "unannotated channels no longer generalize" [state, abort, input, output]
  in val _ = () end
\<close>

lemma semantic_identity_former_instance:
  \<open>semantic_identity = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding semantic_identity_def by (rule refl)

lemma semantic_callback_client_equivalent:
  \<open>semantic_callback_client = semantic_callback_method_client\<close>
  unfolding semantic_callback_client_def semantic_callback_method_client_def by (rule refl)

lemma semantic_fixed_caller_folding:
  \<open>function_body (semantic_fixed_caller value) =
    (funcall1 semantic_identity (literal value) ::
      (unit, nat, nat, bool, nat prompt, unit prompt_output) expression)\<close>
  unfolding semantic_fixed_caller_def by simp

lemma semantic_local_expression_folding:
  fixes x :: nat
  defines D_def: \<open>D \<equiv> (funcall1 semantic_identity (literal x) ::
    (unit, nat, nat, bool, nat prompt, unit prompt_output) expression)\<close>
  shows \<open>function_body (semantic_fixed_caller x) = D\<close>
  unfolding semantic_fixed_caller_def
  by (simp only: function_body_simp D_def[symmetric])

lemma semantic_identity_contract:
  fixes \<Gamma> :: \<open>('s::cancellative_sepalg, bool, nat, unit) striple_context\<close>
  shows \<open>\<Gamma>; semantic_identity value \<Turnstile>\<^sub>F lift_pure_to_contract value\<close>
  by (crush_boot f: semantic_identity_def contract: lift_pure_to_contract_def; crush_base)

lemma semantic_fixed_caller_contract:
  fixes \<Gamma> :: \<open>(unit, bool, nat, unit) striple_context\<close>
  shows \<open>\<Gamma>; semantic_fixed_caller value \<Turnstile>\<^sub>F lift_pure_to_contract value\<close>
  apply (crush_boot f: semantic_fixed_caller_def contract: lift_pure_to_contract_def)
  by (crush_base specs add: semantic_identity_contract contracts add: lift_pure_to_contract_def)

lemma semantic_polymorphic_identity_contract:
  fixes \<Gamma> :: \<open>('s::sepalg, 'abort, 'i, 'o) striple_context\<close>
  shows \<open>\<Gamma>; semantic_polymorphic_identity value \<Turnstile>\<^sub>F lift_pure_to_contract value\<close>
  by (crush_boot f: semantic_polymorphic_identity_def contract: lift_pure_to_contract_def; crush_base)

section\<open> Holes, shared names and independent call instances \<close>

type_synonym ('s, 'v) semantic_identity_type =
  \<open>'v \<Rightarrow> ('s, 'v, bool, nat prompt, unit prompt_output) function_body\<close>

urust_fn [type = \<open>('s::cancellative_sepalg, nat) semantic_identity_type\<close>]
  semantic_synonym_identity
  \<open> fn SemanticSynonymIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn
  [type = \<open>('addr, 'global, 8 word) Global_Store.ref \<Rightarrow>
    ('s::cancellative_sepalg, ('addr, 'global, 8 word) Global_Store.ref,
      bool, nat prompt, unit prompt_output) function_body\<close>]
  semantic_pointer_identity
  \<open> fn SemanticPointerIdentity(value: *const u8) -> *const u8 { value } \<close>

urust_fn
  [type = \<open>'outer \<Rightarrow> ('s::cancellative_sepalg, 'outer, _, _, _) function_body\<close>]
  semantic_shared_names
  \<open> fn SemanticSharedNames(value: \<tau>\<open>'inner\<close>) -> \<tau>\<open>'inner\<close> { value } \<close>

urust_fn
  [type = \<open>_ \<Rightarrow> _ \<Rightarrow> (_, _, bool, _, _) function_body\<close>]
  semantic_independent_holes
  \<open> fn SemanticIndependentHoles(left: \<tau>\<open>_\<close>, right: \<tau>\<open>_\<close>) { left } \<close>

urust_fn
  [type = \<open>nat \<Rightarrow> (unit, nat, bool, _, _) function_body\<close>]
  semantic_specialized_name
  \<open> fn SemanticSpecializedName(value: \<tau>\<open>'value\<close>) -> \<tau>\<open>'value\<close> { value } \<close>

urust_fn
  [type = \<open>nat \<Rightarrow> (unit, nat, bool, _, _) function_body\<close>]
  semantic_two_instances
  \<open>
    fn SemanticTwoInstances(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      let ignored = SemanticSharedNames(true);
      SemanticSharedNames(value)
    }
  \<close>

urust_fn
  [type = \<open>('s, nat, bool, nat prompt, unit prompt_output) function_body\<close>]
  semantic_omitted_result
  \<open> fn SemanticOmittedResult() { 7 } \<close>

urust_fn
  [type = \<open>(unit, (unit, nat, bool, unit, unit) function_body, bool, unit, unit) function_body\<close>]
  semantic_returned_computation
  \<open>
    fn SemanticReturnedComputation() -> \<tau>\<open>(unit, nat, bool, unit, unit) function_body\<close> {
      \<llangle>fun_literal (7::nat)\<rrangle>
    }
  \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    val typ = declared_type ctxt "semantic_independent_holes"
    val [left, right] = binder_types typ
    val (state, result, abort, input, output) = channels typ
    val _ = require "result is not connected to the used parameter" (left = result)
    val _ = require "concrete abort was lost" (abort = \<^typ>\<open>bool\<close>)
    val _ = independent "independent annotation holes became identified" [left, right, state, input, output]
    val _ = require "outer and inner variable names failed to unify"
      (hd (binder_types (declared_type ctxt "semantic_shared_names")) =
        #2 (channels (declared_type ctxt "semantic_shared_names")))
    val _ = require "semantic type synonym changed the full declaration scheme"
      (Sign.typ_equiv (Proof_Context.theory_of ctxt)
        (declared_type ctxt "semantic_synonym_identity", declared_type ctxt "semantic_identity"))
    val pointer_type = declared_type ctxt "semantic_pointer_identity"
    val _ = require "annotation lost a pointer backend parameter"
      (Sign.typ_equiv (Proof_Context.theory_of ctxt)
        (pointer_type, Logic.varifyT_global
          \<^typ>\<open>('addr, 'global, 8 word) Global_Store.ref \<Rightarrow>
            ('s::cancellative_sepalg, ('addr, 'global, 8 word) Global_Store.ref,
              bool, nat prompt, unit prompt_output) function_body\<close>))
  in val _ = () end
\<close>

section\<open> Locale fixes and interpreted contexts \<close>

locale semantic_type_locale =
  fixes seed :: \<open>'s::cancellative_sepalg\<close>
begin

urust_fn
  [type = \<open>('s, unit, bool, nat prompt, unit prompt_output) function_body\<close>,
   register_notation = false]
  semantic_locale_callback
  \<open>
    fn SemanticLocaleCallback(
    ) -> () {
      \<llangle>let _ = seed in ()\<rrangle>
    }
  \<close>

urust_fn
  [type = \<open>('s \<Rightarrow> ('s, unit, bool, 'i, 'o) function_body) \<Rightarrow>
    ('s, unit, bool, 'i, 'o) function_body\<close>, register_notation = false]
  semantic_locale_unused
  \<open>
    fn SemanticLocaleUnused(callback: \<tau>\<open>'s \<Rightarrow> ('s, unit, bool, 'i, 'o) function_body\<close>) {}
  \<close>

end

interpretation semantic_unit: semantic_type_locale \<open>()\<close> .

lemma semantic_interpreted_channels:
  \<open>function_body semantic_unit.semantic_locale_callback =
    (literal () :: (unit, unit, unit, bool, nat prompt, unit prompt_output) expression)\<close>
  unfolding semantic_unit.semantic_locale_callback_def by simp

context semantic_type_locale
begin

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val typ =
      Syntax.read_term \<^context>
        ("semantic_locale_unused :: " ^
          "('s \<Rightarrow> ('s, unit, bool, 'i, 'o) function_body) \<Rightarrow> " ^
          "('s, unit, bool, 'i, 'o) function_body")
      |> fastype_of
    val callback = hd (binder_types typ)
    val (state, _, _, _, _) = channels typ
    val _ = require "locale state became flexible" (state = \<^typ>\<open>'s\<close>)
    val _ = require "locale callback state link was lost" (hd (binder_types callback) = state)
  in val _ = () end
\<close>

end

section\<open> Artifacts, options, positioned failures and rollback \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val semantic_type =
      "nat \<Rightarrow> (unit, nat, bool, nat prompt, unit prompt_output) function_body"
    val option = "[type = " ^ cartouche semantic_type ^ "]"
    val item = "fn SemanticArtifact(value: \<tau>" ^ cartouche "nat" ^ ") { value }"
    fun run options target = run_from base "semantic-artifact" (command options target item)
    val normal = run option "semantic_artifact" |> Toplevel.context_of
    val application =
      run ("[type = " ^ cartouche semantic_type ^ ", application_def]") "semantic_application"
      |> Toplevel.context_of
    val abbreviated =
      run ("[type = " ^ cartouche semantic_type ^ ", abbrev]") "semantic_abbreviated"
      |> Toplevel.context_of
    val suppressed =
      run ("[register_notation = false, type = " ^ cartouche semantic_type ^ "]") "semantic_suppressed"
      |> Toplevel.context_of
    val _ = require "application definition lost source argument"
      (is_Const (fst (Logic.dest_equals (Thm.prop_of (theorem normal "semantic_artifact")))) andalso
        not (is_Const (fst (Logic.dest_equals (Thm.prop_of (theorem application "semantic_application"))))))
    val _ = require "abbreviation installed a definition theorem"
      (is_none (try (fn () => theorem abbreviated "semantic_abbreviated") ()))
    val _ = require "registration suppression lost the constant"
      (Sign.typ_equiv (Proof_Context.theory_of suppressed)
        (declared_type suppressed "semantic_suppressed", Syntax.read_typ ctxt semantic_type))
    val _ = registry_unchanged "suppressed semantic function" ctxt suppressed
    val anonymous = run option "_" |> Toplevel.context_of
    val _ = require "anonymous semantic declaration installed a constant"
      (constant_snapshot ctxt = constant_snapshot anonymous)
    val _ = registry_unchanged "anonymous semantic function" ctxt anonymous

    fun reject_text label expected text =
      let
        val (result, reports) =
          Parser_Test_Reports.markup (fn () =>
            Exn.capture (run_from base label) text)
        val diagnostic = message result
        val _ = require (label ^ ": wrong diagnostic")
          (String.isSubstring expected diagnostic)
        val _ = require (label ^ ": no source position")
          (String.isSubstring label diagnostic andalso not (null (diagnostic_ranges diagnostic)))
        val _ = require (label ^ ": installed declaration markup")
          (null (declaration_definitions reports))
        val _ = require (label ^ ": mutated constant table")
          (constant_snapshot ctxt = constant_snapshot (Toplevel.context_of base))
        val _ = registry_unchanged label ctxt (Toplevel.context_of base)
        val _ = ignore (run_from base (label ^ "-recovery") (command option "semantic_failure" item))
      in () end
    fun reject label expected options body =
      reject_text label expected (command options "semantic_failure" body)
    fun typed typ = "[type = " ^ cartouche typ ^ "]"
    val _ = reject "semantic-parameter-mismatch" "parameter type" option
      "fn SemanticMismatch(value: bool) { 0 }"
    val _ = reject "semantic-return-mismatch" "return type" option
      "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) -> bool { true }"
    val _ = reject "semantic-arity" "semantic type expects 1 parameters" option
      "fn SemanticMismatch() { 0 }"
    val _ = reject "semantic-excess-arity" "semantic type expects 1 parameters" option
      "fn SemanticMismatch(left: \<tau>\<open>nat\<close>, right: \<tau>\<open>nat\<close>) { left }"
    val _ = reject "semantic-terminal" "semantic type must end in function_body"
      (typed "nat \<Rightarrow> nat") item
    val _ = reject "semantic-terminal-hole" "semantic type must end in function_body"
      (typed "nat \<Rightarrow> _") item
    val _ = reject "semantic-incompatible-sort" "parameter type"
      (typed "'a::cancellative_sepalg \<Rightarrow> (unit, unit, bool, unit, unit) function_body")
      "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) {}"
    val _ = reject "semantic-body-mismatch" "Type unification failed"
      option "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) { true }"
    val _ = reject "semantic-duplicate-option" "duplicate uRust command option"
      ("[type = " ^ cartouche semantic_type ^ ", type = " ^ cartouche semantic_type ^ "]") item
    val _ = reject "semantic-missing-value" "expects a HOL type" "[type]" item
    val _ = reject_text "semantic-rigid-locale" "parameter type"
      ("context semantic_type_locale begin\n" ^
        command
          (typed "'s \<Rightarrow> ('s, unit, bool, nat prompt, unit prompt_output) function_body")
          "semantic_failure"
          "fn SemanticMismatch(value: ()) {}")
  in val _ = () end
\<close>

end
