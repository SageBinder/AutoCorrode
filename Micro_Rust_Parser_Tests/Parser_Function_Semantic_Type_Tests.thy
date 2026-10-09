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

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>'value::linorder\<close>,
   input = \<open>'channel\<close>, output = \<open>'channel\<close>]
  semantic_channel_sharing
  \<open>
    fn SemanticChannelSharing(value: \<tau>\<open>'value\<close>) -> \<tau>\<open>'value\<close> { value }
  \<close>

urust_fn
  [state = \<open>_::cancellative_sepalg\<close>, abort = \<open>_::linorder\<close>,
   input = \<open>_::finite\<close>, output = \<open>_::order\<close>]
  semantic_sorted_holes
  \<open> fn SemanticSortedHoles(left: \<tau>\<open>_\<close>, right: \<tau>\<open>_\<close>) {} \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    val typ = declared_type ctxt "semantic_channel_sharing"
    val (state, result, abort, input, output) = channels typ
    val _ = require "channel and signature names did not share" (result = abort andalso
      binder_types typ = [result] andalso input = output)
    val _ = require "shared channel sort was lost"
      (Sign.subsort (Proof_Context.theory_of ctxt) (sort_of result, \<^sort>\<open>linorder\<close>))
    val _ = independent "unrelated shared names were captured" [state, result, input]
    val holes = declared_type ctxt "semantic_sorted_holes"
    val (s, r, a, i, o') = channels holes
    val _ = require "omitted result is not unit" (r = \<^typ>\<open>unit\<close>)
    val _ = independent "sorted holes became identified" (binder_types holes @ [s, a, i, o'])
    val _ =
      List.app (fn (typ, expected) =>
        require "channel hole lost its sort"
          (Sign.subsort (Proof_Context.theory_of ctxt) (sort_of typ, expected)))
        [(s, \<^sort>\<open>cancellative_sepalg\<close>), (a, \<^sort>\<open>linorder\<close>),
         (i, \<^sort>\<open>finite\<close>), (o', \<^sort>\<open>order\<close>)]
  in val _ = () end
\<close>

type_synonym 'v semantic_input_type = \<open>'v prompt\<close>
type_synonym 'v semantic_output_type = \<open>'v prompt_output\<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat semantic_input_type\<close>, output = \<open>unit semantic_output_type\<close>]
  semantic_synonym_identity
  \<open> fn SemanticSynonymIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  semantic_pointer_identity
  \<open> fn SemanticPointerIdentity(value: *const u8) -> *const u8 { value } \<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>]
  semantic_shared_names
  \<open> fn SemanticSharedNames(value: \<tau>\<open>'inner\<close>) -> \<tau>\<open>'inner\<close> { value } \<close>

urust_fn
  [state = \<open>_\<close>, abort = \<open>bool\<close>, input = \<open>_\<close>, output = \<open>_\<close>]
  semantic_independent_holes
  \<open> fn SemanticIndependentHoles(left: \<tau>\<open>_\<close>, right: \<tau>\<open>_\<close>) -> \<tau>\<open>_\<close> { left } \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>bool\<close>]
  semantic_specialized_name
  \<open> fn SemanticSpecializedName(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>bool\<close>]
  semantic_two_instances
  \<open>
    fn SemanticTwoInstances(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      let ignored = SemanticSharedNames(true);
      SemanticSharedNames(value)
    }
  \<close>

urust_fn
  [state = \<open>'s\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  semantic_omitted_result
  \<open> fn SemanticOmittedResult() -> \<tau>\<open>nat\<close> { 7 } \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>bool\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>]
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
    val _ = require "signature variable names failed to share"
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
  [state = \<open>'s\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>,
   register_notation = false]
  semantic_locale_callback
  \<open>
    fn SemanticLocaleCallback(
    ) -> () {
      \<llangle>let _ = seed in ()\<rrangle>
    }
  \<close>

urust_fn
  [state = \<open>'s\<close>, abort = \<open>bool\<close>, input = \<open>'i\<close>, output = \<open>'o\<close>,
   register_notation = false]
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

section\<open> Every channel combination and default unit results \<close>

urust_fn [abort = \<open>bool\<close>] semantic_default_unit
  \<open> fn SemanticDefaultUnit(value: \<tau>\<open>nat\<close>) { () } \<close>

urust_fn [abort = \<open>bool\<close>] semantic_explicit_unit
  \<open> fn SemanticExplicitUnit(value: \<tau>\<open>nat\<close>) -> () { () } \<close>

lemma semantic_default_unit_equivalent:
  \<open>semantic_default_unit = semantic_explicit_unit\<close>
  unfolding semantic_default_unit_def semantic_explicit_unit_def by (rule refl)

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val entries =
      [("state", "'s::cancellative_sepalg"),
       ("abort", "bool"), ("input", "nat prompt"), ("output", "unit prompt_output")]
    fun subsets [] = [[]]
      | subsets (entry :: rest) =
          let val smaller = subsets rest in smaller @ map (cons entry) smaller end
    fun check selected =
      let
        val options =
          if null selected then ""
          else "[" ^ commas (map (fn (name, typ) => name ^ " = " ^ cartouche typ) selected) ^ "]"
        fun channel name fallback =
          the_default fallback (AList.lookup (op =) selected name)
        val expected =
          "nat \<Rightarrow> (" ^ commas
            [channel "state" "'s", "unit", channel "abort" "'abort",
             channel "input" "'input", channel "output" "'output"] ^ ") function_body"
        fun run annotation =
          run_from base ("semantic-combination-" ^ space_implode "-" (map fst selected))
            (command options "semantic_combination"
              ("fn SemanticCombination(value: \<tau>" ^ cartouche "nat" ^ ")" ^
                annotation ^ " { () }"))
          |> Toplevel.context_of
        val omitted = run ""
        val explicit = run " -> ()"
        val _ =
          List.app (fn context =>
            require ("channel combination changed its complete type: " ^ options)
              (Sign.typ_equiv (Proof_Context.theory_of context)
                (declared_type context "semantic_combination",
                 Logic.varifyT_global (Syntax.read_typ ctxt expected))))
            [omitted, explicit]
        val _ = require "default unit changed the definition"
          (Term.aconv (rhs omitted "semantic_combination", rhs explicit "semantic_combination"))
      in () end
    val _ = List.app check (subsets entries)
  in val _ = () end
\<close>

section\<open> Artifacts, options, positioned failures and rollback \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val semantic_type =
      "nat \<Rightarrow> (unit, nat, bool, nat prompt, unit prompt_output) function_body"
    val channel_options =
      "state = " ^ cartouche "unit" ^ ", abort = " ^ cartouche "bool" ^
      ", input = " ^ cartouche "nat prompt" ^ ", output = " ^ cartouche "unit prompt_output"
    val option = "[" ^ channel_options ^ "]"
    val item = "fn SemanticArtifact(value: \<tau>" ^ cartouche "nat" ^
      ") -> \<tau>" ^ cartouche "nat" ^ " { value }"
    fun run options target = run_from base "semantic-artifact" (command options target item)
    val normal = run option "semantic_artifact" |> Toplevel.context_of
    val application =
      run ("[" ^ channel_options ^ ", application_def]") "semantic_application"
      |> Toplevel.context_of
    val abbreviated =
      run ("[" ^ channel_options ^ ", abbrev]") "semantic_abbreviated"
      |> Toplevel.context_of
    val suppressed =
      run ("[register_notation = false, " ^ channel_options ^ "]") "semantic_suppressed"
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
    fun typed name typ = "[" ^ name ^ " = " ^ cartouche typ ^ "]"
    val _ = reject "semantic-removed-type" "unknown uRust command option \"type\""
      (typed "type" semantic_type) item
    val _ = reject "semantic-removed-type-malformed" "unknown uRust command option \"type\""
      "[type = [broken]]" item
    val _ = reject "semantic-omitted-nonunit" "Type unification failed"
      "" "fn SemanticMismatch(value: u64) { value }"
    val _ = reject "semantic-omitted-nonunit-channels" "Type unification failed"
      option "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) { value }"
    val _ = reject "semantic-explicit-unit-mismatch" "Type unification failed"
      "" "fn SemanticMismatch(value: u64) -> () { value }"
    val _ = reject "semantic-return-mismatch" "Type unification failed"
      option "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) -> bool { value }"
    val _ = reject "semantic-parameter-mismatch" "Type unification failed"
      option "fn SemanticMismatch(value: bool) -> \<tau>\<open>nat\<close> { value }"
    val _ = reject "semantic-incompatible-sort" "Type unification failed"
      (typed "state" "'a::cancellative_sepalg")
      "fn SemanticMismatch(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>nat\<close> { value }"
    val _ = reject "semantic-body-mismatch" "Type unification failed"
      option "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { true }"
    val _ = reject "semantic-state-mismatch" "Type unification failed"
      (typed "state" "bool")
      "fn SemanticMismatch() -> \<tau>\<open>nat\<close> { \<epsilon>\<open>get (\<lambda>s::nat. s)\<close> }"
    val _ = reject "semantic-abort-mismatch" "Type unification failed"
      (typed "abort" "unit")
      "fn SemanticMismatch() { \<epsilon>\<open>abort (CustomAbort True)\<close> }"
    val fixed_body =
      "fn SemanticMismatch() { \<epsilon>\<open>literal () :: " ^
      "(unit, unit, unit, bool, nat prompt, unit prompt_output) expression\<close> }"
    val _ = reject "semantic-input-mismatch" "Type unification failed"
      (typed "input" "bool") fixed_body
    val _ = reject "semantic-output-mismatch" "Type unification failed"
      (typed "output" "bool") fixed_body
    val _ = reject "semantic-shared-sort-concrete" "Type unification failed"
      (typed "abort" "'a::cancellative_sepalg")
      "fn SemanticMismatch(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { \<llangle>0::nat\<rrangle> }"
    val _ =
      List.app (fn name =>
        (reject ("semantic-duplicate-" ^ name) "duplicate uRust command option"
          ("[" ^ name ^ " = " ^ cartouche "unit" ^ ", " ^ name ^ " = " ^ cartouche "unit" ^ "]") item;
         reject ("semantic-missing-" ^ name) "expects a HOL type" ("[" ^ name ^ "]") item;
         reject ("semantic-wrong-" ^ name) "expects a HOL type" ("[" ^ name ^ " = true]") item;
         reject ("semantic-integer-" ^ name) "expects a HOL type" ("[" ^ name ^ " = 1]") item;
         reject ("semantic-malformed-" ^ name) "Failed to parse type"
           (typed name "unit \<Rightarrow>") item))
        ["state", "abort", "input", "output"]
    val _ = reject_text "semantic-rigid-locale" "Type unification failed"
      ("context semantic_type_locale begin\n" ^
        command (typed "state" "'s")
          "semantic_failure"
          "fn SemanticMismatch() { \<epsilon>\<open>put (\<lambda>_::unit. ())\<close> }")
  in val _ = () end
\<close>

end
