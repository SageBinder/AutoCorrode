theory Parser_Function_Channel_Default_Tests
  imports
    Parser_Function_Semantic_Type_Tests
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = false]]
declare [[urust_verbosity = 0]]

text\<open>
The scoped attributes \<open>urust_state\<close>, \<open>urust_abort\<close>, \<open>urust_input\<close> and \<open>urust_output\<close>
supply the channel types of every later function that omits the corresponding option. An inline
option or \<omega> annotation overrides one channel; an exact \<open>_\<close> removes a default. Each inheriting
function rereads the default with its own signature, exactly as if the option were written inline.
\<close>

section\<open> Inherited and overridden channels \<close>

context
  notes [[urust_state = \<open>'s::cancellative_sepalg\<close>, urust_abort = \<open>bool\<close>,
          urust_input = \<open>nat prompt\<close>, urust_output = \<open>unit prompt_output\<close>]]
begin

urust_fn default_identity
  \<open> fn DefaultIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn [abort = \<open>unit\<close>] default_abort_override
  \<open> fn DefaultAbortOverride(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn default_fixed_caller
  \<open> fn DefaultFixedCaller(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { DefaultIdentity(value) } \<close>

end

urust_fn default_outside_scope
  \<open> fn DefaultOutsideScope(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun same_type label (name, expected) =
      require (label ^ ": " ^ name)
        (Sign.typ_equiv (Proof_Context.theory_of ctxt)
          (declared_type ctxt name, Logic.varifyT_global expected))
    val _ =
      same_type "default differs from the inline channels"
        ("default_identity", Logic.unvarifyT_global (declared_type ctxt "semantic_identity"))
    val _ =
      same_type "override replaced more than its channel"
        ("default_abort_override",
         \<^typ>\<open>nat \<Rightarrow>
           ('s::cancellative_sepalg, nat, unit, nat prompt, unit prompt_output) function_body\<close>)
    val (state, _, abort, input, output) = channels (declared_type ctxt "default_outside_scope")
    val _ = independent "default escaped its context block" [state, abort, input, output]

    (* The readable examples in Parser_Function_Tests. *)
    val _ =
      same_type "scoped example differs from the inline channels"
        ("scoped_identity", Logic.unvarifyT_global (declared_type ctxt "semantic_identity"))
    val _ =
      same_type "scoped example override replaced more than its channel"
        ("scoped_unit_abort_identity", Logic.unvarifyT_global (declared_type ctxt "default_abort_override"))
    val (state, _, _, _, _) = channels (declared_type ctxt "scoped_any_state_identity")
    val _ = require "scoped example hole kept the state default"
      (generic state andalso
        not (Sign.subsort (Proof_Context.theory_of ctxt)
          (sort_of state, \<^sort>\<open>cancellative_sepalg\<close>)))
  in val _ = () end
\<close>

lemma default_identity_equivalent:
  \<open>default_identity = semantic_identity\<close>
  unfolding default_identity_def semantic_identity_def by (rule refl)

section\<open> Members of an item list \<close>

context
  notes [[urust_state = \<open>'s::cancellative_sepalg\<close>, urust_abort = \<open>bool\<close>]]
begin

urust \<open>
  fn DefaultChunkInherited(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }

  \<omega>\<open>abort = \<open>unit\<close>\<close>
  fn DefaultChunkOverride(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }
\<close>

end

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun check name expected_abort =
      let
        val (state, _, abort, input, output) = channels (declared_type ctxt name)
      in
        require (name ^ ": inherited state was lost")
          (generic state andalso
            Sign.subsort (Proof_Context.theory_of ctxt)
              (sort_of state, \<^sort>\<open>cancellative_sepalg\<close>));
        require (name ^ ": wrong abort channel") (abort = expected_abort);
        independent (name ^ ": unset channels became constrained") [state, input, output]
      end
    val _ = check "default_chunk_inherited" \<^typ>\<open>bool\<close>
    val _ = check "default_chunk_override" \<^typ>\<open>unit\<close>
  in val _ = () end
\<close>

section\<open> Equivalence, precedence, removal and sharing \<close>

ML\<open>
structure Parser_Channel_Default_Test =
struct
  open Parser_Function_Regression_Test

  val channel_names = ["state", "abort", "input", "output"]

  fun subsets [] = [[]]
    | subsets (entry :: rest) =
        let val smaller = subsets rest in smaller @ map (cons entry) smaller end

  fun inline_options [] = ""
    | inline_options entries =
        "[" ^ commas (map (fn (name, typ) => name ^ " = " ^ cartouche typ) entries) ^ "]"

  fun declare_defaults [] = ""
    | declare_defaults entries =
        "declare [[" ^
          commas (map (fn (name, typ) => "urust_" ^ name ^ " = " ^ cartouche typ) entries) ^
          "]]\n"

  fun context_after base label text = run_from base label text |> Toplevel.context_of

  fun same_scheme label (context, name) expected =
    require label
      (Sign.typ_equiv (Proof_Context.theory_of context)
        (declared_type context name, Logic.varifyT_global expected))

  fun file_markup label =
    exists (fn (_, properties) => Properties.get properties Markup.fileN = SOME label)
end
\<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val defaults =
      [("state", "'s::cancellative_sepalg"), ("abort", "bool"),
       ("input", "nat prompt"), ("output", "unit prompt_output")]
    val overrides =
      [("state", "unit"), ("abort", "nat"), ("input", "bool prompt"), ("output", "nat prompt_output")]
    val item = "fn DefaultCombination(value: \<tau>" ^ cartouche "nat" ^ ") { () }"
    fun expected selected fallback =
      let
        fun channel name = the_default (fallback name) (AList.lookup (op =) selected name)
      in
        Syntax.read_typ ctxt
          ("nat \<Rightarrow> (" ^
            commas [channel "state", "unit", channel "abort", channel "input", channel "output"] ^
            ") function_body")
      end
    fun label prefix selected = space_implode "-" (prefix :: map fst selected)

    (* Scoped defaults agree exactly with the same inline options. *)
    fun inherit selected =
      let
        val inherited =
          context_after base (label "default-inherit" selected)
            (declare_defaults selected ^ command "" "default_combination" item)
        val inline =
          context_after base (label "default-inline" selected)
            (command (inline_options selected) "default_combination" item)
        val _ =
          same_scheme ("inherited channels changed the complete type: " ^ inline_options selected)
            (inherited, "default_combination")
            (expected selected (fn name => "'" ^ name))
      in
        require "inherited channels changed the definition"
          (Term.aconv (rhs inherited "default_combination", rhs inline "default_combination"))
      end
    val _ = List.app inherit (subsets defaults)

    (* Each inline option replaces exactly its own channel. *)
    fun override selected =
      same_scheme ("override changed another channel: " ^ inline_options selected)
        (context_after base (label "default-override" selected)
          (declare_defaults defaults ^
            command (inline_options selected) "default_combination" item),
         "default_combination")
        (expected selected (the o AList.lookup (op =) defaults))
    val _ = List.app override (subsets overrides)

    (* A hole option, a removed default and a nested removal all mean an omitted channel. *)
    fun removal name =
      let
        val remaining = filter_out (fn (channel, _) => channel = name) defaults
        val reference =
          context_after base ("default-reference-" ^ name)
            (declare_defaults remaining ^ command "" "default_combination" item)
        fun agrees how context =
          same_scheme (how ^ " " ^ name ^ " differs from an omitted channel")
            (context, "default_combination")
            (Logic.unvarifyT_global (declared_type reference "default_combination"))
        val _ =
          agrees "inline hole"
            (context_after base ("default-hole-" ^ name)
              (declare_defaults defaults ^
                command (inline_options [(name, "_")]) "default_combination" item))
        val _ =
          agrees "removed default"
            (context_after base ("default-removed-" ^ name)
              (declare_defaults defaults ^ declare_defaults [(name, "_")] ^
                command "" "default_combination" item))
        val nested =
          context_after base ("default-nested-" ^ name)
            (declare_defaults defaults ^
              "context notes [[urust_" ^ name ^ " = " ^ cartouche "_" ^ "]] begin\n" ^
              command "" "default_combination" item ^ "\nend\n" ^
              command "" "default_restored"
                ("fn DefaultRestored(value: \<tau>" ^ cartouche "nat" ^ ") { () }"))
        val _ = agrees "nested removal" nested
      in
        same_scheme ("nested removal did not restore the outer " ^ name ^ " default")
          (nested, "default_restored") (expected [] (the o AList.lookup (op =) defaults))
      end
    val _ = List.app removal channel_names

    val sorted_holes =
      context_after base "default-sorted-holes"
        (declare_defaults [("input", "_::finite"), ("output", "_::finite")] ^
          command "" "default_sorted_holes" item)
    val (_, _, _, input, output) = channels (declared_type sorted_holes "default_sorted_holes")
    val _ = independent "sorted hole defaults became identified" [input, output]
    val _ =
      List.app (fn typ =>
        require "sorted hole default lost its sort"
          (Sign.subsort (Proof_Context.theory_of sorted_holes) (sort_of typ, \<^sort>\<open>finite\<close>)))
        [input, output]

    val later = context_after base "default-later-duplicate"
      ("declare [[urust_abort = " ^ cartouche "bool" ^ ", urust_abort = " ^ cartouche "unit" ^
        "]]\n" ^ command "" "default_combination" item)
    val (_, _, abort, _, _) = channels (declared_type later "default_combination")
    val _ = require "the later duplicate default did not win" (abort = \<^typ>\<open>unit\<close>)
  in val _ = () end
\<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>

    (* Named variables of defaults, inline options and HOL escapes share one environment. *)
    val escape_sharing =
      context_after base "default-escape-sharing"
        (declare_defaults [("abort", "'value::linorder")] ^
          command "" "default_sharing"
            ("fn DefaultSharing(value: \<tau>" ^ cartouche "'value" ^ ") -> \<tau>" ^
              cartouche "'value" ^ " { value }"))
    val typ = declared_type escape_sharing "default_sharing"
    val (state, result, abort, input, output) = channels typ
    val _ = require "default and escape names did not share"
      (abort = result andalso binder_types typ = [result])
    val _ = require "default sort was lost"
      (Sign.subsort (Proof_Context.theory_of escape_sharing) (sort_of abort, \<^sort>\<open>linorder\<close>))
    val _ = independent "unrelated channels were captured" [state, result, input, output]

    val option_sharing =
      context_after base "default-option-sharing"
        (declare_defaults [("input", "'channel")] ^
          command (inline_options [("output", "'channel")]) "default_sharing"
            "fn DefaultSharing() {}")
    val (_, _, _, input, output) = channels (declared_type option_sharing "default_sharing")
    val _ = require "default and inline option names did not share" (input = output)

    (* Every inheriting function reads its own fresh variables. *)
    val fresh =
      context_after base "default-fresh-names"
        (declare_defaults [("state", "'s"), ("abort", "'s")] ^
          command "" "default_first" "fn DefaultFirst() {}" ^ "\n" ^
          command "" "default_second"
            ("fn DefaultSecond(callback: \<tau>" ^
              cartouche "('s, unit, 's, unit, unit) function_body" ^ ") {}"))
    val (first_state, _, first_abort, _, _) = channels (declared_type fresh "default_first")
    val _ = require "one default name did not share across channels" (first_state = first_abort)
    val second = declared_type fresh "default_second"
    val (second_state, _, _, _, _) = channels second
    val (callback_state, _, _, _, _) = channels (hd (binder_types second))
    val _ = require "default name did not share with a later escape" (second_state = callback_state)
  in val _ = () end
\<close>

section\<open> Context scoping, locales and interpretation \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    fun abort_of context name =
      let val (_, _, abort, _, _) = channels (declared_type context name) in abort end

    (* Theory declarations persist; nested blocks shadow and then restore. *)
    val scoped =
      context_after base "default-scoping"
        (declare_defaults [("abort", "bool")] ^
          command "" "default_first" "fn DefaultFirst() {}" ^ "\n" ^
          "context notes [[urust_abort = " ^ cartouche "nat" ^ "]] begin\n" ^
          "context notes [[urust_abort = " ^ cartouche "unit" ^ "]] begin\n" ^
          command "" "default_inner" "fn DefaultInner() {}" ^ "\nend\n" ^
          command "" "default_middle" "fn DefaultMiddle() {}" ^ "\nend\n" ^
          command "" "default_second" "fn DefaultSecond() {}")
    val _ =
      List.app (fn (name, expected) =>
        require ("wrong scoped abort for " ^ name) (abort_of scoped name = expected))
        [("default_first", \<^typ>\<open>bool\<close>), ("default_inner", \<^typ>\<open>unit\<close>),
         ("default_middle", \<^typ>\<open>nat\<close>), ("default_second", \<^typ>\<open>bool\<close>)]

    val locale_text =
      "locale default_scope_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
      "\nbegin\n" ^ declare_defaults [("state", "'s")]
    fun locale_function name =
      command "[register_notation = false]" name
        ("fn " ^ name ^ "() -> () { \<llangle>let _ = seed in ()\<rrangle> }")
    fun local_state context name =
      let val (state, _, _, _, _) = channels (fastype_of (rhs context name)) in state end
    val rigid = \<^typ>\<open>'s::cancellative_sepalg\<close>

    (* A locale default reads the locale's fixed variable, stays in the locale and returns with
       it. A theory bundle opened in the locale is captured by the same rigid variable. *)
    val inside =
      context_after base "default-locale-inside" (locale_text ^ locale_function "default_inside")
    val _ = require "locale default state became flexible" (local_state inside "default_inside" = rigid)
    val reentered =
      context_after base "default-locale-reentered"
        (locale_text ^ locale_function "default_inside" ^ "\nend\n" ^
          command "" "default_outside" "fn DefaultOutside() {}" ^ "\n" ^
          "context default_scope_locale begin\n" ^ locale_function "default_reentered")
    val _ = require "re-entered locale lost its default"
      (local_state reentered "default_reentered" = rigid)
    val (outside, _, _, _, _) =
      channels (declared_type (Proof_Context.init_global (Proof_Context.theory_of reentered))
        "default_outside")
    val _ = independent "locale default escaped to the theory" [outside]
    val bundled =
      context_after base "default-locale-bundle"
        ("bundle default_scope_bundle = [[urust_state = " ^ cartouche "'s" ^ "]]\n" ^
          "locale default_scope_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
          "\ncontext default_scope_locale opening default_scope_bundle begin\n" ^
          locale_function "default_bundled")
    val _ = require "bundled default was not captured by the locale variable"
      (local_state bundled "default_bundled" = rigid)

    (* Native locale notes replay a locale declaration into every global interpretation, both
       later and existing ones; each replay rereads the source in the interpreting theory. *)
    val interpreted =
      context_after base "default-interpretation"
        ("locale default_interpreted_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
          "\nbegin\n" ^ declare_defaults [("state", "'s"), ("abort", "bool")] ^
          locale_function "default_inside" ^ "\nend\n" ^
          "interpretation default_unit: default_interpreted_locale " ^ cartouche "()" ^ " .\n" ^
          command "" "default_after_interpretation" "fn DefaultAfterInterpretation() {}")
    val (state, _, abort, _, _) = channels (declared_type interpreted "default_after_interpretation")
    val _ = require "interpretation did not replay the locale default"
      (abort = \<^typ>\<open>bool\<close> andalso generic state)
    val (instantiated, _, _, _, _) =
      channels (declared_type interpreted "default_unit.default_inside")
    val _ = require "interpreted function lost its instantiated state"
      (instantiated = \<^typ>\<open>unit\<close>)
    val existing =
      context_after base "default-existing-interpretation"
        ("locale default_interpreted_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
          "\ninterpretation default_unit: default_interpreted_locale " ^ cartouche "()" ^ " .\n" ^
          "context default_interpreted_locale begin\n" ^ declare_defaults [("abort", "bool")] ^
          "end\n" ^
          command "" "default_after_declaration" "fn DefaultAfterDeclaration() {}")
    val _ = require "existing interpretation did not receive the locale default"
      (abort_of existing "default_after_declaration" = \<^typ>\<open>bool\<close>)
  in val _ = () end
\<close>

section\<open> Reports \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val declaration = "default-markup-declaration"

    (* The declaration reports once in its own command. Inheriting functions, item-list members
       and interpretation replays report only in their own sources. *)
    val (declared, declaration_reports) =
      Parser_Test_Reports.markup (fn () =>
        run_from base declaration
          ("locale default_markup_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
            "\nbegin\n" ^ declare_defaults [("abort", "bool"), ("output", "_::finite")] ^ "end\n" ^
            declare_defaults [("abort", "bool"), ("output", "_::finite")]))
    val _ = require "the default declaration reported no markup"
      (file_markup declaration
        (filter (fn (name, _) => name = Markup.entityN) declaration_reports))
    fun quiet label text =
      let
        val (_, reports) = Parser_Test_Reports.markup (fn () => run_from declared label text)
        val _ = require (label ^ ": captured no markup of its own") (file_markup label reports)
      in
        require (label ^ ": reported into the default declaration")
          (not (file_markup declaration reports))
      end
    val _ =
      quiet "default-markup-function"
        (command "" "default_markup" "fn DefaultMarkup(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }")
    val _ =
      quiet "default-markup-chunk"
        ("urust " ^ cartouche "fn DefaultMarkupChunk(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }")
    val _ =
      quiet "default-markup-interpretation"
        ("interpretation default_markup_unit: default_markup_locale " ^ cartouche "()" ^ " .\n" ^
          command "" "default_markup" "fn DefaultMarkup() {}")
  in val _ = () end
\<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val label = "default-markup-keyword-option"

    (* The output option is spelled like the Pure minor keyword. Inline and in an annotation it is
       reported as unhighlighted after any keyword report, so it renders as an option name. *)
    val text =
      command (inline_options [("output", "unit")]) "default_keyword_inline"
        "fn DefaultKeywordInline() {}" ^ "\n" ^
      "urust " ^
        cartouche
          ("\n  \<omega>" ^ cartouche ("output = " ^ cartouche "unit") ^
            "\n  fn DefaultKeywordAnnotated() {}\n")
    val (_, markup) = Parser_Test_Reports.markup (fn () => run_from base label text)
    (* Colour reports at one range in report order; the last one determines the rendering. *)
    fun colours position =
      markup
      |> filter (fn (name, properties) =>
          member (op =) [Markup.keyword2N, Markup.delimiterN] name andalso
            has_position properties position)
      |> map #1
    val inline = token_position text (start label) "output" 0
    val annotated =
      token_position text (start label) "output" (find_from text "output" 0 + 1)
    val _ = require "inline keyword option name was not reported as unhighlighted"
      (colours inline = [Markup.delimiterN])
    val _ = require "annotation keyword option name kept the keyword colour"
      (colours annotated = [Markup.keyword2N, Markup.delimiterN])
  in val _ = () end
\<close>

section\<open> Commands that read no channels \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val defaults =
      declare_defaults
        [("state", "unit"), ("abort", "bool"), ("input", "unit"), ("output", "unit")]
    val expression = "urust_expr default_expression " ^ cartouche "()"
    val plain = context_after base "default-expression-plain" expression
    val inherited = context_after base "default-expression-inherited" (defaults ^ expression)
    val _ = same_scheme "urust_expr inherited a function channel default"
      (inherited, "default_expression") (Logic.unvarifyT_global (declared_type plain "default_expression"))

    fun elaborate context =
      Parser_Test_Elaboration.function context
        {raw_type = ("nat \<Rightarrow> _", start "default-api-type"),
         parameters = [("value", start "default-api-parameter")],
         parameters_pos = start "default-api-parameter",
         body = source "default-api-body" "value"}
    val _ = require "the typed-body API inherited function channel defaults"
      (Term.aconv (elaborate (Toplevel.context_of base), elaborate inherited) andalso
        fastype_of (elaborate (Toplevel.context_of base)) = fastype_of (elaborate inherited))
  in val _ = () end
\<close>

section\<open> Positioned failures and rollback \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val item = "fn DefaultFailure(value: \<tau>" ^ cartouche "nat" ^ ") -> \<tau>" ^ cartouche "nat" ^
      " { value }"

    (* An inline option overrides a broken default, so recovery bypasses all four. *)
    val recovery =
      command (inline_options (map (rpair "_") channel_names)) "default_recovery" item

    fun rejected_from state label expected text =
      let
        val (result, reports) =
          Parser_Test_Reports.markup (fn () => Exn.capture (run_from state label) text)
        val diagnostic = message result
        val _ = require (label ^ ": wrong diagnostic " ^ quote diagnostic)
          (String.isSubstring expected diagnostic)
        val _ = require (label ^ ": no source position")
          (String.isSubstring label diagnostic andalso not (null (diagnostic_ranges diagnostic)))
        val _ = require (label ^ ": installed declaration markup")
          (null (declaration_definitions reports))
        val _ = ignore (run_from state (label ^ "-recovery") recovery)
      in diagnostic end
    fun reject_declaration label expected text = ignore (rejected_from base label expected text)

    (* Declaration-time failures. *)
    val _ = reject_declaration "default-malformed" "Failed to parse type"
      (declare_defaults [("state", "unit \<Rightarrow>")])
    val _ = reject_declaration "default-undefined" "Undefined type name"
      (declare_defaults [("abort", "default_missing_type")])
    val _ = reject_declaration "default-missing-value" "Bad arguments"
      "declare [[urust_input]]"
    val _ = reject_declaration "default-inline-spelling"
      "unknown uRust command option \"urust_output\""
      (command (inline_options [("urust_output", "unit")]) "default_failure" item)

    (* Signature failures cite the inheriting function and the default declaration. Body
       mismatches against the resolved type are positioned in the body, as for inline options. *)
    fun reject_use_with cites label expected defaults text =
      let
        val declaration = label ^ "-declaration"
        val declared = run_from base declaration defaults
        val diagnostic = rejected_from declared label expected text
      in
        require (label ^ ": wrong default declaration citation")
          (String.isSubstring declaration diagnostic = cites)
      end
    val reject_use = reject_use_with true
    val _ = reject_use "default-sort-clash" "Inconsistent sort constraints"
      (declare_defaults [("abort", "'value::linorder")])
      (command "" "default_failure"
        ("fn DefaultFailure(value: \<tau>" ^ cartouche "'value::cancellative_sepalg" ^ ") {}"))
    val _ = reject_use "default-hidden-type" "scoped default urust_abort"
      ("typedecl default_hidden_type\n" ^ declare_defaults [("abort", "default_hidden_type")] ^
        "hide_type default_hidden_type\n")
      (command "" "default_failure" item)
    val _ = reject_use "default-locale-capture" "Sort constraint"
      ("bundle default_capture_bundle = [[urust_state = " ^ cartouche "'s::linorder" ^ "]]\n" ^
        "locale default_capture_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
        "\n")
      ("context default_capture_locale opening default_capture_bundle begin\n" ^
        command "[register_notation = false]" "default_failure" "fn DefaultFailure() {}")
    val fixed_body =
      "fn DefaultFailure() { \<epsilon>\<open>literal () :: " ^
      "(unit, unit, unit, bool, nat prompt, unit prompt_output) expression\<close> }"
    val _ =
      List.app (fn (channel, body) =>
        reject_use_with false ("default-" ^ channel ^ "-mismatch") "Type unification failed"
          (declare_defaults [(channel, "bool")]) (command "" "default_failure" body))
        [("state", "fn DefaultFailure() -> \<tau>\<open>nat\<close> { \<epsilon>\<open>get (\<lambda>s::nat. s)\<close> }"),
         ("abort", "fn DefaultFailure() { \<epsilon>\<open>abort (CustomAbort (0::nat))\<close> }"),
         ("input", fixed_body), ("output", fixed_body)]
  in val _ = () end
\<close>

end
