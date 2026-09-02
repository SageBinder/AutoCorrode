theory Micro_Rust_Parser_Command
  imports
    Micro_Rust_Diagnostics
    Micro_Rust_Matcher_Normalize
    Micro_Rust_Translate
  keywords
    "urust_expr" :: thy_decl
    and "urust_expr_with_check" :: thy_decl
    and "urust_expr_with_check'" :: thy_decl
begin

section\<open> The command \<close>

named_theorems urust_parser_definitions

text\<open>
\<open>urust_expr NAME src\<close> parses, elaborates, checks once, and defines \<open>NAME\<close>.
It adds no attributes, keeping generated definitions out of the global simp set.

\<open>urust_expr_with_check NAME src\<close> additionally checks the resulting definition
against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend by definition unfolding and
\<open>refl\<close>, and records the theorem as \<open>NAME_conformance\<close>.

\<open>urust_expr_with_check' NAME new_src old_term\<close> performs the same check with
\<open>new_src\<close> sent to the new parser and the explicit
\<open>\<lbrakk>old_src\<rbrakk>\<close> in \<open>old_term\<close> sent to the existing frontend.

Checked commands use a saturating compatibility analysis with a hard boundary of 256 predicted
legacy copies and 256 times the linear matcher-node count. Forms above either boundary remain
available through \<open>urust_expr\<close>, but checked commands reject them before invoking the old
frontend.
\<close>
ML\<open>
structure URust_Inventory =
struct
  datatype rejection_tag = Fidelity | Divergent | Audit

  datatype category =
      Plain_Definition
    | Same_Source_Conformance
    | Explicit_Old_Conformance
    | Dual_Frontend_Rejection
    | New_Only_Rejection of rejection_tag
    | Old_Frontend_Rejection

  type entry =
    {category: category,
     theory_name: string,
     position: Position.T}

  structure Data = Theory_Data
  (
    type T = entry Symtab.table
    val empty = Symtab.empty
    fun merge data = Symtab.merge (K true) data
  )

  type counts =
    {plain: int,
     same_source: int,
     explicit_old: int,
     dual_rejection: int,
     new_divergent: int,
     new_audit: int,
     old_rejection: int}

  val zero_counts : counts =
    {plain = 0,
     same_source = 0,
     explicit_old = 0,
     dual_rejection = 0,
     new_divergent = 0,
     new_audit = 0,
     old_rejection = 0}

  fun add_category Plain_Definition
        {plain, same_source, explicit_old, dual_rejection,
         new_divergent, new_audit, old_rejection} =
        {plain = plain + 1,
         same_source = same_source,
         explicit_old = explicit_old,
         dual_rejection = dual_rejection,
         new_divergent = new_divergent,
         new_audit = new_audit,
         old_rejection = old_rejection}
    | add_category Same_Source_Conformance
        {plain, same_source, explicit_old, dual_rejection,
         new_divergent, new_audit, old_rejection} =
        {plain = plain,
         same_source = same_source + 1,
         explicit_old = explicit_old,
         dual_rejection = dual_rejection,
         new_divergent = new_divergent,
         new_audit = new_audit,
         old_rejection = old_rejection}
    | add_category Explicit_Old_Conformance
        {plain, same_source, explicit_old, dual_rejection,
         new_divergent, new_audit, old_rejection} =
        {plain = plain,
         same_source = same_source,
         explicit_old = explicit_old + 1,
         dual_rejection = dual_rejection,
         new_divergent = new_divergent,
         new_audit = new_audit,
         old_rejection = old_rejection}
    | add_category Dual_Frontend_Rejection
        {plain, same_source, explicit_old, dual_rejection,
         new_divergent, new_audit, old_rejection} =
        {plain = plain,
         same_source = same_source,
         explicit_old = explicit_old,
         dual_rejection = dual_rejection + 1,
         new_divergent = new_divergent,
         new_audit = new_audit,
         old_rejection = old_rejection}
    | add_category (New_Only_Rejection Divergent)
        {plain, same_source, explicit_old, dual_rejection,
         new_divergent, new_audit, old_rejection} =
        {plain = plain,
         same_source = same_source,
         explicit_old = explicit_old,
         dual_rejection = dual_rejection,
         new_divergent = new_divergent + 1,
         new_audit = new_audit,
         old_rejection = old_rejection}
    | add_category (New_Only_Rejection Audit)
        {plain, same_source, explicit_old, dual_rejection,
         new_divergent, new_audit, old_rejection} =
        {plain = plain,
         same_source = same_source,
         explicit_old = explicit_old,
         dual_rejection = dual_rejection,
         new_divergent = new_divergent,
         new_audit = new_audit + 1,
         old_rejection = old_rejection}
    | add_category (New_Only_Rejection Fidelity) _ =
        error "uRust inventory: fidelity rejection must check both frontends"
    | add_category Old_Frontend_Rejection
        {plain, same_source, explicit_old, dual_rejection,
         new_divergent, new_audit, old_rejection} =
        {plain = plain,
         same_source = same_source,
         explicit_old = explicit_old,
         dual_rejection = dual_rejection,
         new_divergent = new_divergent,
         new_audit = new_audit,
         old_rejection = old_rejection + 1}

  fun entries thy = map #2 (Symtab.dest (Data.get thy))

  fun counts_matching predicate thy =
    fold
      (fn entry =>
        if predicate entry
        then add_category (#category entry)
        else I)
      (entries thy) zero_counts

  fun counts thy = counts_matching (K true) thy

  fun counts_for_theory theory_name =
    counts_matching (fn entry => #theory_name entry = theory_name)

  fun record category position lthy =
    let
      val theory_name =
        Context.theory_name {long = false} (Proof_Context.theory_of lthy)
      val entry =
        {category = category,
         theory_name = theory_name,
         position = position}
      val key = serial_string ()
    in
      Local_Theory.background_theory
        (Data.map (Symtab.update_new (key, entry))) lthy
    end

  fun string_of_counts
      {plain, same_source, explicit_old, dual_rejection,
       new_divergent, new_audit, old_rejection} =
    "plain=" ^ string_of_int plain ^
    ", same-source=" ^ string_of_int same_source ^
    ", explicit-old=" ^ string_of_int explicit_old ^
    ", dual-rejection=" ^ string_of_int dual_rejection ^
    ", new-divergent=" ^ string_of_int new_divergent ^
    ", new-audit=" ^ string_of_int new_audit ^
    ", old-rejection=" ^ string_of_int old_rejection

  fun equal_counts
      ({plain = plain1, same_source = same_source1,
        explicit_old = explicit_old1, dual_rejection = dual_rejection1,
        new_divergent = new_divergent1, new_audit = new_audit1,
        old_rejection = old_rejection1} : counts)
      ({plain = plain2, same_source = same_source2,
        explicit_old = explicit_old2, dual_rejection = dual_rejection2,
        new_divergent = new_divergent2, new_audit = new_audit2,
        old_rejection = old_rejection2} : counts) =
    plain1 = plain2 andalso
    same_source1 = same_source2 andalso
    explicit_old1 = explicit_old2 andalso
    dual_rejection1 = dual_rejection2 andalso
    new_divergent1 = new_divergent2 andalso
    new_audit1 = new_audit2 andalso
    old_rejection1 = old_rejection2

  fun assert_theory_counts theory_name expected thy =
    let
      val actual = counts_for_theory theory_name thy
    in
      if equal_counts expected actual then ()
      else
        error
          ("uRust inventory mismatch for theory " ^ quote theory_name ^
            "\nexpected: " ^ string_of_counts expected ^
            "\nactual:   " ^ string_of_counts actual)
    end
end

structure URust_Compatibility_Inventory =
struct
  type entry =
    {theory_name: string,
     checked_size: int,
     normalized_size: int,
     position: Position.T}

  structure Data = Theory_Data
  (
    type T = entry Symtab.table
    val empty = Symtab.empty
    fun merge data = Symtab.merge (K true) data
  )

  fun entries thy = map #2 (Symtab.dest (Data.get thy))

  fun record checked_size normalized_size position lthy =
    let
      val theory_name =
        Context.theory_name {long = false} (Proof_Context.theory_of lthy)
      val entry =
        {theory_name = theory_name,
         checked_size = checked_size,
         normalized_size = normalized_size,
         position = position}
    in
      Local_Theory.background_theory
        (Data.map (Symtab.update_new (serial_string (), entry))) lthy
    end
end

(* THE pipeline, exported: every uRust command runs source through exactly this function, so the
   definition commands (`urust_expr`, `urust_expr_with_check`, `urust_expr_with_check'`) and the
   negative harness (`urust_expr_rejects`, Micro_Rust_Parser_Negative_Conformance) can never drift on
   WHAT they exercise -- only on how they interpret success/failure. Raises (positioned) on any
   rejection: lexer (URust_Err.lex_error), yacc (parse_source's print_error), elaborator, or check_term.
   ONLY `parse_source` touches the Isabelle_lex_yacc global refs, so only it is serialized; elaboration and
   check_term are pure w.r.t. those, and holding the lock across them would serialize the (slower)
   type-checking of every uRust command theory-wide. *)
datatype checked_urust =
  Checked_URust of
    {term: term,
     translation: URust_Translate.result}

fun elab_urust_result lthy source =
  (case
      (Parser_Utils.with_parser_lock
        (fn () => URust_Diagnostics.parse_source lthy source)) of
     SOME ast =>
       let
         val translation =
           URust_Translate.make_result lthy ast
         val checked =
           Syntax.check_term lthy
             (URust_Translate.result_term translation)
       in
         Checked_URust
           {term = checked,
            translation = translation}
       end
   | NONE => error ("urust_expr: empty expression" ^ Position.here (Input.pos_of source)))

fun elab_urust lthy source =
  let val Checked_URust {term, ...} =
    elab_urust_result lthy source
  in term end

fun define_urust_result (binding, source) lthy =
  let
    val Checked_URust {term, translation} =
      elab_urust_result lthy source
    val (definition, lthy') =
      Local_Theory.define
        ((binding, NoSyn),
          ((Thm.def_binding binding,
            [Code.singleton_default_equation_attrib,
             Attrib.internal \<^here>
               (K (Named_Theorems.add
                 \<^named_theorems>\<open>urust_parser_definitions\<close>))]),
           term)) lthy
  in ((definition, translation), lthy') end

fun define_urust (binding, source) lthy =
  let
    val (_, lthy') =
      define_urust_result (binding, source) lthy
  in
    URust_Inventory.record
      URust_Inventory.Plain_Definition (Input.pos_of source) lthy'
  end

fun old_frontend_source source = "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"

val legacy_normalization_factor = 256

fun with_legacy_compatible translation action =
  if URust_Translate.legacy_compatible translation then action ()
  else
    let
      val (message, pos) =
        URust_Translate.compatibility_diagnostic translation
    in
      error
        ("urust_expr_with_check: scalable matcher form is not available" ^
          " to the legacy frontend: " ^ message ^
          "; use `urust_expr` for the scalable definition" ^
          Position.here pos)
    end

fun define_urust_with_frontend_check
    category (binding, new_source, old_frontend_source) lthy =
  let
    val (((lhs, (_, def_thm)), translation), lthy') =
      define_urust_result (binding, new_source) lthy
    val old_frontend =
      with_legacy_compatible translation
        (fn () => Syntax.parse_term lthy' old_frontend_source)
    val equality =
      Syntax.check_term lthy'
        (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ old_frontend)
    val checked_rhs =
      Thm.term_of (Thm.rhs_of def_thm)
    val (_, normalized_legacy_rhs) =
      HOLogic.dest_eq equality
    val checked_size = Term.size_of_term checked_rhs
    val normalized_size =
      Term.size_of_term normalized_legacy_rhs
    val normalization_limit =
      legacy_normalization_factor * checked_size + 8192
    val _ =
      if normalized_size <= normalization_limit then ()
      else
        error
          ("urust_expr_with_check: bounded legacy normalization size " ^
            string_of_int normalized_size ^ " exceeds " ^
            string_of_int normalization_limit ^
            Position.here (Input.pos_of new_source))
    val conformance =
      Goal.prove lthy' [] [] (HOLogic.mk_Trueprop equality)
        (fn {context = ctxt, ...} =>
          let
            val matcher_simps =
              ctxt addsimps
                (@{thms micro_rust_simps} @
                 @{thms
                   urust_lazy_conditional_const
                   urust_matcher_fail_def
                   urust_matcher_succeed_def
                   urust_matcher_run_fail
                   urust_matcher_run_succeed
                   urust_matcher_run_guarded_fail
                   urust_matcher_run_guarded_succeed
                   urust_matcher_run_value_fail
                   urust_matcher_run_value_succeed
                   urust_matcher_run_value_map
                   urust_matcher_run_value_test
                   urust_matcher_run_guarded_value_fail
                   urust_matcher_run_guarded_value_succeed
                   two_armed_conditional_def
                   sequence_def
                   bind_literal_unit
                   bind_literal_unit2
                   evaluate_conjunction_literal
                   evaluate_eq_literal
                   evaluate_ge_literal
                   evaluate_gt_literal
                   evaluate_le_literal
                   evaluate_lt_literal
                   evaluate_pure_if})
              |> Simplifier.del_cong @{thm if_weak_cong}
              |> Simplifier.add_cong @{thm if_cong}
            val semantic_simps =
              matcher_simps addsimps
                @{thms
                  Core_Expression.bind.simps
                  urust_eq_def
                  bindlift2_def}
            fun case_splits goal =
              let
                fun collect (Const (name, _)) splits =
                      (case Ctr_Sugar.ctr_sugar_of_case ctxt name of
                         SOME sugar =>
                           insert Thm.eq_thm_prop (#split sugar) splits
                       | NONE => splits)
                  | collect _ splits = splits
              in Term.fold_aterms collect goal [] end
            fun case_congruences goal =
              let
                fun collect (Const (name, _)) congruences =
                      (case Ctr_Sugar.ctr_sugar_of_case ctxt name of
                         SOME sugar =>
                           insert Thm.eq_thm_prop
                             (#case_cong sugar) congruences
                       | NONE => congruences)
                  | collect _ congruences = congruences
              in Term.fold_aterms collect goal [] end
            fun simp_cases simps index =
              SUBGOAL
                (fn (goal, _) =>
                  let
                    val splits = case_splits goal
                    val congruences = case_congruences goal
                  in
                    asm_full_simp_tac
                      (simps
                        |> fold Simplifier.add_cong congruences
                        |> fold Splitter.add_split_bang splits)
                      index
                  end)
                index
            fun finish_matcher_goal index =
              URust_Matcher_Normalize.normalize_tac ctxt index THEN
              (TRY
                (resolve_tac ctxt [@{thm expression_eqI2}] index THEN
                 force_tac semantic_simps index) THEN
               TRY (force_tac matcher_simps index))
          in
            Local_Defs.unfold_tac ctxt [def_thm] THEN
            (resolve_tac ctxt [@{thm refl}] 1 ORELSE
              (URust_Matcher_Normalize.normalize_tac ctxt 1 THEN
                TRY
                  (simp_cases matcher_simps 1 THEN
                   ALLGOALS finish_matcher_goal)))
          end)
    val (_, lthy'') =
      Local_Theory.note
        ((Binding.suffix_name "_conformance" binding, []), [conformance]) lthy'
    val lthy''' =
      URust_Compatibility_Inventory.record
        checked_size normalized_size (Input.pos_of new_source) lthy''
  in
    URust_Inventory.record category (Input.pos_of new_source) lthy'''
  end

fun define_urust_with_check (binding, source) =
  define_urust_with_frontend_check
    URust_Inventory.Same_Source_Conformance
    (binding, source, old_frontend_source source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr\<close>
          "Parse a uRust expression and define it as a HOL constant"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check\<close>
          "Define a uRust expression and check it against the existing frontend by refl"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust_with_check)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check'\<close>
          "Define a uRust expression and check it against an explicit existing-frontend term by refl"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) --
            Parse.term >>
            (fn ((binding, new_source), old_frontend_source) =>
              define_urust_with_frontend_check
                URust_Inventory.Explicit_Old_Conformance
                (binding, new_source, old_frontend_source)))
\<close>

end
