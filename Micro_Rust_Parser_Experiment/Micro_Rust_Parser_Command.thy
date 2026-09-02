theory Micro_Rust_Parser_Command
  imports
    Micro_Rust_Diagnostics
    Micro_Rust_Translate
  keywords
    "urust_expr" :: thy_decl
    and "urust_expr_with_check" :: thy_decl
    and "urust_expr_with_check'" :: thy_decl
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr NAME src\<close> parses, elaborates, checks once, and defines \<open>NAME\<close>.
It adds no attributes, keeping generated definitions out of the global simp set.

\<open>urust_expr_with_check NAME src\<close> additionally checks the resulting definition
against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend by definition unfolding and
\<open>refl\<close>, and records the theorem as \<open>NAME_conformance\<close>.

\<open>urust_expr_with_check' NAME new_src old_term\<close> performs the same check with
\<open>new_src\<close> sent to the new parser and the explicit
\<open>\<lbrakk>old_src\<rbrakk>\<close> in \<open>old_term\<close> sent to the existing frontend.
\<close>
ML\<open>
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
          ((Thm.def_binding binding, []), term)) lthy
  in ((definition, translation), lthy') end

fun define_urust args lthy = snd (define_urust_result args lthy)

fun old_frontend_source source = "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"

val legacy_normalization_factor = 256

fun define_urust_with_frontend_check (binding, new_source, old_frontend_source) lthy =
  let
    val (((lhs, (_, def_thm)), translation), lthy') =
      define_urust_result (binding, new_source) lthy
    val _ =
      if URust_Translate.legacy_compatible translation then ()
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
    val old_frontend =
      Syntax.parse_term lthy' old_frontend_source
    val equality =
      Syntax.check_term lthy'
        (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ old_frontend)
    val checked_rhs =
      Thm.term_of (Thm.rhs_of def_thm)
    val checked_size = Term.size_of_term checked_rhs
    val legacy_size = Term.size_of_term old_frontend
    val normalization_limit =
      legacy_normalization_factor * checked_size + 8192
    val _ =
      if legacy_size <= normalization_limit then ()
      else
        error
          ("urust_expr_with_check: bounded legacy normalization size " ^
            string_of_int legacy_size ^ " exceeds " ^
            string_of_int normalization_limit ^
            Position.here (Input.pos_of new_source))
    val conformance =
      Goal.prove lthy' [] [] (HOLogic.mk_Trueprop equality)
        (fn {context = ctxt, ...} =>
          let
            val matcher_definitions =
              @{thms
                urust_matcher_fail_def
                urust_matcher_succeed_def
                urust_matcher_choice_def
                urust_matcher_map_def
                urust_matcher_product_def
                urust_matcher_test_def
                urust_matcher_lift_def
                urust_matcher_destructure_def
                urust_matcher_run_def
                urust_matcher_run_guarded_def
                urust_matcher_run_value_def
                urust_matcher_run_guarded_value_def}
            val matcher_simps =
              ctxt addsimps
                (@{thms micro_rust_simps} @
                 @{thms
                   bind_literal_unit
                   bind_literal_unit2
                   evaluate_conjunction_literal
                   evaluate_eq_literal
                   evaluate_ge_literal
                   evaluate_gt_literal
                   evaluate_le_literal
                   evaluate_lt_literal
                   evaluate_pure_if})
            val unfold_matchers =
              Local_Defs.unfold_tac ctxt matcher_definitions
            val semantic_simps =
              matcher_simps addsimps
                @{thms
                  two_armed_conditional_def
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
              TRY
                (resolve_tac ctxt [@{thm expression_eqI2}] index THEN
                 force_tac semantic_simps index) THEN
              TRY (force_tac matcher_simps index)
          in
            Local_Defs.unfold_tac ctxt [def_thm] THEN
            (resolve_tac ctxt [@{thm refl}] 1 ORELSE
              (unfold_matchers THEN
                simp_cases matcher_simps 1 THEN
                ALLGOALS finish_matcher_goal))
          end)
    val (_, lthy'') =
      Local_Theory.note
        ((Binding.suffix_name "_conformance" binding, []), [conformance]) lthy'
  in lthy'' end

fun define_urust_with_check (binding, source) =
  define_urust_with_frontend_check (binding, source, old_frontend_source source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr\<close>
          "Parse a uRust expression and define it as a HOL constant"
          (Parse.binding -- Parse.input Parse.cartouche >> define_urust)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check\<close>
          "Define a uRust expression and check it against the existing frontend by refl"
          (Parse.binding -- Parse.input Parse.cartouche >> define_urust_with_check)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check'\<close>
          "Define a uRust expression and check it against an explicit existing-frontend term by refl"
          (Parse.binding -- Parse.input Parse.cartouche -- Parse.term >>
            (fn ((binding, new_source), old_frontend_source) =>
              define_urust_with_frontend_check (binding, new_source, old_frontend_source)))
\<close>

end
