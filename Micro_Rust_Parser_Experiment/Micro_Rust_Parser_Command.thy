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

text\<open>
\<open>urust_expr NAME src\<close> parses, elaborates, checks once, and defines \<open>NAME\<close>.
The standard Isabelle definition mechanism supplies one default code equation, but the command
adds no custom attributes and keeps generated definitions out of the global simp set.

\<open>urust_expr_with_check NAME src\<close> additionally checks the resulting definition
against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend as a kernel-proved HOL
equality and records the theorem as \<open>NAME_conformance\<close>. The checker unfolds
the generated definition, tries \<open>refl\<close> first, then uses bounded structural
matcher normalization and semantic equality rules.

\<open>urust_expr_with_check' NAME new_src old_term\<close> performs the same check with
\<open>new_src\<close> sent to the new parser and the explicit
\<open>\<lbrakk>old_src\<rbrakk>\<close> in \<open>old_term\<close> sent to the existing frontend.

Checked commands run one command-local, saturating branch-path analysis before invoking the old
frontend.  It protects the conformance harness from the old frontend's pattern expansion; ordinary
\<open>urust_expr\<close> definitions do not run this compatibility-only analysis.
\<close>
ML\<open>
structure URust_Legacy_Conformance_Budget =
struct
  open URust_AST

  val branch_path_limit = 256
  exception Overflow of Position.T

  fun add position left right =
    if left > branch_path_limit - right
    then raise Overflow position
    else left + right

  fun multiply position left right =
    if left = 0 orelse right = 0 then 0
    else if left > branch_path_limit div right
    then raise Overflow position
    else left * right

  fun pattern_paths pattern =
    let
      fun product position patterns =
        fold
          (fn nested => fn paths =>
            multiply position paths (pattern_paths nested))
          patterns 1

      fun field_pattern (SF_Field (_, _, nested)) = SOME nested
        | field_pattern (SF_Shorthand _) = NONE
        | field_pattern (SF_Rest _) = NONE

      fun slice_pattern (SI_Pat nested) = SOME nested
        | slice_pattern (SI_Rest _) = NONE
    in
      (case pattern of
         P_Wild _ => 1
       | P_Ident _ => 1
       | P_Literal _ => 1
       | P_Constr (_, position, arguments) =>
           product position arguments
       | P_Tuple (arguments, position) =>
           product position arguments
       | P_Group nested =>
           pattern_paths nested
       | P_Borrow (_, nested, _) =>
           pattern_paths nested
       | P_Alias (_, _, nested, _) =>
           pattern_paths nested
       | P_Range (_, lower, upper, position) =>
           product position [lower, upper]
       | P_Slice (items, position) =>
           product position (map_filter slice_pattern items)
       | P_Struct (_, position, fields) =>
           product position (map_filter field_pattern fields)
       | P_Or (alternatives, position) =>
           fold
             (fn alternative => fn paths =>
               add position paths (pattern_paths alternative))
             alternatives 0)
    end

  fun visit_pattern multiplier pattern =
    multiply (URust_Patterns.position pattern)
      multiplier (pattern_paths pattern)

  fun visit_expression multiplier expression =
    let
      fun visit nested =
        visit_expression multiplier nested

      fun visit_binding (pattern, rhs, body) =
        let
          val _ = visit rhs
          val body_multiplier =
            visit_pattern multiplier pattern
        in
          visit_expression body_multiplier body
        end

      fun visit_place place =
        (case place of
           UP_Ident _ => ()
         | UP_Deref (nested, _) => visit nested
         | UP_Field (base, _, _) => visit_place base
         | UP_Antiq _ => ())

      fun visit_expression_arms _ [] = ()
        | visit_expression_arms current
            (UR_Arm (pattern, guard, body) :: rest) =
            let
              val arm_multiplier =
                visit_pattern current pattern
              val _ =
                (case guard of
                   NONE => ()
                 | SOME (guard_expression, _) =>
                     visit_expression arm_multiplier
                       guard_expression)
              val _ =
                visit_expression arm_multiplier body
              val fallback_multiplier =
                (case guard of
                   NONE => arm_multiplier
                 | SOME (_, position) =>
                     multiply position arm_multiplier 2)
            in
              visit_expression_arms fallback_multiplier rest
            end
    in
      (case expression of
         UE_Unit _ => ()
       | UE_Tuple (arguments, _) =>
           List.app visit arguments
       | UE_Ident _ => ()
       | UE_Literal _ => ()
       | UE_ExprAntiq _ => ()
       | UE_Let binding => visit_binding binding
       | UE_LetMut (pattern, rhs, body, _) =>
           visit_binding (pattern, rhs, body)
       | UE_Const binding => visit_binding binding
       | UE_Seq (first, second) =>
           (visit first; visit second)
       | UE_Return (value, _) =>
           Option.app visit value
       | UE_Bin (_, left, right, _) =>
           (visit left; visit right)
       | UE_Unary (_, operand, _) =>
           visit operand
       | UE_Group (nested, _) =>
           visit nested
       | UE_Block (nested, _) =>
           visit nested
       | UE_If (condition, then_branch, else_branch, _) =>
           (visit condition;
            visit then_branch;
            Option.app visit else_branch)
       | UE_While (_, condition, body, _) =>
           (visit condition; visit body)
       | UE_Loop (_, body, _) =>
           visit body
       | UE_For (pattern, iterable, body, _) =>
           (visit iterable;
            visit_expression
              (visit_pattern multiplier pattern) body)
       | UE_WhileLet (_, pattern, scrutinee, body, _) =>
           (visit scrutinee;
            visit_expression
              (visit_pattern multiplier pattern) body)
       | UE_Call (_, _, arguments, _) =>
           List.app visit arguments
       | UE_Field (receiver, _, _) =>
           visit receiver
       | UE_Assign (_, place, rhs, _) =>
           (visit_place place; visit rhs)
       | UE_Match (_, scrutinee, arms, _) =>
           (visit scrutinee;
            visit_expression_arms multiplier arms))
    end

  fun check expression =
    visit_expression 1 expression
    handle Overflow position =>
      error
        ("urust_expr_with_check: legacy frontend branch-path budget would exceed " ^
          string_of_int branch_path_limit ^
          "; use `urust_expr` for the scalable definition" ^
          Position.here position)

  fun with_check expression action =
    (check expression; action ())
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
     ast: URust_AST.ur_expr}

fun elab_urust_result lthy source =
  (case
      (Parser_Utils.with_parser_lock
        (fn () => URust_Diagnostics.parse_source lthy source)) of
     SOME ast =>
       let
         val checked =
           Syntax.check_term lthy
             (URust_Translate.mk_closed lthy ast)
       in
         Checked_URust
           {term = checked,
            ast = ast}
       end
   | NONE => error ("urust_expr: empty expression" ^ Position.here (Input.pos_of source)))

fun elab_urust lthy source =
  let val Checked_URust {term, ...} =
    elab_urust_result lthy source
  in term end

fun define_urust_result (binding, source) lthy =
  let
    val Checked_URust {term, ast} =
      elab_urust_result lthy source
    val name = Binding.name_of binding
    val (definition, lthy') =
      Specification.definition
        (SOME (binding, NONE, NoSyn)) [] []
        ((Thm.def_binding binding, []),
          Logic.mk_equals
            (Free (name, fastype_of term), term)) lthy
  in ((definition, ast), lthy') end

fun define_urust (binding, source) lthy =
  let
    val (_, lthy') =
      define_urust_result (binding, source) lthy
  in lthy' end

fun old_frontend_source source = "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"

fun define_urust_with_frontend_check
    (binding, new_source, old_frontend_source) lthy =
  let
    val (((lhs, (_, def_thm)), ast), lthy') =
      define_urust_result (binding, new_source) lthy
    val old_frontend =
      URust_Legacy_Conformance_Budget.with_check ast
        (fn () => Syntax.parse_term lthy' old_frontend_source)
    val equality =
      Syntax.check_term lthy'
        (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ old_frontend)
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
  in lthy'' end

fun define_urust_with_check (binding, source) =
  define_urust_with_frontend_check
    (binding, source, old_frontend_source source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr\<close>
          "Parse a uRust expression and define it as a HOL constant"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check\<close>
          "Define a uRust expression and prove HOL equality with the existing frontend"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust_with_check)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check'\<close>
          "Define a uRust expression and prove HOL equality with an explicit old-frontend term"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) --
            Parse.term >>
            (fn ((binding, new_source), old_frontend_source) =>
              define_urust_with_frontend_check
                (binding, new_source, old_frontend_source)))
\<close>

end
