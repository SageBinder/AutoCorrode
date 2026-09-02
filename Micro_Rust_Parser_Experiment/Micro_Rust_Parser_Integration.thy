theory Micro_Rust_Parser_Integration
  imports
    Micro_Rust_Parser
    Shallow_Micro_Rust.Eval
    Shallow_Separation_Logic.Weakest_Precondition
    Crush.Crush
begin

section\<open> Parser proof integration \<close>

text\<open>
This theory provides adapters only for matcher and lazy-conditional constructs emitted by the
parser. It registers those adapters in the existing Eval, WP, and Crush extension points without
changing the upstream proof engines.
\<close>

lemma urust_lazy_conditional_as_two_armed:
  \<open>
    urust_lazy_conditional condition then_thunk else_thunk =
      two_armed_conditional condition
        (then_thunk ()) (else_thunk ())
  \<close>
  by (simp add:
    urust_lazy_conditional_def
    two_armed_conditional_def)

declare urust_matcher_fail_def [micro_rust_simps]
declare urust_matcher_succeed_def [micro_rust_simps]
declare urust_lazy_conditional_as_two_armed [micro_rust_simps]

lemma evaluate_urust_lazy_conditional
    [urust_matcher_evaluation]:
  \<open>
    evaluate
      (urust_lazy_conditional condition then_thunk else_thunk)
      state =
    evaluate
      (two_armed_conditional condition
        (then_thunk ()) (else_thunk ()))
      state
  \<close>
  by (simp add: urust_lazy_conditional_as_two_armed)

corollary urust_eval_action_lazy_conditional
    [urust_eval_action_simps]:
  shows
    \<open>
      (\<Gamma>,
        urust_lazy_conditional condition then_thunk else_thunk)
        \<diamondop>\<^sub>v \<sigma> =
      (\<Union>(value, \<sigma>') \<in>
        (\<Gamma>, condition) \<diamondop>\<^sub>v \<sigma>.
        if value
        then (\<Gamma>, then_thunk ()) \<diamondop>\<^sub>v \<sigma>'
        else (\<Gamma>, else_thunk ()) \<diamondop>\<^sub>v \<sigma>')
    \<close>
    and
    \<open>
      (\<Gamma>,
        urust_lazy_conditional condition then_thunk else_thunk)
        \<diamondop>\<^sub>r \<sigma> =
      ((\<Gamma>, condition) \<diamondop>\<^sub>r \<sigma>) \<union>
      (\<Union>(value, \<sigma>') \<in>
        (\<Gamma>, condition) \<diamondop>\<^sub>v \<sigma>.
        if value
        then (\<Gamma>, then_thunk ()) \<diamondop>\<^sub>r \<sigma>'
        else (\<Gamma>, else_thunk ()) \<diamondop>\<^sub>r \<sigma>')
    \<close>
    and
    \<open>
      (\<Gamma>,
        urust_lazy_conditional condition then_thunk else_thunk)
        \<diamondop>\<^sub>a \<sigma> =
      ((\<Gamma>, condition) \<diamondop>\<^sub>a \<sigma>) \<union>
      (\<Union>(value, \<sigma>') \<in>
        (\<Gamma>, condition) \<diamondop>\<^sub>v \<sigma>.
        if value
        then (\<Gamma>, then_thunk ()) \<diamondop>\<^sub>a \<sigma>'
        else (\<Gamma>, else_thunk ()) \<diamondop>\<^sub>a \<sigma>')
    \<close>
  by (simp_all only:
    urust_lazy_conditional_as_two_armed
    urust_eval_action_two_armed_conditional)

corollary urust_eval_predicate_lazy_conditional
    [urust_eval_predicate_simps]:
  shows
    \<open>
      evaluates_to_value \<Gamma>
        (urust_lazy_conditional condition
          then_thunk else_thunk)
        \<sigma> value \<sigma>'' =
      ((\<exists>\<sigma>'.
          evaluates_to_value \<Gamma> condition
            \<sigma> True \<sigma>' \<and>
          evaluates_to_value \<Gamma> (then_thunk ())
            \<sigma>' value \<sigma>'') \<or>
       (\<exists>\<sigma>'.
          evaluates_to_value \<Gamma> condition
            \<sigma> False \<sigma>' \<and>
          evaluates_to_value \<Gamma> (else_thunk ())
            \<sigma>' value \<sigma>''))
    \<close>
    and
    \<open>
      evaluates_to_return \<Gamma>
        (urust_lazy_conditional condition
          then_thunk else_thunk)
        \<sigma> result \<sigma>'' =
      (evaluates_to_return \<Gamma> condition
        \<sigma> result \<sigma>'' \<or>
       (\<exists>\<sigma>'.
          evaluates_to_value \<Gamma> condition
            \<sigma> True \<sigma>' \<and>
          evaluates_to_return \<Gamma> (then_thunk ())
            \<sigma>' result \<sigma>'') \<or>
       (\<exists>\<sigma>'.
          evaluates_to_value \<Gamma> condition
            \<sigma> False \<sigma>' \<and>
          evaluates_to_return \<Gamma> (else_thunk ())
            \<sigma>' result \<sigma>''))
    \<close>
    and
    \<open>
      evaluates_to_abort \<Gamma>
        (urust_lazy_conditional condition
          then_thunk else_thunk)
        \<sigma> reason \<sigma>'' =
      (evaluates_to_abort \<Gamma> condition
        \<sigma> reason \<sigma>'' \<or>
       (\<exists>\<sigma>'.
          evaluates_to_value \<Gamma> condition
            \<sigma> True \<sigma>' \<and>
          evaluates_to_abort \<Gamma> (then_thunk ())
            \<sigma>' reason \<sigma>'') \<or>
       (\<exists>\<sigma>'.
          evaluates_to_value \<Gamma> condition
            \<sigma> False \<sigma>' \<and>
          evaluates_to_abort \<Gamma> (else_thunk ())
            \<sigma>' reason \<sigma>''))
    \<close>
  by (simp_all only:
    urust_lazy_conditional_as_two_armed
    urust_eval_predicate_two_armed_conditional)

context sepalg
begin

lemma wp_urust_lazy_conditional [micro_rust_wp_simps]:
  \<open>
    \<W>\<P> \<Gamma>
      (urust_lazy_conditional (literal condition)
        then_thunk else_thunk)
      \<psi> \<rho> \<theta> =
    (if condition
     then \<W>\<P> \<Gamma> (then_thunk ()) \<psi> \<rho> \<theta>
     else \<W>\<P> \<Gamma> (else_thunk ()) \<psi> \<rho> \<theta>)
  \<close>
  by (simp add:
    urust_lazy_conditional_as_two_armed
    wp_two_armed_conditional)

lemma wp_urust_lazy_conditionalI
    [micro_rust_wp_case_splits]:
  assumes
    \<open>
      condition \<Longrightarrow>
      \<phi> \<longlongrightarrow>
        \<W>\<P> \<Gamma> (then_thunk ()) \<psi> \<rho> \<theta>
    \<close>
    and
    \<open>
      \<not> condition \<Longrightarrow>
      \<phi> \<longlongrightarrow>
        \<W>\<P> \<Gamma> (else_thunk ()) \<psi> \<rho> \<theta>
    \<close>
  shows
    \<open>
      \<phi> \<longlongrightarrow>
        \<W>\<P> \<Gamma>
          (urust_lazy_conditional (literal condition)
            then_thunk else_thunk)
          \<psi> \<rho> \<theta>
    \<close>
  using assms
  by (simp add: wp_urust_lazy_conditional)

end

ML\<open>
structure URust_Parser_Integration =
struct
  fun definition_rules context =
    Named_Theorems.get context
      \<^named_theorems>\<open>urust_parser_definitions\<close>

  fun prepare_tac context =
    Local_Defs.unfold_tac context
      (definition_rules context) THEN
    ALLGOALS
      (URust_Matcher_Normalize.normalize_tac context)

  fun simp_context context =
    context addsimps
      (@{thms micro_rust_simps} @
       @{thms urust_matcher_evaluation} @
       @{thms urust_eval_action_simps} @
       @{thms urust_eval_predicate_simps} @
       @{thms micro_rust_wp_simps})

  fun simp_tac context =
    prepare_tac context THEN
    ALLGOALS
      (asm_full_simp_tac (simp_context context))
end
\<close>

method_setup urust_parser_prepare = \<open>
  Scan.succeed
    (fn context =>
      SIMPLE_METHOD
        (URust_Parser_Integration.prepare_tac context))
\<close>

method_setup urust_parser_simp = \<open>
  Scan.succeed
    (fn context =>
      SIMPLE_METHOD
        (URust_Parser_Integration.simp_tac context))
\<close>

ML_val\<open>
  local
    val context = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Parser integration collection audit: " ^ message)

    fun check_collection label collection expected_size expected =
      let
        val actual =
          Named_Theorems.get context collection
        val selected =
          filter
            (fn theorem =>
              exists
                (fn candidate =>
                  Thm.eq_thm_prop
                    (theorem, candidate))
                expected)
            actual
        val counts =
          map
            (fn candidate =>
              length
                (filter
                  (fn theorem =>
                    Thm.eq_thm_prop
                      (theorem, candidate))
                  actual))
            expected
      in
        audit_assert
          (label ^ " has cardinality " ^
            string_of_int (length actual) ^
            ", expected " ^ string_of_int expected_size)
          (length actual = expected_size);
        audit_assert
          (label ^ " has the wrong parser adapter membership: " ^
            commas (map string_of_int counts))
          (length selected = length expected andalso
           eq_set Thm.eq_thm_prop (selected, expected))
      end
  in
    val _ =
      check_collection "micro_rust_simps"
        \<^named_theorems>\<open>micro_rust_simps\<close> 147
        @{thms
          urust_matcher_fail_def
          urust_matcher_succeed_def
          urust_lazy_conditional_as_two_armed}
    val _ =
      check_collection "urust_matcher_evaluation"
        \<^named_theorems>\<open>urust_matcher_evaluation\<close> 3
        @{thms evaluate_urust_lazy_conditional}
    val _ =
      check_collection "urust_eval_action_simps"
        \<^named_theorems>\<open>urust_eval_action_simps\<close> 84
        @{thms urust_eval_action_lazy_conditional}
    val _ =
      check_collection "urust_eval_predicate_simps"
        \<^named_theorems>\<open>urust_eval_predicate_simps\<close> 96
        @{thms urust_eval_predicate_lazy_conditional}
    val _ =
      check_collection "micro_rust_wp_simps"
        \<^named_theorems>\<open>micro_rust_wp_simps\<close> 29
        @{thms wp_urust_lazy_conditional}
    val _ =
      check_collection "micro_rust_wp_case_splits"
        \<^named_theorems>\<open>micro_rust_wp_case_splits\<close> 3
        @{thms wp_urust_lazy_conditionalI}
  end
\<close>

end
