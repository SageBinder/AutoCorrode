theory Micro_Rust_Parser_Cycle_2_Audit
  imports
    Micro_Rust_Parser_Negative_Conformance
    Micro_Rust_Parser_Improvements
    Micro_Rust_Parser_Showoff
    Micro_Rust_Parser_Cycle_1_Audit
begin

section\<open> Cycle 2 matcher audit \<close>

text\<open>
This theory keeps the Cycle 2 stress cases out of the language corpora. It audits the public
definition boundary, scalable structural growth, semantic matcher laws, compatibility limits,
constructor resolution, terminal diagnostics, and the transaction-safe command inventories.
\<close>

datatype cycle2_tree =
    Cycle2_Leaf cycle1_case
  | Cycle2_Node cycle1_case cycle2_tree

datatype cycle2_nat_chain =
    Cycle2_Nat_Last nat
  | Cycle2_Nat_More nat cycle2_nat_chain

datatype cycle2_mixed =
  Cycle2_Mixed cycle1_case nat \<open>nat list\<close> \<open>nat option\<close>

consts
  cycle2_tree_scrutinee :: cycle2_tree
  cycle2_nat_scrutinee :: cycle2_nat_chain
  cycle2_slice_scrutinee :: \<open>nat list\<close>
  cycle2_mixed_scrutinee :: cycle2_mixed
  cycle2_guard_marker :: \<open>nat \<Rightarrow> bool\<close>
  cycle2_body_marker :: \<open>nat \<Rightarrow> nat\<close>
  cycle2_fallback_marker :: nat
  cycle2_value_marker :: \<open>nat \<Rightarrow> nat\<close>
  cycle2_lower_marker :: \<open>nat \<Rightarrow> nat\<close>
  cycle2_upper_marker :: \<open>nat \<Rightarrow> nat\<close>
  cycle2_while_body_marker :: unit

urust_expr cycle2_scalable_definition
  \<open>
    match \<llangle>cycle2_tree_scrutinee\<rrangle> {
      Cycle2_Node(Cycle1_A | Cycle1_B,
        Cycle2_Node(Cycle1_A | Cycle1_B,
          Cycle2_Node(Cycle1_A | Cycle1_B,
            Cycle2_Node(Cycle1_A | Cycle1_B,
              Cycle2_Node(Cycle1_A | Cycle1_B,
                Cycle2_Node(Cycle1_A | Cycle1_B,
                  Cycle2_Node(Cycle1_A | Cycle1_B,
                    Cycle2_Node(Cycle1_A | Cycle1_B,
                      Cycle2_Leaf(Cycle1_A | Cycle1_B)))))))))
        if \<llangle>cycle2_guard_marker 900\<rrangle> \<Rightarrow>
          \<llangle>cycle2_body_marker 900\<rrangle>,
      _ \<Rightarrow> \<llangle>cycle2_fallback_marker\<rrangle>
    }
  \<close>

subsection\<open> Public representation and code preparation \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 2 representation audit: " ^ message)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun contains_matcher term =
      count_constant \<^const_name>\<open>urust_matcher_run\<close> term +
      count_constant \<^const_name>\<open>urust_matcher_run_guarded\<close> term +
      count_constant \<^const_name>\<open>urust_matcher_run_value\<close> term +
      count_constant
        \<^const_name>\<open>urust_matcher_run_guarded_value\<close> term > 0

    fun antiquotation source = "\<llangle>" ^ source ^ "\<rrangle>"

    fun tree_pattern 1 =
          "Cycle2_Leaf(Cycle1_A | Cycle1_B)"
      | tree_pattern depth =
          "Cycle2_Node(Cycle1_A | Cycle1_B, " ^
            tree_pattern (depth - 1) ^ ")"

    val source =
      "match " ^ antiquotation "cycle2_tree_scrutinee" ^ " { " ^
      tree_pattern 9 ^ " if " ^
      antiquotation "cycle2_guard_marker 900" ^ " \<Rightarrow> " ^
      antiquotation "cycle2_body_marker 900" ^ ", _ \<Rightarrow> " ^
      antiquotation "cycle2_fallback_marker" ^ " }"
    val Checked_URust {term = checked_rhs, ...} =
      elab_urust_result ctxt
        (Parser_Lex_Util.text_source source)
    val definition_rhs =
      Thm.term_of
        (Thm.rhs_of
          (Proof_Context.get_thm ctxt
            "cycle2_scalable_definition_def"))
    val simplified_rhs =
      Thm.term_of
        (Thm.rhs_of
          (Simplifier.rewrite ctxt (Thm.cterm_of ctxt definition_rhs)))
    val {eqngr, ...} =
      Code_Preproc.obtain true
        {ctxt = ctxt,
         consts = [\<^const_name>\<open>cycle2_scalable_definition\<close>],
         terms = []}
    val code_constants = Code_Preproc.all eqngr

    val _ =
      audit_assert "the checked RHS lost its matcher representation"
        (contains_matcher checked_rhs)
    val _ =
      audit_assert "definition unfolding changed the linear checked size"
        (Term.size_of_term definition_rhs =
          Term.size_of_term checked_rhs)
    val _ =
      audit_assert "definition unfolding erased the matcher representation"
        (contains_matcher definition_rhs)
    val _ =
      audit_assert "default simplification unfolded the matcher runtime"
        (contains_matcher simplified_rhs)
    val _ =
      audit_assert "default simplification expanded the scalable term"
        (Term.size_of_term simplified_rhs <=
          Term.size_of_term definition_rhs + 64)
    val _ =
      audit_assert "code preparation omitted the public definition"
        (member (op =) code_constants
          \<^const_name>\<open>cycle2_scalable_definition\<close>)
    val _ =
      audit_assert "code preparation omitted the lazy matcher runtime"
        (member (op =) code_constants
          \<^const_name>\<open>urust_lazy_conditional\<close>)
  in
    val _ =
      writeln
        ("Cycle 2 scalable definition sizes: checked=" ^
          string_of_int (Term.size_of_term checked_rhs) ^
          ", default-simp=" ^
          string_of_int (Term.size_of_term simplified_rhs))
  end
\<close>

subsection\<open> Linear structural growth \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val constructors =
      ["Cycle1_A", "Cycle1_B", "Cycle1_C", "Cycle1_D",
       "Cycle1_E", "Cycle1_F", "Cycle1_G", "Cycle1_H",
       "Cycle1_I", "Cycle1_J", "Cycle1_K", "Cycle1_L",
       "Cycle1_M", "Cycle1_N", "Cycle1_O", "Cycle1_P"]

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 2 growth audit: " ^ message)

    fun antiquotation source = "\<llangle>" ^ source ^ "\<rrangle>"

    fun checked_result source =
      let
        val Checked_URust result =
          elab_urust_result ctxt
            (Parser_Lex_Util.text_source source)
      in result end

    fun checked source = #term (checked_result source)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_subterm needle =
      let
        fun count term =
          (if term aconv needle then 1 else 0) +
          (case term of
             left $ right => count left + count right
           | Abs (_, _, body) => count body
           | _ => 0)
      in count end

    fun marker name index =
      Syntax.read_term ctxt (name ^ " " ^ string_of_int index)

    fun match_source scrutinee pattern index =
      "match " ^ antiquotation scrutinee ^ " { " ^
      pattern ^ " if " ^
      antiquotation ("cycle2_guard_marker " ^ string_of_int index) ^
      " \<Rightarrow> " ^
      antiquotation ("cycle2_body_marker " ^ string_of_int index) ^
      ", _ \<Rightarrow> " ^ antiquotation "cycle2_fallback_marker" ^ " }"

    fun check_markers label scrutinee index term =
      (audit_assert (label ^ " duplicated its scrutinee")
         (count_constant scrutinee term = 1);
       audit_assert (label ^ " duplicated its guard")
         (count_subterm (marker "cycle2_guard_marker" index) term = 1);
       audit_assert (label ^ " duplicated its body")
         (count_subterm (marker "cycle2_body_marker" index) term = 1);
       audit_assert (label ^ " duplicated its fallback")
         (count_constant \<^const_name>\<open>cycle2_fallback_marker\<close>
            term = 1))

    fun check_linear label bound sizes =
      let
        val deltas =
          map (fn (later, earlier) => later - earlier)
            (tl sizes ~~ take (length sizes - 1) sizes)
      in
        audit_assert (label ^ " did not grow monotonically")
          (List.all (fn delta => delta > 0) deltas);
        audit_assert (label ^ " exceeded its per-step linear bound")
          (List.all (fn delta => delta <= bound) deltas);
        audit_assert (label ^ " exceeded its aggregate linear bound")
          (List.last sizes <= hd sizes + (length sizes - 1) * bound)
      end

    fun top_or_source count =
      match_source "cycle2_tree_scrutinee"
        ("Cycle2_Leaf(" ^
          space_implode " | " (take count constructors) ^ ")")
        (100 + count)

    fun top_arm_source count =
      let
        fun arm (index, constructor) =
          "Cycle2_Leaf(" ^ constructor ^ ") if " ^
          antiquotation
            ("cycle2_guard_marker " ^ string_of_int (200 + index)) ^
          " \<Rightarrow> " ^
          antiquotation
            ("cycle2_body_marker " ^ string_of_int (200 + index))
      in
        "match " ^ antiquotation "cycle2_tree_scrutinee" ^ " { " ^
        space_implode ", "
          (map arm
            (map_index (fn (index, constructor) =>
              (index + 1, constructor)) (take count constructors))) ^
        ", _ \<Rightarrow> " ^ antiquotation "cycle2_fallback_marker" ^ " }"
      end

    fun tree_pattern element 1 =
          "Cycle2_Leaf(" ^ element 1 ^ ")"
      | tree_pattern element depth =
          "Cycle2_Node(" ^ element depth ^ ", " ^
            tree_pattern element (depth - 1) ^ ")"

    fun nat_pattern element 1 =
          "Cycle2_Nat_Last(" ^ element 1 ^ ")"
      | nat_pattern element depth =
          "Cycle2_Nat_More(" ^ element depth ^ ", " ^
            nat_pattern element (depth - 1) ^ ")"

    fun or_element _ = "Cycle1_A | Cycle1_B"
    fun value_element index =
      antiquotation ("cycle2_value_marker " ^ string_of_int index)
    fun range_element index =
      antiquotation ("cycle2_lower_marker " ^ string_of_int index) ^
      "..=" ^
      antiquotation ("cycle2_upper_marker " ^ string_of_int index)
    fun alias_element index =
      "cycle2_alias_" ^ string_of_int index ^ " @ _"

    fun nested_source scrutinee element family count =
      match_source scrutinee (tree_pattern element count)
        (family * 100 + count)

    fun nested_nat_source element family count =
      match_source "cycle2_nat_scrutinee"
        (nat_pattern element count) (family * 100 + count)

    fun slice_pattern count =
      "[cycle2_slice_head, .., " ^
      commas
        (map (fn index =>
          "cycle2_slice_suffix_" ^ string_of_int index)
          (1 upto count)) ^ "]"

    fun check_top_or count =
      let
        val {term, ...} = checked_result (top_or_source count)
      in
        check_markers ("top-level or " ^ string_of_int count)
          \<^const_name>\<open>cycle2_tree_scrutinee\<close>
          (100 + count) term;
        Term.size_of_term term
      end

    fun check_top_arms count =
      let
        val term = checked (top_arm_source count)
        fun one index =
          (audit_assert "a guarded source arm duplicated its guard"
             (count_subterm
               (marker "cycle2_guard_marker" (200 + index)) term = 1);
           audit_assert "a guarded source arm duplicated its body"
             (count_subterm
               (marker "cycle2_body_marker" (200 + index)) term = 1))
      in
        audit_assert "guarded source arms duplicated the scrutinee"
          (count_constant
            \<^const_name>\<open>cycle2_tree_scrutinee\<close> term = 1);
        List.app one (1 upto count);
        Term.size_of_term term
      end

    fun check_nested_or count =
      let
        val {term, ...} =
          checked_result
            (nested_source "cycle2_tree_scrutinee"
              or_element 3 count)
      in
        check_markers ("nested or " ^ string_of_int count)
          \<^const_name>\<open>cycle2_tree_scrutinee\<close>
          (300 + count) term;
        Term.size_of_term term
      end

    fun check_nested_values count =
      let
        val term =
          checked
            (nested_nat_source value_element 4 count)
        val _ =
          List.app
            (fn index =>
              audit_assert "a value endpoint was elaborated more than once"
                (count_subterm
                  (marker "cycle2_value_marker" index) term = 1))
            (1 upto count)
      in
        check_markers ("nested values " ^ string_of_int count)
          \<^const_name>\<open>cycle2_nat_scrutinee\<close>
          (400 + count) term;
        Term.size_of_term term
      end

    fun check_ranges count =
      let
        val term =
          checked
            (nested_nat_source range_element 5 count)
        val _ =
          List.app
            (fn index =>
              (audit_assert "a lower range endpoint was elaborated more than once"
                 (count_subterm
                   (marker "cycle2_lower_marker" index) term = 1);
               audit_assert "an upper range endpoint was elaborated more than once"
                 (count_subterm
                   (marker "cycle2_upper_marker" index) term = 1)))
            (1 upto count)
      in
        check_markers ("nested ranges " ^ string_of_int count)
          \<^const_name>\<open>cycle2_nat_scrutinee\<close>
          (500 + count) term;
        Term.size_of_term term
      end

    fun check_aliases count =
      let
        val term =
          checked
            (nested_source "cycle2_tree_scrutinee"
              alias_element 6 count)
      in
        check_markers ("nested aliases " ^ string_of_int count)
          \<^const_name>\<open>cycle2_tree_scrutinee\<close>
          (600 + count) term;
        Term.size_of_term term
      end

    fun check_slices count =
      let
        val term =
          checked
            (match_source "cycle2_slice_scrutinee"
              (slice_pattern count) (700 + count))
      in
        check_markers ("slice suffix " ^ string_of_int count)
          \<^const_name>\<open>cycle2_slice_scrutinee\<close>
          (700 + count) term;
        audit_assert "slice suffix reversal was not represented by one lift"
          (count_constant \<^const_name>\<open>urust_matcher_lift\<close> term = 1);
        Term.size_of_term term
      end

    val top_or_sizes = map check_top_or (1 upto 16)
    val top_arm_sizes = map check_top_arms (1 upto 16)
    val nested_or_sizes = map check_nested_or (1 upto 12)
    val value_sizes = map check_nested_values (1 upto 12)
    val range_sizes = map check_ranges (1 upto 12)
    val alias_sizes = map check_aliases (1 upto 12)
    val slice_sizes = map check_slices (1 upto 12)

    val _ = check_linear "top-level ors" 512 top_or_sizes
    val _ = check_linear "guarded source arms" 768 top_arm_sizes
    val _ = check_linear "independent nested ors" 768 nested_or_sizes
    val _ = check_linear "nested values" 1024 value_sizes
    val _ = check_linear "nested ranges" 1536 range_sizes
    val _ = check_linear "nested aliases" 1024 alias_sizes
    val _ = check_linear "slice suffixes" 1024 slice_sizes

    val mixed_pattern =
      "cycle2_whole @ Cycle2_Mixed(" ^
      "Cycle1_A | Cycle1_B, " ^
      antiquotation "cycle2_lower_marker 91" ^ "..=" ^
      antiquotation "cycle2_upper_marker 91" ^ ", " ^
      "[cycle2_head, .., cycle2_tail], " ^
      "Some(cycle2_option @ cycle2_value))"
    val mixed =
      checked
        (match_source "cycle2_mixed_scrutinee"
          mixed_pattern 991)
    val _ =
      check_markers "mixed payload"
        \<^const_name>\<open>cycle2_mixed_scrutinee\<close> 991 mixed
    val _ =
      audit_assert "the mixed payload did not retain structural choice"
        (count_constant \<^const_name>\<open>urust_matcher_choice\<close>
          mixed > 0)
    val _ =
      audit_assert "the mixed payload did not retain structural products"
        (count_constant \<^const_name>\<open>urust_matcher_product\<close>
          mixed > 0)
    val _ =
      audit_assert "the mixed payload did not evaluate slice reversal once"
        (count_constant \<^const_name>\<open>urust_matcher_lift\<close>
          mixed = 1)
  in
    val _ =
      writeln
        ("Cycle 2 growth endpoints: top-or=" ^
          string_of_int (List.last top_or_sizes) ^
          ", arms=" ^ string_of_int (List.last top_arm_sizes) ^
          ", nested-or=" ^ string_of_int (List.last nested_or_sizes) ^
          ", values=" ^ string_of_int (List.last value_sizes) ^
          ", ranges=" ^ string_of_int (List.last range_sizes) ^
          ", aliases=" ^ string_of_int (List.last alias_sizes) ^
          ", slices=" ^ string_of_int (List.last slice_sizes))
  end
\<close>

subsection\<open> Matcher semantics and executable code \<close>

lemmas cycle2_matcher_semantic_laws =
  urust_matcher_choice_left_to_right
  urust_matcher_product_backtracks
  urust_matcher_guard_false_skips_alternatives
  urust_matcher_guard_false_skips_value_alternatives
  evaluate_urust_matcher_run
  evaluate_urust_matcher_lift

definition cycle2_code_expression ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
where
  \<open>
    cycle2_code_expression =
      urust_matcher_run_value
        (urust_matcher_choice
          (urust_matcher_test (\<lambda>x :: nat. literal (x = 2)))
          (urust_matcher_test (\<lambda>x. literal (x = 3))))
        3
        (\<lambda>x. literal (x + 10))
        (\<lambda>_. literal 0)
  \<close>

lemma cycle2_code_expression_result:
  \<open> evaluate cycle2_code_expression () = Success 13 () \<close>
  by (simp add:
    cycle2_code_expression_def
    urust_matcher_run_value_def
    urust_matcher_choice_def
    urust_matcher_test_def
    urust_lazy_conditional_def
    Core_Expression.bind.simps
    bind_evaluate literal_def evaluate_def)

value [code]
  \<open>
    case evaluate cycle2_code_expression () of
      Success value _ \<Rightarrow> value
    | _ \<Rightarrow> 0
  \<close>

definition cycle2_different_return_expression ::
  \<open>(unit, bool, nat, unit, unit, unit) expression\<close>
where
  \<open>
    cycle2_different_return_expression =
      urust_matcher_run_value
        (urust_matcher_succeed (\<lambda>x :: nat. x))
        1
        (\<lambda>_. literal True)
        (\<lambda>_. literal False)
  \<close>

lemma cycle2_different_return_expression_result:
  \<open>
    evaluate cycle2_different_return_expression () =
      Success True ()
  \<close>
  by (simp add:
    cycle2_different_return_expression_def
    urust_matcher_run_value_def
    urust_matcher_succeed_def
    literal_def evaluate_def)

definition cycle2_return_scrutinee ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
where
  \<open> cycle2_return_scrutinee = Expression (\<lambda>state. Return 7 state) \<close>

definition cycle2_abort_scrutinee ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
where
  \<open> cycle2_abort_scrutinee = abort (CustomAbort ()) \<close>

definition cycle2_yield_scrutinee ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
where
  \<open>
    cycle2_yield_scrutinee =
      Expression
        (\<lambda>state.
          Yield () state (\<lambda>_. literal 4))
  \<close>

lemma cycle2_return_propagates:
  \<open>
    evaluate
      (urust_matcher_run
        (urust_matcher_succeed (\<lambda>x :: nat. x))
        cycle2_return_scrutinee
        (\<lambda>x. literal x)
        (\<lambda>_. literal 0))
      () =
      Return 7 ()
  \<close>
  by (simp add:
    urust_matcher_run_def
    urust_matcher_succeed_def
    cycle2_return_scrutinee_def
    Core_Expression.bind.simps
    literal_def evaluate_def)

lemma cycle2_abort_propagates:
  \<open>
    evaluate
      (urust_matcher_run
        (urust_matcher_succeed (\<lambda>x :: nat. x))
        cycle2_abort_scrutinee
        (\<lambda>x. literal x)
        (\<lambda>_. literal 0))
      () =
      Abort (CustomAbort ()) ()
  \<close>
  by (simp add:
    urust_matcher_run_def
    urust_matcher_succeed_def
    cycle2_abort_scrutinee_def
    Core_Expression.bind.simps
    abort_def literal_def evaluate_def)

lemma cycle2_yield_resumes_matcher:
  \<open>
    case evaluate
      (urust_matcher_run
        (urust_matcher_succeed (\<lambda>x :: nat. x))
        cycle2_yield_scrutinee
        (\<lambda>x. literal x)
        (\<lambda>_. literal 0))
      () of
      Yield _ state continuation \<Rightarrow>
        evaluate (continuation ()) state = Success 4 state
    | _ \<Rightarrow> False
  \<close>
  by (simp add:
    urust_matcher_run_def
    cycle2_yield_scrutinee_def
    urust_matcher_succeed_def
    Core_Expression.bind.simps
    bind_evaluate literal_def evaluate_def)

subsection\<open> While-let coverage and checked-command compatibility boundary \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 2 boundary audit: " ^ message)

    fun antiquotation source = "\<llangle>" ^ source ^ "\<rrangle>"

    fun checked_result source =
      let
        val Checked_URust result =
          elab_urust_result ctxt
            (Parser_Lex_Util.text_source source)
      in result end

    fun checked source = #term (checked_result source)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun tree_pattern 1 =
          "Cycle2_Leaf(Cycle1_A | Cycle1_B)"
      | tree_pattern depth =
          "Cycle2_Node(Cycle1_A | Cycle1_B, " ^
            tree_pattern (depth - 1) ^ ")"

    fun matcher_source depth =
      "match " ^ antiquotation "cycle2_tree_scrutinee" ^ " { " ^
      tree_pattern depth ^ " if " ^
      antiquotation "cycle2_guard_marker 812" ^ " \<Rightarrow> " ^
      antiquotation "cycle2_body_marker 812" ^ ", _ \<Rightarrow> " ^
      antiquotation "cycle2_fallback_marker" ^ " }"

    fun nested_guard_source outer_depth inner_depth =
      "match " ^ antiquotation "cycle2_tree_scrutinee" ^ " { " ^
      tree_pattern outer_depth ^ " if (match " ^
      antiquotation "cycle2_tree_scrutinee" ^ " { " ^
      tree_pattern inner_depth ^ " \<Rightarrow> True, _ \<Rightarrow> False }) \<Rightarrow> " ^
      antiquotation "cycle2_body_marker 813" ^ ", _ \<Rightarrow> " ^
      antiquotation "cycle2_fallback_marker" ^ " }"

    fun while_source pattern scrutinee =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
      pattern ^ " = " ^ scrutinee ^ " { " ^
      antiquotation "cycle2_while_body_marker" ^ " }"

    val direct =
      checked (while_source "_" (antiquotation "1 :: nat"))
    val total =
      checked
        (while_source "Some(_) | None"
          (antiquotation "Some (1 :: nat)"))
    val partial =
      checked
        (while_source "Some(_)"
          (antiquotation "None :: nat option"))

    val _ =
      audit_assert "direct irrefutable while-let used a matcher"
        (count_constant \<^const_name>\<open>urust_matcher_run_value\<close>
          direct = 0 andalso
         count_constant
          \<^const_name>\<open>urust_matcher_run_guarded_value\<close>
          direct = 0)
    val _ =
      audit_assert "direct irrefutable while-let retained a false fallback"
        (count_constant \<^const_name>\<open>False\<close> direct = 0)
    val _ =
      audit_assert "total while-let retained a false fallback"
        (count_constant \<^const_name>\<open>False\<close> total = 0)
    val _ =
      audit_assert "partial while-let lost its single false fallback"
        (count_constant \<^const_name>\<open>False\<close> partial = 1)

    val at_limit = checked_result (matcher_source 7)
    val over_limit = checked_result (matcher_source 8)
    val _ =
      URust_Legacy_Conformance_Budget.with_check
        (#ast at_limit) (fn () => ())
    val _ =
      audit_assert "ordinary elaboration rejected the over-budget source"
        (count_constant \<^const_name>\<open>urust_matcher_run\<close>
            (#term over_limit) +
         count_constant \<^const_name>\<open>urust_matcher_run_guarded\<close>
            (#term over_limit) +
         count_constant \<^const_name>\<open>urust_matcher_run_value\<close>
            (#term over_limit) +
         count_constant
            \<^const_name>\<open>urust_matcher_run_guarded_value\<close>
            (#term over_limit) > 0)
    val over_limit_check =
      Exn.result
        (fn () =>
          URust_Legacy_Conformance_Budget.with_check
            (#ast over_limit)
            (fn () =>
              error "THIS LEGACY NORMALIZATION MUST NOT RUN")) ()
    val _ =
      (case over_limit_check of
         Exn.Res _ =>
           error "an over-budget checked command unexpectedly succeeded"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               audit_assert "over-budget rejection lost its diagnostic"
                 (String.isSubstring
                   "legacy frontend branch-path budget would exceed 256"
                   message);
               audit_assert "over-budget rejection reached old-term parsing"
                 (not
                   (String.isSubstring
                     "THIS LEGACY NORMALIZATION MUST NOT RUN" message))
             end)

    val nested_at_limit =
      checked_result (nested_guard_source 6 2)
    val nested_over_limit =
      checked_result (nested_guard_source 7 2)
    val _ =
      URust_Legacy_Conformance_Budget.check
        (#ast nested_at_limit)
    val _ =
      (case Exn.result
          URust_Legacy_Conformance_Budget.check
          (#ast nested_over_limit) of
         Exn.Res _ =>
           error "nested match did not contribute to the branch-path budget"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())

    val positioned_source =
      Parser_Lex_Util.positioned_content_source
        (matcher_source 8)
        (Position.make0 20 5 0 "" "" "")
    val Checked_URust {ast = positioned_ast, ...} =
      elab_urust_result ctxt positioned_source
    val overflow_position =
      (case positioned_ast of
         URust_AST.UE_Match (_, _,
           URust_AST.UR_Arm (_, SOME (_, guard_position), _) :: _, _) =>
             guard_position
       | _ =>
           error "Cycle 2 boundary audit: positioned source AST changed")
    val expected_here =
      XML.content_of
        (YXML.parse_body (Position.here overflow_position))
    val _ =
      (case Exn.result
          URust_Legacy_Conformance_Budget.check
          positioned_ast of
         Exn.Res _ =>
           error "positioned over-budget source unexpectedly succeeded"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message =
                 XML.content_of
                   (YXML.parse_body
                     (Runtime.exn_message exn))
             in
               audit_assert "branch-path rejection lost its source position"
                 (String.isSubstring expected_here message)
             end)
  in
    val _ =
      writeln "Cycle 2 checked-command branch-path budget passed"
  end
\<close>

subsection\<open> Constructor-resolution closure \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val left_struct =
      "Struct_Ambiguity_Left.struct_ambiguity_left.AmbiguousStruct"
    val right_struct =
      "Struct_Ambiguity_Right.struct_ambiguity_right.AmbiguousStruct"
    val left_nullary =
      "Struct_Ambiguity_Left.nullary_ambiguity_left.AmbiguousNullary"
    val right_nullary =
      "Struct_Ambiguity_Right.nullary_ambiguity_right.AmbiguousNullary"

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 2 closure audit: " ^ message)

    fun expect_sorted_ambiguity source left right =
      (case Exn.result
          (fn () =>
            elab_urust ctxt
              (Parser_Lex_Util.text_source source)) () of
         Exn.Res _ => error "ambiguous constructor unexpectedly resolved"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               audit_assert "constructor candidates were not sorted"
                 (String.isSubstring (left ^ ", " ^ right) message)
             end)

    val resolver =
      URust_Resolution.make_constructor_resolver
        ctxt Position.none
    val left_info =
      the
        (URust_Resolution.resolve_constructor resolver
          (left_struct, Position.none))
    val _ =
      audit_assert "qualified constructor selection changed identity"
        (URust_Resolution.constructor_identity left_info =
          left_struct)
    val _ =
      audit_assert "qualified constructor selection changed arity"
        (URust_Resolution.constructor_arity left_info = 1)
    val _ =
      (case URust_Resolution.constructor_family left_info of
         SOME (_, members) =>
           audit_assert "qualified family metadata changed"
             (map_filter
               (fn Const (name, _) => SOME name | _ => NONE)
               members = [left_struct])
       | NONE => error "qualified constructor lost family metadata")
    val _ =
      expect_sorted_ambiguity
        "match_case \<llangle>undefined\<rrangle> { AmbiguousStruct(x) \<Rightarrow> x }"
        left_struct right_struct
    val _ =
      expect_sorted_ambiguity
        "match_case \<llangle>undefined\<rrangle> { AmbiguousNullary \<Rightarrow> \<llangle>True\<rrangle> }"
        left_nullary right_nullary

  in
    val _ = writeln "Cycle 2 constructor-resolution audit passed"
  end
\<close>

end
