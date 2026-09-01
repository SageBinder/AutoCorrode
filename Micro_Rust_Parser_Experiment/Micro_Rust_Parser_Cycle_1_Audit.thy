theory Micro_Rust_Parser_Cycle_1_Audit
  imports Micro_Rust_Parser
begin

section\<open> Cycle 1 structural audit \<close>

text\<open>
C1-I5 requires guarded case compilation to retain one checked scrutinee, one source guard and body
per source arm, and parser-private administrative sharing before explicit unfolding. The checks
below exercise both growing or-pattern alternatives and growing source-arm lists through 16 cases.
They also inspect the explicitly unfolded false-guard path to ensure it enters the next source arm,
not a sibling alternative.
\<close>

datatype cycle1_case =
    Cycle1_A | Cycle1_B | Cycle1_C | Cycle1_D
  | Cycle1_E | Cycle1_F | Cycle1_G | Cycle1_H
  | Cycle1_I | Cycle1_J | Cycle1_K | Cycle1_L
  | Cycle1_M | Cycle1_N | Cycle1_O | Cycle1_P

consts
  cycle1_scrutinee :: cycle1_case
  cycle1_guard_marker :: \<open>nat \<Rightarrow> bool\<close>
  cycle1_body_marker :: \<open>nat \<Rightarrow> nat\<close>
  cycle1_fallback_marker :: nat
  cycle1_first_body :: nat
  cycle1_next_body :: nat
  cycle1_last_body :: nat

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
      else error ("Cycle 1 pattern audit: " ^ message)

    fun checked source =
      elab_urust ctxt (Input.string source)

    fun antiquotation source =
      "\<llangle>" ^ source ^ "\<rrangle>"

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

    fun check_common label term =
      let
        val admin_count =
          count_constant \<^const_name>\<open>urust_admin_let\<close> term
        val scrutinee_count =
          count_constant \<^const_name>\<open>cycle1_scrutinee\<close> term
        val fallback_count =
          count_constant \<^const_name>\<open>cycle1_fallback_marker\<close> term
      in
        audit_assert (label ^ " lost the administrative sharing constant")
          (admin_count > 0);
        audit_assert (label ^ " duplicated the scrutinee")
          (scrutinee_count = 1);
        audit_assert (label ^ " duplicated the terminal fallback")
          (fallback_count = 1)
      end

    fun alternative_source count =
      let
        val alternatives =
          space_implode " | " (take count constructors)
      in
        "match " ^ antiquotation "cycle1_scrutinee" ^ " { " ^
        alternatives ^ " if " ^
        antiquotation "cycle1_guard_marker 0" ^ " \<Rightarrow> " ^
        antiquotation "cycle1_body_marker 0" ^ ", _ \<Rightarrow> " ^
        antiquotation "cycle1_fallback_marker" ^ " }"
      end

    fun check_alternatives count =
      let
        val term = checked (alternative_source count)
        val guard_count =
          count_subterm (marker "cycle1_guard_marker" 0) term
        val body_count =
          count_subterm (marker "cycle1_body_marker" 0) term
      in
        check_common ("or-pattern size " ^ string_of_int count) term;
        audit_assert "an or-pattern duplicated its shared source guard"
          (guard_count = 1);
        audit_assert "an or-pattern duplicated its shared source body"
          (body_count = 1);
        Term.size_of_term term
      end

    fun source_arm (index, constructor) =
      constructor ^ " if " ^
      antiquotation ("cycle1_guard_marker " ^ string_of_int index) ^
      " \<Rightarrow> " ^
      antiquotation ("cycle1_body_marker " ^ string_of_int index)

    fun arm_source count =
      "match " ^ antiquotation "cycle1_scrutinee" ^ " { " ^
      space_implode ", "
        (map source_arm
          (map_index (fn (index, constructor) => (index + 1, constructor))
            (take count constructors))) ^
      ", _ \<Rightarrow> " ^ antiquotation "cycle1_fallback_marker" ^ " }"

    fun check_arms count =
      let
        val term = checked (arm_source count)
        fun check_marker index =
          (audit_assert
             ("source guard " ^ string_of_int index ^ " was duplicated")
             (count_subterm
                (marker "cycle1_guard_marker" index) term = 1);
           audit_assert
             ("source body " ^ string_of_int index ^ " was duplicated")
             (count_subterm
                (marker "cycle1_body_marker" index) term = 1))
      in
        check_common ("source-arm size " ^ string_of_int count) term;
        List.app check_marker (1 upto count);
        Term.size_of_term term
      end

    fun check_linear label sizes =
      let
        val previous = take (length sizes - 1) sizes
        val later = tl sizes
        val deltas =
          map (fn (next, prior) => next - prior)
            (later ~~ previous)
        val maximum_delta =
          fold (fn delta => fn current => Int.max (delta, current))
            deltas 0
        val first = hd sizes
        val last = List.last sizes
      in
        audit_assert (label ^ " did not grow monotonically")
          (List.all (fn delta => delta > 0) deltas);
        audit_assert (label ^ " exceeded the per-case linear size bound")
          (maximum_delta <= 256);
        audit_assert (label ^ " exceeded the aggregate linear size bound")
          (last <= first + 15 * 256)
      end

    fun unfold_admin term =
      let
        val simps =
          put_simpset HOL_basic_ss ctxt
          addsimps [@{thm urust_admin_let_def}]
        val rewrite =
          Simplifier.rewrite simps (Thm.cterm_of ctxt term)
      in Thm.term_of (Thm.rhs_of rewrite) end

    fun conditional_branches term =
      let
        fun collect
            (Const (name, _) $ condition $ then_branch $ else_branch) branches =
              let
                val nested =
                  collect condition
                    (collect then_branch
                      (collect else_branch branches))
              in
                if name = \<^const_name>\<open>two_armed_conditional\<close>
                then (condition, then_branch, else_branch) :: nested
                else nested
              end
          | collect (left $ right) branches =
              collect left (collect right branches)
          | collect (Abs (_, _, body)) branches =
              collect body branches
          | collect _ branches = branches
      in collect term [] end

    val alternative_sizes = map check_alternatives (1 upto 16)
    val arm_sizes = map check_arms (1 upto 16)
    val _ = check_linear "guarded or-pattern compilation" alternative_sizes
    val _ = check_linear "guarded source-arm compilation" arm_sizes

    val fallthrough =
      checked
        ("match " ^ antiquotation "cycle1_scrutinee" ^ " { " ^
         "Cycle1_A | Cycle1_B if " ^
         antiquotation "cycle1_guard_marker 99" ^ " \<Rightarrow> " ^
         antiquotation "cycle1_first_body" ^
         ", Cycle1_B \<Rightarrow> " ^ antiquotation "cycle1_next_body" ^
         ", _ \<Rightarrow> " ^ antiquotation "cycle1_last_body" ^ " }")
    val _ =
      audit_assert "the pre-unfolding false-guard term has no administrative sharing"
        (count_constant \<^const_name>\<open>urust_admin_let\<close> fallthrough > 0)
    val _ =
      audit_assert "the false-guard source body was duplicated before unfolding"
        (count_constant \<^const_name>\<open>cycle1_first_body\<close> fallthrough = 1)
    val unfolded = unfold_admin fallthrough
    val _ =
      audit_assert "explicit administrative unfolding left an administrative constant"
        (count_constant \<^const_name>\<open>urust_admin_let\<close> unfolded = 0)
    val guarded =
      filter
        (fn (_, then_branch, _) =>
          count_constant \<^const_name>\<open>cycle1_first_body\<close>
            then_branch > 0)
        (conditional_branches unfolded)
    val _ =
      audit_assert "explicit unfolding exposed no source-guard false branch"
        (not (null guarded))
    val _ =
      List.app
        (fn (_, _, else_branch) =>
          (audit_assert
             "a false source guard retried a sibling or-alternative"
             (count_constant \<^const_name>\<open>cycle1_first_body\<close>
                else_branch = 0);
           audit_assert
             "a false source guard did not continue with the next source arm"
             (count_constant \<^const_name>\<open>cycle1_next_body\<close>
                else_branch > 0)))
        guarded
  in
    val _ =
      writeln
        ("Cycle 1 guarded-case audit sizes (alternatives): " ^
         commas (map string_of_int alternative_sizes))
    val _ =
      writeln
        ("Cycle 1 guarded-case audit sizes (source arms): " ^
         commas (map string_of_int arm_sizes))
  end
\<close>

end
