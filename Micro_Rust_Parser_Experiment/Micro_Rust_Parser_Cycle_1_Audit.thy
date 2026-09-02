theory Micro_Rust_Parser_Cycle_1_Audit
  imports Micro_Rust_Parser
begin

section\<open> Cycle 1 structural audit \<close>

text\<open>
C1-I5 requires guarded case compilation to retain one checked scrutinee, one source guard and body
per source arm in the semantic matcher representation. The checks below exercise both growing
or-pattern alternatives and growing source-arm lists through 16 cases. They also inspect the guarded
runner's failure continuation to ensure it enters the next source arm, not a sibling alternative.
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
  cycle1_while_body_marker :: unit

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
        val matcher_count =
          count_constant \<^const_name>\<open>urust_matcher_run\<close> term +
          count_constant \<^const_name>\<open>urust_matcher_run_guarded\<close> term +
          count_constant \<^const_name>\<open>urust_matcher_run_value\<close> term +
          count_constant
            \<^const_name>\<open>urust_matcher_run_guarded_value\<close> term
        val scrutinee_count =
          count_constant \<^const_name>\<open>cycle1_scrutinee\<close> term
        val fallback_count =
          count_constant \<^const_name>\<open>cycle1_fallback_marker\<close> term
      in
        audit_assert (label ^ " lost the semantic matcher runner")
          (matcher_count > 0);
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

    fun guarded_runs term =
      let
        fun collect
            (application as
              Const (name, _) $ matcher $ scrutinee $ guard $
                success $ failure) runs =
              let
                val nested =
                  collect matcher
                    (collect scrutinee
                      (collect guard
                        (collect success
                          (collect failure runs))))
              in
                if name =
                    \<^const_name>\<open>urust_matcher_run_guarded_value\<close>
                then application :: nested
                else nested
              end
          | collect (left $ right) runs =
              collect left (collect right runs)
          | collect (Abs (_, _, body)) runs =
              collect body runs
          | collect _ runs = runs
      in collect term [] end

    fun guarded_success_failure
        (Const (name, _) $ _ $ _ $ _ $ success $ failure) =
          if name =
              \<^const_name>\<open>urust_matcher_run_guarded_value\<close>
          then (success, failure)
          else error "Cycle 1 pattern audit: expected guarded matcher runner"
      | guarded_success_failure _ =
          error "Cycle 1 pattern audit: malformed guarded matcher runner"

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
      audit_assert "the false-guard source body was duplicated"
        (count_constant \<^const_name>\<open>cycle1_first_body\<close> fallthrough = 1)
    val guarded =
      filter
        (fn run =>
          let val (success, _) = guarded_success_failure run in
          count_constant \<^const_name>\<open>cycle1_first_body\<close>
            success > 0
          end)
        (guarded_runs fallthrough)
    val _ =
      audit_assert "the matcher term exposed no source-guard runner"
        (not (null guarded))
    val _ =
      List.app
        (fn run =>
          let val (_, failure) = guarded_success_failure run in
            (audit_assert
               "a false source guard retried a sibling or-alternative"
               (count_constant \<^const_name>\<open>cycle1_first_body\<close>
                  failure = 0);
             audit_assert
               "a false source guard did not continue with the next source arm"
               (count_constant \<^const_name>\<open>cycle1_next_body\<close>
                  failure > 0))
          end)
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

section\<open> Conservative while-let coverage \<close>

text\<open>
C1-I6 removes the false continuation only for coverage proved by the resolved-pattern metadata.
The condition still sequences the source body with true, and the bounded loop body remains skip.
Partial patterns retain exactly one false fallback.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 1 while-let audit: " ^ message)

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

    fun loop_source pattern scrutinee =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
      pattern ^ " = " ^ scrutinee ^ " { let _ = " ^
      antiquotation "cycle1_while_body_marker" ^ "; () }"

    fun bounded_while_arguments term =
      let
        fun find
            (Const (name, _) $ fuel $ condition $ body) =
              if name = \<^const_name>\<open>bounded_while\<close>
              then SOME (fuel, condition, body)
              else
                get_first find [fuel, condition, body]
          | find (left $ right) =
              (case find left of
                 SOME result => SOME result
               | NONE => find right)
          | find (Abs (_, _, body)) = find body
          | find _ = NONE
      in
        (case find term of
           SOME result => result
         | NONE => error "Cycle 1 while-let audit: bounded_while was not generated")
      end

    fun is_skip term =
      (case Term.strip_comb term of
         (Const (literal_name, _), [Const (unit_name, _)]) =>
           literal_name = \<^const_name>\<open>literal\<close> andalso
             unit_name = \<^const_name>\<open>Product_Type.Unity\<close>
       | _ => false)

    fun check_exhaustive label source =
      let
        val term = checked source
        val (_, condition, body) = bounded_while_arguments term
      in
        audit_assert (label ^ " retained a false fallback")
          (count_constant \<^const_name>\<open>False\<close> term = 0);
        audit_assert (label ^ " moved the source body out of the condition")
          (count_constant
             \<^const_name>\<open>cycle1_while_body_marker\<close>
             condition = 1);
        audit_assert (label ^ " did not keep skip as the bounded loop body")
          (is_skip body)
      end

    val _ =
      check_exhaustive "TNil"
        (loop_source "TNil" "TNil")
    val _ =
      check_exhaustive "complete option family"
        (loop_source "Some(_) | None"
          (antiquotation "Some (1 :: nat)"))
    val _ =
      check_exhaustive "nested complete option family"
        (loop_source "Some(Some(_) | None) | None"
          (antiquotation "Some (None :: nat option)"))

    val partial =
      checked
        (loop_source "Some(_)"
          (antiquotation "None :: nat option"))
    val (_, partial_condition, partial_body) =
      bounded_while_arguments partial
    val _ =
      audit_assert "a partial while-let pattern lost its false fallback"
        (count_constant \<^const_name>\<open>False\<close> partial = 1)
    val _ =
      audit_assert "a partial while-let moved the source body out of the condition"
        (count_constant
           \<^const_name>\<open>cycle1_while_body_marker\<close>
           partial_condition = 1)
    val _ =
      audit_assert "a partial while-let did not keep skip as the bounded loop body"
        (is_skip partial_body)
  in
    val _ = writeln "Cycle 1 conservative while-let coverage audit passed"
  end
\<close>

end
