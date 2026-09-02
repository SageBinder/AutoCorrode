theory Micro_Rust_Parser_Cycle_3_Audit
  imports Micro_Rust_Parser_Cycle_2_Audit
begin

section\<open> Cycle 3 integration audit \<close>

text\<open>
Cycle 3 keeps executable parser-generated fixtures, controlled-normalization stress cases,
source-position regressions, grammar performance checks, and final inventory arithmetic in one
session-ending audit theory.
\<close>

subsection\<open> Lazy matcher code generation \<close>

datatype cycle3_single = Cycle3_Single nat
datatype cycle3_bit = Cycle3_Zero | Cycle3_One

definition cycle3_some_seven :: \<open>nat option\<close>
where
  \<open> cycle3_some_seven = Some 7 \<close>

definition cycle3_none :: \<open>nat option\<close>
where
  \<open> cycle3_none = None \<close>

definition cycle3_some_three :: \<open>nat option\<close>
where
  \<open> cycle3_some_three = Some 3 \<close>

definition cycle3_single_nine :: cycle3_single
where
  \<open> cycle3_single_nine = Cycle3_Single 9 \<close>

definition cycle3_nested_bits ::
  \<open>cycle3_bit \<times> (cycle3_bit \<times> tnil)\<close>
where
  \<open>
    cycle3_nested_bits =
      (Cycle3_One, (Cycle3_Zero, TNil))
  \<close>

definition cycle3_some_nineteen :: \<open>nat option\<close>
where
  \<open> cycle3_some_nineteen = Some 19 \<close>

definition cycle3_some_seven_expression ::
  \<open>(unit, nat option, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_some_seven_expression = literal cycle3_some_seven \<close>

definition cycle3_none_expression ::
  \<open>(unit, nat option, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_none_expression = literal cycle3_none \<close>

definition cycle3_some_three_expression ::
  \<open>(unit, nat option, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_some_three_expression = literal cycle3_some_three \<close>

definition cycle3_single_nine_expression ::
  \<open>(unit, cycle3_single, unit, unit, unit, unit) expression\<close>
where
  \<open>
    cycle3_single_nine_expression =
      literal cycle3_single_nine
  \<close>

definition cycle3_nested_bits_expression ::
  \<open>
    (unit, cycle3_bit \<times> (cycle3_bit \<times> tnil),
      unit, unit, unit, unit) expression
  \<close>
where
  \<open>
    cycle3_nested_bits_expression =
      literal cycle3_nested_bits
  \<close>

definition cycle3_some_nineteen_expression ::
  \<open>(unit, nat option, unit, unit, unit, unit) expression\<close>
where
  \<open>
    cycle3_some_nineteen_expression =
      literal cycle3_some_nineteen
  \<close>

definition cycle3_false_expression ::
  \<open>(unit, bool, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_false_expression = literal False \<close>

urust_expr cycle3_code_constructor
  \<open>
    match \<epsilon>\<open>cycle3_some_seven_expression\<close> {
      Some(value) \<Rightarrow> value,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr cycle3_code_fallthrough
  \<open>
    match \<epsilon>\<open>cycle3_none_expression\<close> {
      Some(value) \<Rightarrow> value,
      None \<Rightarrow> 11
    }
  \<close>

urust_expr cycle3_code_false_guard
  \<open>
    match \<epsilon>\<open>cycle3_some_three_expression\<close> {
      Some(value) if \<epsilon>\<open>cycle3_false_expression\<close> \<Rightarrow> 100,
      Some(value) \<Rightarrow> value,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr cycle3_code_exhaustive
  \<open>
    match \<epsilon>\<open>cycle3_single_nine_expression\<close> {
      Cycle3_Single(value) \<Rightarrow> value
    }
  \<close>

urust_expr cycle3_code_nested_product_or
  \<open>
    match \<epsilon>\<open>cycle3_nested_bits_expression\<close> {
      (Cycle3_Zero | Cycle3_One, Cycle3_One | Cycle3_Zero) \<Rightarrow> 23
    }
  \<close>

urust_expr cycle3_code_lazy_undefined
  \<open>
    match \<epsilon>\<open>cycle3_some_nineteen_expression\<close> {
      Some(value) \<Rightarrow> value
    }
  \<close>

definition cycle3_code_constructor_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_code_constructor_closed = cycle3_code_constructor \<close>

definition cycle3_code_fallthrough_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_code_fallthrough_closed = cycle3_code_fallthrough \<close>

definition cycle3_code_false_guard_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_code_false_guard_closed = cycle3_code_false_guard \<close>

definition cycle3_code_exhaustive_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
where
  \<open> cycle3_code_exhaustive_closed = cycle3_code_exhaustive \<close>

definition cycle3_code_nested_product_or_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
where
  \<open>
    cycle3_code_nested_product_or_closed =
      cycle3_code_nested_product_or
  \<close>

definition cycle3_code_lazy_undefined_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
where
  \<open>
    cycle3_code_lazy_undefined_closed =
      cycle3_code_lazy_undefined
  \<close>

lemma cycle3_code_constructor_result:
  \<open> evaluate cycle3_code_constructor_closed () = Success 7 () \<close>
  by eval

lemma cycle3_code_fallthrough_result:
  \<open> evaluate cycle3_code_fallthrough_closed () = Success 11 () \<close>
  by eval

lemma cycle3_code_false_guard_result:
  \<open> evaluate cycle3_code_false_guard_closed () = Success 3 () \<close>
  by eval

lemma cycle3_code_exhaustive_result:
  \<open> evaluate cycle3_code_exhaustive_closed () = Success 9 () \<close>
  by eval

lemma cycle3_code_nested_product_or_result:
  \<open>
    evaluate cycle3_code_nested_product_or_closed () =
      Success 23 ()
  \<close>
  by eval

lemma cycle3_code_lazy_undefined_result:
  \<open>
    evaluate cycle3_code_lazy_undefined_closed () =
      Success 19 ()
  \<close>
  by eval

value [code]
  \<open> evaluate cycle3_code_constructor_closed () \<close>

value [code]
  \<open> evaluate cycle3_code_fallthrough_closed () \<close>

value [code]
  \<open> evaluate cycle3_code_false_guard_closed () \<close>

value [code]
  \<open> evaluate cycle3_code_exhaustive_closed () \<close>

value [code]
  \<open> evaluate cycle3_code_nested_product_or_closed () \<close>

value [code]
  \<open> evaluate cycle3_code_lazy_undefined_closed () \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 3 code audit: " ^ message)

    val generated =
      [\<^const_name>\<open>cycle3_code_constructor\<close>,
       \<^const_name>\<open>cycle3_code_fallthrough\<close>,
       \<^const_name>\<open>cycle3_code_false_guard\<close>,
       \<^const_name>\<open>cycle3_code_exhaustive\<close>,
       \<^const_name>\<open>cycle3_code_nested_product_or\<close>,
       \<^const_name>\<open>cycle3_code_lazy_undefined\<close>]

    fun definition_theorem constant =
      Proof_Context.get_thm ctxt
        (Long_Name.base_name constant ^ "_def")

    fun executable_equations constant =
      let
        val certificate = Code.get_cert ctxt [] constant
        val (_, equations) =
          Code.equations_of_cert thy certificate
      in
        map_filter
          (fn (_, (SOME theorem, _)) => SOME theorem
            | _ => NONE)
          (the equations)
      end

    fun check_generated constant =
      let
        val definition = definition_theorem constant
        val equations = executable_equations constant
        val code_equation = the_single equations
        val unoverloaded_definition =
          Axclass.unoverload ctxt definition
      in
        audit_assert
          ("expected one default equation for " ^ quote constant)
          (length equations = 1);
        audit_assert
          ("default equation differs from the definition for " ^
            quote constant ^
            "\ndefinition: " ^
            Thm.string_of_thm ctxt definition ^
            "\ncode:       " ^
            Thm.string_of_thm ctxt code_equation)
          (Thm.equiv_thm thy
            (code_equation, unoverloaded_definition))
      end

    val _ = List.app check_generated generated

    val matcher_code =
      Named_Theorems.get ctxt
        \<^named_theorems>\<open>urust_matcher_code\<close>
    val expected_matcher_code =
      @{thms urust_matcher_code_definitions}
    val _ =
      audit_assert "urust_matcher_code has the wrong cardinality"
        (length matcher_code = length expected_matcher_code)
    val _ =
      audit_assert "urust_matcher_code has the wrong theorem identity"
        (eq_set Thm.eq_thm_prop
          (matcher_code, expected_matcher_code))

    val parser_definitions =
      Named_Theorems.get ctxt
        \<^named_theorems>\<open>urust_parser_definitions\<close>
    val _ =
      List.app
        (fn constant =>
          let
            val definition = definition_theorem constant
          in
            audit_assert
              ("parser definition collection omitted " ^
                quote constant)
              (length
                (filter
                  (Thm.eq_thm_prop o pair definition)
                  parser_definitions) = 1)
          end)
        generated
  in
    val _ =
      writeln
        "Cycle 3 parser-generated default-code equations passed"
  end
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val lthy = Named_Target.theory_init thy
    val probe = "cycle3_failed_definition_probe"
    val generated =
      [\<^const_name>\<open>cycle3_code_constructor\<close>,
       \<^const_name>\<open>cycle3_code_fallthrough\<close>,
       \<^const_name>\<open>cycle3_code_false_guard\<close>,
       \<^const_name>\<open>cycle3_code_exhaustive\<close>,
       \<^const_name>\<open>cycle3_code_nested_product_or\<close>,
       \<^const_name>\<open>cycle3_code_lazy_undefined\<close>]

    fun executable_equations context constant =
      let
        val theory = Proof_Context.theory_of context
        val certificate = Code.get_cert context [] constant
        val (_, equations) =
          Code.equations_of_cert theory certificate
      in
        map_filter
          (fn (_, (SOME theorem, _)) => SOME theorem
            | _ => NONE)
          (the equations)
      end

    val before_inventory = URust_Inventory.counts thy
    val before_definitions =
      Named_Theorems.get ctxt
        \<^named_theorems>\<open>urust_parser_definitions\<close>
    val before_code_equations =
      map (executable_equations ctxt) generated

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 3 rollback audit: " ^ message)

    val attempt =
      Exn.result
        (fn () =>
          define_urust_with_frontend_check
            URust_Inventory.Explicit_Old_Conformance
            (Binding.name probe,
             Input.string "1",
             "\<lbrakk> True \<rbrakk>")
            lthy) ()

    val _ =
      (case attempt of
         Exn.Res _ =>
           error "Cycle 3 rollback audit: failing definition succeeded"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())

    val after_inventory = URust_Inventory.counts thy
    val after_definitions =
      Named_Theorems.get ctxt
        \<^named_theorems>\<open>urust_parser_definitions\<close>
    val after_code_equations =
      map (executable_equations ctxt) generated
    val _ =
      audit_assert "failed definition leaked a constant"
        (not (Sign.declared_const thy probe))
    val _ =
      audit_assert "failed definition changed the parser inventory"
        (URust_Inventory.equal_counts
          before_inventory after_inventory)
    val _ =
      audit_assert "failed definition changed parser-definition state"
        (eq_list Thm.eq_thm_prop
          (before_definitions, after_definitions))
    val _ =
      audit_assert "failed definition changed default code equations"
        (eq_list
          (eq_list Thm.eq_thm_prop)
          (before_code_equations, after_code_equations))
    val _ =
      audit_assert "failed definition leaked a code certificate"
        (not (can (Code.get_cert ctxt []) probe))
  in
    val _ =
      writeln
        "Cycle 3 failed-command inventory/code rollback passed"
  end
\<close>

end
