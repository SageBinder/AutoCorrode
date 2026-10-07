(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Micro_Rust_Record_Tests
  imports Micro_Rust_Parser_Target
begin

section\<open>Record-generation compatibility\<close>

datatype_record testrec =
  field1 :: integer
  field2 :: bool
micro_rust_record testrec

datatype_record testrec2 =
  field3 :: testrec
  field4 :: \<open>bool option\<close>
micro_rust_record testrec2

datatype_record ('a, 'b) record_autogen_poly =
  record_autogen_poly_value :: 'a
  record_autogen_poly_flag :: bool
  record_autogen_poly_payload :: \<open>'b option\<close>
micro_rust_record record_autogen_poly

datatype_record record_autogen_no_fields =
  record_autogen_no_fields_value :: nat
micro_rust_record [no_fields] record_autogen_no_fields

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun assert message condition =
      if condition then ()
      else error ("record autogen compatibility: " ^ message)

    fun theorem name = Proof_Context.get_thm ctxt name
    fun theorems name = Proof_Context.get_thms ctxt name

    fun schematic_prop prop =
      let
        val params = Term.strip_all_vars prop
        val body = Term.strip_all_body prop
        val frees = map Free params
      in
        Term.subst_bounds (rev frees, body)
        |> Logic.varify_global
      end

    fun assert_prop name expected =
      assert (quote name ^ " proposition changed")
        (Thm.prop_of (theorem name) aconv schematic_prop expected)

    fun same_props [] [] = true
      | same_props (theorem :: theorems) (prop :: props) =
          Thm.prop_of theorem aconv prop andalso same_props theorems props
      | same_props _ _ = false

    fun assert_const_type label name expected =
      assert (label ^ " type changed")
        (Sign.typ_equiv thy
          (Sign.the_const_type thy name, Logic.varifyT_global expected))

    fun assert_localizable label T =
      assert (label ^ " lost its localizable instance")
        (Sign.of_sort thy (T, \<^sort>\<open>localizable\<close>))

    fun named_member collection name =
      Named_Theorems.member ctxt collection (theorem name)

    fun entry_targets name
          ({hol_term, ...} : Micro_Rust_Names.entry) =
      (case hol_term of
         Const (actual, _) => actual = name
       | _ => false)

    val lens_components =
      theorems "testrec_field1_lens_view_update_modify"
    val focus_components =
      theorems "testrec_field1_focus_view_update_modify"
    val field1_entries =
      Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NField "field1"
    val no_fields_entries =
      Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NField
        "record_autogen_no_fields_value"

    val _ =
      assert_const_type "ordinary lens"
        \<^const_name>\<open>testrec_field1_lens\<close>
        \<^typ>\<open>(testrec, integer) lens\<close>
    val _ =
      assert_const_type "ordinary focus"
        \<^const_name>\<open>testrec_field1_focus\<close>
        \<^typ>\<open>(testrec, integer) focus\<close>
    val _ =
      assert_const_type "polymorphic value lens"
        \<^const_name>\<open>record_autogen_poly_record_autogen_poly_value_lens\<close>
        \<^typ>\<open>(('a, 'b) record_autogen_poly, 'a) lens\<close>
    val _ =
      assert_const_type "polymorphic Boolean focus"
        \<^const_name>\<open>record_autogen_poly_record_autogen_poly_flag_focus\<close>
        \<^typ>\<open>(('a, 'b) record_autogen_poly, bool) focus\<close>
    val _ =
      assert_const_type "polymorphic option lens"
        \<^const_name>\<open>record_autogen_poly_record_autogen_poly_payload_lens\<close>
        \<^typ>\<open>(('a, 'b) record_autogen_poly, 'b option) lens\<close>
    val _ =
      assert_const_type "no-fields lens"
        \<^const_name>\<open>record_autogen_no_fields_record_autogen_no_fields_value_lens\<close>
        \<^typ>\<open>(record_autogen_no_fields, nat) lens\<close>

    val _ =
      assert_prop "testrec_field1_update_explicit"
        \<^prop>\<open>\<And>f field1 field2.
          update_field1 f (make_testrec field1 field2) =
            make_testrec (f field1) field2\<close>
    val _ =
      assert_prop "testrec_field1_update_localI"
        \<^prop>\<open>\<And>f g r.
          f (field1 r) = g (field1 r) \<Longrightarrow>
            update_field1 f r = update_field1 g r\<close>

    val _ =
      assert "lens component grouping or order changed"
        (same_props lens_components
          [\<^prop>\<open>lens_view testrec_field1_lens = field1\<close>,
           \<^prop>\<open>lens_modify testrec_field1_lens = update_field1\<close>,
           \<^prop>\<open>lens_update testrec_field1_lens =
             (\<lambda>x. update_field1 (\<lambda>_. x))\<close>])
    val _ =
      assert "focus component theorem grouping changed"
        (length focus_components = 3)

    val _ =
      assert "lens components left micro_rust_record_simps"
        (forall
          (Named_Theorems.member ctxt
            \<^named_theorems>\<open>micro_rust_record_simps\<close>)
          lens_components)
    val _ =
      assert "lens validity left micro_rust_record_intros"
        (named_member \<^named_theorems>\<open>micro_rust_record_intros\<close>
          "testrec_field1_lens_valid")
    val _ =
      assert "explicit update left micro_rust_record_simps"
        (named_member \<^named_theorems>\<open>micro_rust_record_simps\<close>
          "testrec_field1_update_explicit")
    val _ =
      assert "local update left micro_rust_record_intros"
        (named_member \<^named_theorems>\<open>micro_rust_record_intros\<close>
          "testrec_field1_update_localI")
    val _ =
      assert "focus components left focus_components"
        (forall
          (Named_Theorems.member ctxt
            \<^named_theorems>\<open>focus_components\<close>)
          focus_components)

    val _ =
      assert "ordinary field registration changed"
        (length field1_entries = 1 andalso
          entry_targets \<^const_name>\<open>testrec_field1_lens\<close>
            (hd field1_entries))
    val _ =
      assert "[no_fields] registered its field"
        (null no_fields_entries)

    val _ =
      assert_localizable "ordinary record" \<^typ>\<open>testrec\<close>
    val _ =
      assert_localizable "polymorphic record"
        \<^typ>\<open>('a, 'b) record_autogen_poly\<close>
    val _ =
      assert_localizable "no-fields record"
        \<^typ>\<open>record_autogen_no_fields\<close>
  in
  end
\<close>

end
