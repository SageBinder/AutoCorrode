(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory State_References
  imports
    Lenses_And_Other_Optics.Lenses_And_Other_Optics
    Misc.Array
    Misc.Vector
begin

section\<open>References into abstract stores\<close>

text\<open>A raw reference carries an address and records the store's cell type in its
HOL type. A typed reference additionally carries a focus describing how a cell
contains a value.\<close>

datatype_record ('address, 'cell) gref =
  gref_address :: \<open>'address\<close>

datatype ('address, 'cell) ro_gref =
  ROGRef (unsafe_gref_from_ro_gref: \<open>('address, 'cell) gref\<close>)

type_synonym ('address, 'cell, 'value) ref =
  \<open>(('address, 'cell) gref, 'cell, 'value) focused\<close>

type_synonym ('address, 'cell, 'value) ro_ref =
  \<open>(('address, 'cell) ro_gref, 'cell, 'value) focused\<close>

abbreviation untype_ref where
  \<open>untype_ref \<equiv> unwrap_focused\<close>

abbreviation untype_roref where
  \<open>untype_roref \<equiv> unwrap_focused\<close>

translations
  "CONST unwrap_focused" \<leftharpoondown> "CONST untype_ref"
  "CONST unwrap_focused" \<leftharpoondown> "CONST untype_roref"

definition ro_ref_from_ref ::
    \<open>('address, 'cell, 'value) ref \<Rightarrow> ('address, 'cell, 'value) ro_ref\<close>
  where \<open>ro_ref_from_ref \<equiv> update_unwrap_focused ROGRef\<close>

definition unsafe_ref_from_ro_ref ::
    \<open>('address, 'cell, 'value) ro_ref \<Rightarrow> ('address, 'cell, 'value) ref\<close>
  where
    \<open>unsafe_ref_from_ro_ref \<equiv>
       update_unwrap_focused unsafe_gref_from_ro_gref\<close>

abbreviation ref_address ::
    \<open>('address, 'cell, 'value) ref \<Rightarrow> 'address\<close>
  where \<open>ref_address r \<equiv> gref_address (unwrap_focused r)\<close>

abbreviation ro_address ::
    \<open>('address, 'cell, 'value) ro_ref \<Rightarrow> 'address\<close>
  where
    \<open>ro_address r \<equiv>
       gref_address (unsafe_gref_from_ro_gref (unwrap_focused r))\<close>

consts address :: \<open>'a \<Rightarrow> 'b\<close>

adhoc_overloading
  address \<rightleftharpoons> gref_address ref_address ro_address

definition make_untyped_ref ::
    \<open>'address \<Rightarrow> ('address, 'cell) gref\<close>
  where \<open>make_untyped_ref addr \<equiv> make_gref addr\<close>

abbreviation make_ref_typed_from_untyped ::
    \<open>('address, 'cell) gref \<Rightarrow>
      ('cell, 'value) focus \<Rightarrow>
      ('address, 'cell, 'value) ref\<close>
  where \<open>make_ref_typed_from_untyped \<equiv> make_focused\<close>

definition make_ro_ref_typed_from_untyped ::
    \<open>('address, 'cell) ro_gref \<Rightarrow>
      ('cell, 'value) focus \<Rightarrow>
      ('address, 'cell, 'value) ro_ref\<close>
  where \<open>make_ro_ref_typed_from_untyped \<equiv> make_focused\<close>

subsection\<open>Focused references\<close>

abbreviation focus_reference ::
    \<open>('value, 'subvalue) focus \<Rightarrow>
      ('address, 'cell, 'value) ref \<Rightarrow>
      ('address, 'cell, 'subvalue) ref\<close>
  where \<open>focus_reference \<equiv> focus_focused\<close>

abbreviation focus_reference_via_lens where
  \<open>focus_reference_via_lens l \<equiv>
     focus_reference (lens_to_focus l)\<close>

lemmas focus_reference_def = focus_focused_def

abbreviation (input) focus_option ::
    \<open>('address, 'cell, 'value option) ref \<Rightarrow>
      ('address, 'cell, 'value) ref\<close>
  where \<open>focus_option \<equiv> focus_focused option_focus\<close>

abbreviation (input) focus_result_ok ::
    \<open>('address, 'cell, ('value, 'error) result) ref \<Rightarrow>
      ('address, 'cell, 'value) ref\<close>
  where \<open>focus_result_ok \<equiv> focus_focused result_ok_focus\<close>

abbreviation (input) focus_result_err ::
    \<open>('address, 'cell, ('value, 'error) result) ref \<Rightarrow>
      ('address, 'cell, 'error) ref\<close>
  where \<open>focus_result_err \<equiv> focus_focused result_err_focus\<close>

abbreviation (input) focus_nth ::
    \<open>nat \<Rightarrow>
      ('address, 'cell, 'value list) ref \<Rightarrow>
      ('address, 'cell, 'value) ref\<close>
  where \<open>focus_nth n \<equiv> focus_focused (nth_focus n)\<close>

abbreviation (input) focus_nth_array ::
    \<open>nat \<Rightarrow>
      ('address, 'cell, ('value, 'length::len) array) ref \<Rightarrow>
      ('address, 'cell, 'value) ref\<close>
  where \<open>focus_nth_array n \<equiv> focus_focused (nth_focus_array n)\<close>

abbreviation (input) focus_nth_vector ::
    \<open>nat \<Rightarrow>
      ('address, 'cell, ('value, 'length::len) vector) ref \<Rightarrow>
      ('address, 'cell, 'value) ref\<close>
  where \<open>focus_nth_vector n \<equiv> focus_focused (nth_focus_vector n)\<close>

definition focus_raw_reference ::
    \<open>('cell, 'value) focus \<Rightarrow>
      ('address, 'cell) gref \<Rightarrow>
      ('address, 'cell, 'value) ref\<close>
  where \<open>focus_raw_reference f r \<equiv> make_focused r f\<close>

end
