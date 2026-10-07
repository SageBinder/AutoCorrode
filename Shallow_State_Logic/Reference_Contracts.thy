(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Reference_Contracts
  imports
    Shallow_State.Global_Store
    Assertion_Language
begin

section\<open>Generic reference contracts\<close>

datatype_record ('state, 'result) reference_contract =
  reference_contract_pre :: \<open>'state assert\<close>
  reference_contract_post :: \<open>'result \<Rightarrow> 'state assert\<close>

locale reference_contracts =
  fixes reference_types ::
      \<open>'state::sepalg \<Rightarrow> 'address \<Rightarrow> 'cell \<Rightarrow> unit\<close>
    and points_to_raw' ::
      \<open>('address, 'cell) gref \<Rightarrow> share \<Rightarrow> 'cell \<Rightarrow> 'state assert\<close>
    and gref_can_store :: \<open>('address, 'cell) gref \<Rightarrow> 'cell set\<close>
    and new_gref_can_store :: \<open>'cell set\<close>
    and can_alloc_reference :: \<open>'state assert\<close>
begin

definition points_to_raw where
  \<open>points_to_raw \<equiv> points_to_raw'\<close>

notation points_to_raw ("(_) \<mapsto>\<langle>_\<rangle> (_)" [69, 0, 69] 70)

definition update_raw_contract ::
    \<open>('address, 'cell) gref \<Rightarrow> 'cell \<Rightarrow> 'cell \<Rightarrow>
      ('state, unit) reference_contract\<close>
  where
    \<open>update_raw_contract r old new \<equiv>
      make_reference_contract
        (\<langle>new \<in> gref_can_store r\<rangle> \<star> r \<mapsto>\<langle>\<top>\<rangle> old)
        (\<lambda>_. r \<mapsto>\<langle>\<top>\<rangle> new)\<close>

definition dereference_raw_contract ::
    \<open>('address, 'cell) gref \<Rightarrow> share \<Rightarrow> 'cell \<Rightarrow>
      ('state, 'cell) reference_contract\<close>
  where
    \<open>dereference_raw_contract r sh value \<equiv>
      make_reference_contract
        (r \<mapsto>\<langle>sh\<rangle> value)
        (\<lambda>result. r \<mapsto>\<langle>sh\<rangle> value \<star> \<langle>value = result\<rangle>)\<close>

definition allocation_contract ::
    \<open>'cell \<Rightarrow> ('state, ('address, 'cell) gref) reference_contract\<close>
  where
    \<open>allocation_contract value \<equiv>
      make_reference_contract
        (can_alloc_reference \<star> \<langle>value \<in> new_gref_can_store\<rangle>)
        (\<lambda>r. r \<mapsto>\<langle>\<top>\<rangle> value \<star>
          \<langle>new_gref_can_store \<subseteq> gref_can_store r\<rangle> \<star>
          can_alloc_reference)\<close>

definition is_valid_ref_for ::
    \<open>('address, 'cell, 'value) State_References.ref \<Rightarrow> 'cell set \<Rightarrow> bool\<close>
  where
    \<open>is_valid_ref_for r values \<equiv> focus_dom (get_focus r) \<subseteq> values\<close>

lemma is_valid_ref_for_focus_reference [focus_intros]:
  assumes \<open>is_valid_ref_for r values\<close>
  shows \<open>is_valid_ref_for (focus_reference f r) values\<close>
  using assms
  by (simp add: is_valid_ref_for_def focus_factors_trans focus_focused_get_focus)

abbreviation points_to_localizes where
  \<open>points_to_localizes r cell value \<equiv>
    is_valid_ref_for r (gref_can_store (unwrap_focused r)) \<and>
    focus_view (get_focus r) cell = Some value\<close>

definition points_to ::
    \<open>('address, 'cell, 'value) State_References.ref \<Rightarrow>
      share \<Rightarrow> 'cell \<Rightarrow> 'value \<Rightarrow> 'state assert\<close>
  where
    \<open>points_to r sh cell value \<equiv>
      points_to_raw (unwrap_focused r) sh cell \<star>
      \<langle>points_to_localizes r cell value\<rangle>\<close>

notation points_to ("(_) \<mapsto>\<langle>_\<rangle>/_/\<down> (_)" [69, 0, 69, 69] 70)

end

end
