(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Reference_Separation_Rules
  imports Reference_Contracts
begin

section\<open>Generic separation-logic rules for references\<close>

named_theorems state_reference_specs

definition reference_triple ::
    \<open>('state::sepalg \<Rightarrow> 'result \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow>
      'state assert \<Rightarrow> ('result \<Rightarrow> 'state assert) \<Rightarrow> bool\<close>
  where
    \<open>reference_triple transition pre post \<equiv>
      \<forall>frame. ucincl frame \<longrightarrow>
        (\<forall>state result state'.
          transition state result state' \<longrightarrow>
          state \<Turnstile> pre \<star> frame \<longrightarrow>
          state' \<Turnstile> post result \<star> frame)\<close>

definition satisfies_reference_contract ::
    \<open>('state::sepalg \<Rightarrow> 'result \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow>
      ('state, 'result) reference_contract \<Rightarrow> bool\<close>
  where
    \<open>satisfies_reference_contract transition contract \<equiv>
      ucincl (reference_contract_pre contract) \<and>
      (\<forall>result. ucincl (reference_contract_post contract result)) \<and>
      reference_triple transition
        (reference_contract_pre contract)
        (reference_contract_post contract)\<close>

lemma reference_tripleI:
  assumes \<open>\<And>frame state result state'.
    ucincl frame \<Longrightarrow>
    transition state result state' \<Longrightarrow>
    state \<Turnstile> pre \<star> frame \<Longrightarrow>
    state' \<Turnstile> post result \<star> frame\<close>
  shows \<open>reference_triple transition pre post\<close>
  using assms by (auto simp add: reference_triple_def)

lemma reference_tripleE:
  assumes \<open>reference_triple transition pre post\<close>
      and \<open>ucincl frame\<close>
      and \<open>transition state result state'\<close>
      and \<open>state \<Turnstile> pre \<star> frame\<close>
  shows \<open>state' \<Turnstile> post result \<star> frame\<close>
  using assms by (auto simp add: reference_triple_def)

lemma reference_triple_consequence:
  assumes \<open>pre \<longlongrightarrow> pre'\<close>
      and \<open>reference_triple transition pre' post'\<close>
      and \<open>\<And>result. post' result \<longlongrightarrow> post result\<close>
  shows \<open>reference_triple transition pre post\<close>
proof (rule reference_tripleI)
  fix frame state result state'
  assume frame: \<open>ucincl frame\<close>
    and transition: \<open>transition state result state'\<close>
    and state: \<open>state \<Turnstile> pre \<star> frame\<close>
  have \<open>pre \<star> frame \<longlongrightarrow> pre' \<star> frame\<close>
    using assms(1) by (rule asepconj_mono2)
  have \<open>state \<Turnstile> pre' \<star> frame\<close>
    using state \<open>pre \<star> frame \<longlongrightarrow> pre' \<star> frame\<close>
    by (auto simp add: aentails_def)
  then have \<open>state' \<Turnstile> post' result \<star> frame\<close>
    using assms(2) frame transition
    by (auto simp add: reference_triple_def)
  moreover have \<open>post' result \<star> frame \<longlongrightarrow> post result \<star> frame\<close>
    using assms(3) by (rule asepconj_mono2)
  then show \<open>state' \<Turnstile> post result \<star> frame\<close>
    using calculation by (auto simp add: aentails_def)
qed

lemma reference_triple_frame_rule:
  assumes \<open>reference_triple transition pre post\<close>
      and \<open>ucincl extra\<close>
  shows \<open>reference_triple transition
    (pre \<star> extra) (\<lambda>result. post result \<star> extra)\<close>
proof (rule reference_tripleI)
  fix frame state result state'
  assume frame: \<open>ucincl frame\<close>
    and transition: \<open>transition state result state'\<close>
    and state: \<open>state \<Turnstile> (pre \<star> extra) \<star> frame\<close>
  have \<open>ucincl (extra \<star> frame)\<close>
    using assms(2) by (rule ucincl_asepconjL)
  moreover have \<open>state \<Turnstile> pre \<star> (extra \<star> frame)\<close>
    using state by (simp add: asepconj_assoc)
  ultimately have \<open>state' \<Turnstile> post result \<star> (extra \<star> frame)\<close>
    using assms(1) transition
    by (auto simp add: reference_triple_def)
  then show \<open>state' \<Turnstile> (post result \<star> extra) \<star> frame\<close>
    by (simp add: asepconj_assoc)
qed

locale reference =
  reference_contracts reference_types points_to_raw' gref_can_store
    new_gref_can_store can_alloc_reference
  for reference_types ::
      \<open>'state::sepalg \<Rightarrow> 'address \<Rightarrow> 'cell \<Rightarrow> unit\<close>
    and points_to_raw' gref_can_store new_gref_can_store can_alloc_reference +
  fixes update_raw ::
      \<open>('address, 'cell) gref \<Rightarrow> 'cell \<Rightarrow>
        'state \<Rightarrow> unit \<Rightarrow> 'state \<Rightarrow> bool\<close>
    and dereference_raw ::
      \<open>('address, 'cell) gref \<Rightarrow>
        'state \<Rightarrow> 'cell \<Rightarrow> 'state \<Rightarrow> bool\<close>
    and allocate_reference ::
      \<open>'cell \<Rightarrow>
        'state \<Rightarrow> ('address, 'cell) gref \<Rightarrow> 'state \<Rightarrow> bool\<close>
  assumes update_raw_spec [state_reference_specs]:
      \<open>satisfies_reference_contract
        (update_raw r new) (update_raw_contract r old new)\<close>
    and dereference_raw_spec [state_reference_specs]:
      \<open>satisfies_reference_contract
        (dereference_raw r) (dereference_raw_contract r sh value)\<close>
    and allocate_reference_spec [state_reference_specs]:
      \<open>satisfies_reference_contract
        (allocate_reference value) (allocation_contract value)\<close>
    and ucincl_points_to_raw [ucincl_intros, state_reference_specs]:
      \<open>\<And>r sh value. ucincl (points_to_raw r sh value)\<close>
    and ucincl_can_alloc_reference [ucincl_intros, state_reference_specs]:
      \<open>ucincl can_alloc_reference\<close>
    and points_to_raw_combine [state_reference_specs]:
      \<open>\<And>r sh1 sh2 value1 value2.
        r \<mapsto>\<langle>sh1\<rangle> value1 \<star> r \<mapsto>\<langle>sh2\<rangle> value2
          \<longlongrightarrow>
        r \<mapsto>\<langle>sh1 + sh2\<rangle> value1 \<star> \<langle>value1 = value2\<rangle>\<close>
    and points_to_raw_split [state_reference_specs]:
      \<open>\<And>sh sh1 sh2 r value.
        sh = sh1 + sh2 \<Longrightarrow>
        sh1 \<sharp> sh2 \<Longrightarrow>
        0 < sh1 \<Longrightarrow>
        0 < sh2 \<Longrightarrow>
        r \<mapsto>\<langle>sh\<rangle> value
          \<longlongrightarrow>
        r \<mapsto>\<langle>sh1\<rangle> value \<star> r \<mapsto>\<langle>sh2\<rangle> value\<close>
begin

lemma points_to_raw'_ucincl [ucincl_intros]:
  \<open>ucincl (points_to_raw' r sh value)\<close>
  using ucincl_points_to_raw by (simp add: points_to_raw_def)

lemma points_to_raw_aentails [intro]:
  assumes \<open>value0 = value1\<close>
  shows \<open>r \<mapsto>\<langle>sh\<rangle> value0 \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> value1\<close>
  using assms by (simp add: aentails_refl)

lemma points_to_aentails [intro]:
  assumes \<open>cell0 = cell1\<close> and \<open>value0 = value1\<close>
  shows \<open>r \<mapsto>\<langle>sh\<rangle> cell0\<down>value0
    \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> cell1\<down>value1\<close>
  using assms by (simp add: aentails_refl)

lemma aentails_split_single_points_to_assm:
  assumes \<open>points_to_localizes r cell value \<Longrightarrow>
    \<flat>r \<mapsto>\<langle>sh\<rangle> cell \<longlongrightarrow> \<phi>\<close>
  shows \<open>r \<mapsto>\<langle>sh\<rangle> cell\<down>value \<longlongrightarrow> \<phi>\<close>
  by (metis (full_types) apure_entailsL asepconj_comm assms
      points_to_def ucincl_points_to_raw)

lemma aentails_split_top_points_to_assm:
  assumes \<open>points_to_localizes r cell value \<Longrightarrow>
    \<flat>r \<mapsto>\<langle>sh\<rangle> cell \<star> \<psi> \<longlongrightarrow> \<phi>\<close>
  shows \<open>r \<mapsto>\<langle>sh\<rangle> cell\<down>value \<star> \<psi> \<longlongrightarrow> \<phi>\<close>
  by (metis aentails_split_single_points_to_assm assms awand_adjoint)

lemma aentails_cancel_points_to_raw_with_typed:
  assumes \<open>raw = \<flat>r\<close>
      and \<open>cell' = cell\<close>
      and \<open>\<psi> \<longlongrightarrow> \<langle>points_to_localizes r cell value\<rangle> \<star> \<phi>\<close>
  shows \<open>raw \<mapsto>\<langle>sh\<rangle> cell' \<star> \<psi>
    \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> cell\<down>value \<star> \<phi>\<close>
  using assms points_to_def
  by (metis (no_types, lifting) asepconj_assoc asepconj_mono)

end

end
