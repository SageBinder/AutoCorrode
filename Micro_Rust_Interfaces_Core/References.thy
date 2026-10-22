(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory References
  imports 
    Shallow_Separation_Logic.Assertion_Language 
    Shallow_Separation_Logic.Tree_Shares
    Shallow_Separation_Logic.Triple 
    Shallow_Separation_Logic.Weakest_Precondition
    Shallow_Micro_Rust.Core_Expression
    Shallow_Micro_Rust.Numeric_Types
    Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

(*>*)

named_theorems reference_axioms

locale reference_defs = 
  fixes reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i \<Rightarrow> 'o \<Rightarrow> unit\<close>

    and update_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
    and dereference_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
    and reference_raw_fun :: \<open>'b \<Rightarrow> ('s, ('a, 'b) gref, 'abort, 'i, 'o) function_body\<close>

    and points_to_raw' :: \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 's assert\<close> 

    and gref_can_store :: \<open>('a, 'b) gref \<Rightarrow> 'b set\<close>
    and new_gref_can_store :: \<open>'b set\<close>

    and reference_stack ::
      \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) gref list \<Rightarrow> 's assert\<close>
begin

named_theorems all_reference_defs'

abbreviation reference_stack_unrestricted ::
    \<open>('a, 'b) gref list \<Rightarrow> 's assert\<close>
    (\<open>reference'_stack\<^sub>\<top> _\<close> [1000] 1000)
  where
  \<open>reference_stack\<^sub>\<top> \<Phi> \<equiv> reference_stack (\<lambda>_. True) \<Phi>\<close>

definition [all_reference_defs']: \<open>points_to_raw \<equiv> points_to_raw'\<close>
notation points_to_raw ("(_) \<mapsto> \<langle>_\<rangle> (_)" [69,0,69]70)

text\<open>Specifications\<close>

definition update_raw_contract :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>update_raw_contract r g0 g \<equiv>
     let pre = \<langle>g \<in> gref_can_store r\<rangle> \<star> points_to_raw r \<top> g0 in
     let post = \<lambda>_. (points_to_raw r \<top> g) in
     make_function_contract pre post\<close>

definition reference_raw_contract ::
    \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) gref list \<Rightarrow> 'b \<Rightarrow>
      ('s, ('a, 'b) gref, 'abort) function_contract\<close>
  where [all_reference_defs']:
  \<open>reference_raw_contract F \<Phi> g \<equiv>
    let pre =
          reference_stack F \<Phi> \<star>
          \<langle>g \<in> new_gref_can_store\<rangle>;
        post = \<lambda>r.
          points_to_raw r \<top> g \<star>
          \<langle>new_gref_can_store \<subseteq> gref_can_store r\<rangle> \<star>
          reference_stack F (\<Phi> @ [r])
    in make_function_contract pre post\<close>

definition dereference_raw_contract 
  :: \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> ('s, 'b, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>dereference_raw_contract r sh g \<equiv>
     let pre = points_to_raw r sh g in
     let post = \<lambda>g'. (points_to_raw r sh g \<star> \<langle>g=g'\<rangle>) in
     make_function_contract pre post\<close>

text\<open>Lifting the raw reference operations to typed ones using foci:\<close>

urust_fn [attrs = [all_reference_defs'], register_notation = false] \<open>
  fn reference_fun(p: \<tau>\<open>('b, 'v) prism\<close>, e: \<tau>\<open>'v\<close>) -> \<tau>\<open>('a, 'b, 'v) Global_Store.ref\<close> {
    let r = reference_raw_fun (\<llangle>prism_embed p e\<rrangle>);
    \<llangle>make_ref_typed_from_untyped\<rrangle>\<^sub>2(r, \<llangle>prism_to_focus p\<rrangle>)
  }
  \<close>

\<comment>\<open>\<^verbatim>\<open>prism_to_focus p\<close> has no (unconditional) code equations. Instead, specific instances of
for valid \<^verbatim>\<open>p\<close> have to be wrapped as definitions and given code equations by instantiating
\<^verbatim>\<open>prism_to_focus.rep_eq\<close>. However, those specialized code equations will only be recognized 
during code generation if \<^verbatim>\<open>reference_fun\<close> is inlined -- thus the need for \<^verbatim>\<open>code_unfold\<close>.\<close>
declare reference_fun_def[code_unfold]

urust_fn [attrs = [all_reference_defs'], register_notation = false] \<open>
  fn modify_raw_fun(r: \<tau>\<open>('a, 'b) gref\<close>, f: \<tau>\<open>('b \<Rightarrow> 'b)\<close>) -> () {
    let g = dereference_raw_fun(r);
    update_raw_fun(r, \<llangle>f\<rrangle>\<^sub>1(g))
  }
  \<close>

urust_fn [attrs = [all_reference_defs'], register_notation = false] \<open>
  fn modify_fun(ref_value: \<tau>\<open>('a, 'b, 'v) Global_Store.ref\<close>, f: \<tau>\<open>('v \<Rightarrow> 'v)\<close>) -> () {
    modify_raw_fun (\<llangle>untype_ref\<rrangle>\<^sub>1(ref_value), \<llangle>focus_modify (get_focus ref_value) f\<rrangle>)
  }
  \<close>

urust_fn [attrs = [all_reference_defs'], register_notation = false] \<open> fn update_fun(ref_value: \<tau>\<open>('a, 'b, 'v) Global_Store.ref\<close>, v: \<tau>\<open>'v\<close>) -> () { modify_fun(ref_value, \<llangle>\<lambda>_. v\<rrangle>) } \<close>

urust_fn [attrs = [all_reference_defs'], register_notation = false] \<open>
  fn dereference_fun(ref_value: \<tau>\<open>('a, 'b, 'v) Global_Store.ref\<close>) -> \<tau>\<open>'v\<close> {
    let b = dereference_raw_fun(\<llangle>untype_ref\<rrangle>\<^sub>1(ref_value));
    match (\<llangle>focus_view (\<integral> ref_value) b\<rrangle>) {
      None \<Rightarrow> \<epsilon>\<open>abort TypeError\<close>,
      Some(v) \<Rightarrow> v
    }
  }
  \<close>

urust_fn [attrs = [all_reference_defs'], register_notation = false] \<open> fn ro_dereference_fun(r: \<tau>\<open>('a, 'b, 'v) ro_ref\<close>) -> \<tau>\<open>'v\<close> { dereference_fun(\<llangle>unsafe_ref_from_ro_ref\<rrangle>\<^sub>1(r)) } \<close>

\<comment>\<open>Generic compound-assignment helper backing the \<^verbatim>\<open>+=\<close> surface syntax.
   Uses the checked uRust addition (\<^const>\<open>word_add_no_wrap\<close>), so it panics on
   overflow -- matching the checked \<^verbatim>\<open>-=\<close> lowering and the \<^verbatim>\<open>ref = *ref + addend\<close>
   helper it replaces. Calls \<^const>\<open>update_fun\<close> / \<^const>\<open>dereference_fun\<close> directly rather
   than the surface \<^verbatim>\<open>=\<close>/\<^verbatim>\<open>*\<close>, whose store overloads are not in scope in this locale.
   Overload \<^const>\<open>assign_add_const\<close> onto this where \<^verbatim>\<open>+=\<close> is used.\<close>
urust_fn [register_notation = false] \<open>
  fn assign_add_ref(ref_value: \<tau>\<open>('a, 'b, 'l::{len} word) ref\<close>, addend: \<tau>\<open>'l word\<close>) -> () {
    let current = dereference_fun(ref_value);
    update_fun(ref_value, current + addend)
  }
  \<close>

definition is_valid_ref_for :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b set \<Rightarrow> bool\<close>
  where \<open>is_valid_ref_for r P \<equiv> focus_dom (get_focus r) \<subseteq> P\<close>

lemma is_valid_ref_for_compose[focus_intros]:
  assumes \<open>is_valid_ref_for r P\<close>
  shows \<open>is_valid_ref_for (focus_reference f r) P\<close> 
  using assms by (simp add: is_valid_ref_for_def focus_factors_trans focus_focused_get_focus)

abbreviation points_to_localizes :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> bool\<close> where
  \<open>points_to_localizes r b v \<equiv> is_valid_ref_for r (gref_can_store (unwrap_focused r)) 
                                \<and> focus_view (get_focus r) b = Some v\<close>

definition points_to :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 's assert\<close> where
  [all_reference_defs']: \<open>points_to r sh b v \<equiv>
    points_to_raw (unwrap_focused r) sh b \<star> \<langle>points_to_localizes r b v\<rangle>\<close>

notation points_to ("(_) \<mapsto> \<langle>_\<rangle>/_/ \<down>/ _" [69,0,69,69]70)

abbreviation points_to_modified :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> share \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 's assert\<close> where
  \<open>points_to_modified r sh op b v \<equiv> points_to r sh (focus_modify (get_focus r) op b) (op v) \<star>
   \<langle>points_to_localizes r b v\<rangle>\<close>

notation points_to_modified ("(_) \<mapsto> \<langle>_\<rangle>/ _\<sqdot> '(_\<down>_')" [69,0,69,69,69]70)

definition modify_raw_contract :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>modify_raw_contract r g f \<equiv>
     let pre = \<langle>f g \<in> gref_can_store r\<rangle> \<star> points_to_raw r \<top> g in
     let post = \<lambda>_. (points_to_raw r \<top> (f g)) in
     make_function_contract pre post\<close>

definition update_contract :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>update_contract r g0 v0 v \<equiv>
     let pre = points_to r \<top> g0 v0 in
     let post = \<lambda>_. points_to_modified r \<top> (\<lambda>_. v) g0 v0 in
     make_function_contract pre post\<close>

definition modify_contract :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('s, unit, 'abort) function_contract\<close> 
  where [all_reference_defs']: \<open>modify_contract r g0 v0 f \<equiv>
     let pre = points_to r \<top> g0 v0 in
     let post = \<lambda>_. (points_to_modified r \<top> f g0 v0) in
     make_function_contract pre post\<close>

definition dereference_contract 
  :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('s, 'v, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>dereference_contract r sh g v \<equiv>
     let pre = points_to r sh g v in
     let post = \<lambda>v'. (points_to r sh g v \<star> \<langle>v=v'\<rangle>) in
     make_function_contract pre post\<close>

definition ro_dereference_contract
  :: \<open>('a, 'b, 'v) ro_ref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> ('s, 'v, 'abort) function_contract\<close> where 
  [all_reference_defs']: \<open>ro_dereference_contract r sh g v \<equiv>
     let pre = points_to (unsafe_ref_from_ro_ref r) sh g v in
     let post = \<lambda>v'. points_to (unsafe_ref_from_ro_ref r) sh g v \<star> \<langle>v=v'\<rangle> in
     make_function_contract pre post\<close>

definition reference_contract ::
    \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) gref list \<Rightarrow>
      ('b, 'v) prism \<Rightarrow> 'v \<Rightarrow>
      ('s, ('a, 'b, 'v) Global_Store.ref, 'abort) function_contract\<close>
  where [all_reference_defs']:
  \<open>reference_contract F \<Phi> p v \<equiv>
    let pre = reference_stack F \<Phi>;
        post = \<lambda>r.
          points_to r \<top> (prism_embed p v) v \<star>
          \<langle>\<integral>r = prism_to_focus p\<rangle> \<star>
          reference_stack F (\<Phi> @ [\<flat> r])
    in make_function_contract pre post\<close>

lemmas all_reference_defs = all_reference_defs'
named_theorems all_reference_specs

end

locale reference = reference_defs reference_types 
    update_raw_fun 
    dereference_raw_fun
    reference_raw_fun
    points_to_raw'
    gref_can_store
    new_gref_can_store
    reference_stack
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> 
    and update_raw_fun dereference_raw_fun reference_raw_fun points_to_raw' gref_can_store 
      new_gref_can_store reference_stack +

  assumes update_raw_spec [all_reference_specs]:      \<open>\<Gamma> ; update_raw_fun r g    \<Turnstile>\<^sub>F update_raw_contract r g0 g\<close>
      and dereference_raw_spec[all_reference_specs]: \<open>\<Gamma> ; dereference_raw_fun r \<Turnstile>\<^sub>F dereference_raw_contract r sh g\<close>
      and reference_raw_spec[all_reference_specs]:   \<open>\<Gamma> ; reference_raw_fun g   \<Turnstile>\<^sub>F reference_raw_contract F \<Phi> g\<close>

      \<comment>\<open>A full reference known to occur in the live-reference list
      may be absorbed into the stack.  The conclusion exposes the list
      decomposition rather than requiring the caller to know it in advance.\<close>
      and reference_stack_pop_general[all_reference_specs]:
        \<open>\<And>F \<Phi> r g. r \<in> set \<Phi> \<Longrightarrow>
          (r \<mapsto>\<langle>\<top>\<rangle> g \<star> reference_stack F \<Phi>) \<star> \<langle>F g\<rangle>
          \<longlongrightarrow>
          (\<Squnion>\<Phi>\<^sub>1 \<Phi>\<^sub>2.
            reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<star>
            \<langle>\<Phi> = \<Phi>\<^sub>1 @ [r] @ \<Phi>\<^sub>2\<rangle>)\<close>

      \<comment>\<open>The live-reference list contains no duplicates.\<close>
      and reference_stack_distinct[all_reference_specs]:
        \<open>\<And>F \<Phi>. reference_stack F \<Phi>
          \<longlongrightarrow> \<langle>distinct \<Phi>\<rangle> \<star> reference_stack F \<Phi>\<close>

      \<comment>\<open>Share combination returns value agreement as a precise-pure factor, preserving all
      resource ownership.\<close>
      and points_to_raw_combine[all_reference_specs]:
         \<open>\<And>r sh1 sh2 v1 v2. r \<mapsto>\<langle>sh1\<rangle> v1 \<star> r \<mapsto>\<langle>sh2\<rangle> v2
            \<longlongrightarrow> r \<mapsto>\<langle>sh1+sh2\<rangle> v1 \<star> \<langle>v1 = v2\<rangle>\<close>
      and points_to_raw_split[all_reference_specs]: 
         \<open>\<And>sh shA shB r v. sh = shA+shB \<Longrightarrow> shA \<sharp> shB \<Longrightarrow> 0 < shA \<Longrightarrow> 0 < shB \<Longrightarrow> 
            r \<mapsto>\<langle>sh\<rangle> v \<longlongrightarrow> r \<mapsto>\<langle>shA\<rangle> v \<star> r \<mapsto>\<langle>shB\<rangle> v\<close>
begin

lemma remove1_distinct_split:
  assumes \<open>distinct xs\<close>
      and \<open>xs = ys @ [x] @ zs\<close>
    shows \<open>remove1 x xs = ys @ zs\<close>
proof -
  have \<open>x \<notin> set ys\<close> and \<open>x \<notin> set zs\<close>
    using assms by auto
  then show ?thesis
    using assms by (simp add: remove1_append)
qed

lemma reference_stack_pop_split:
  assumes split0: \<open>\<Lambda> = \<Phi> @ [r] @ \<Psi>\<close>
  shows \<open>(reference_stack F \<Lambda> \<star>
      r \<mapsto>\<langle>\<top>\<rangle> g) \<star> \<langle>F g\<rangle>
    \<longlongrightarrow> reference_stack F (\<Phi> @ \<Psi>)\<close>
proof (rule aentailsI)
  fix s
  assume sat:
    \<open>s \<Turnstile> (reference_stack F \<Lambda> \<star>
      r \<mapsto>\<langle>\<top>\<rangle> g) \<star> \<langle>F g\<rangle>\<close>
  have distinct: \<open>distinct \<Lambda>\<close>
  proof -
    from sat obtain stack cell where
        stack_sat: \<open>stack \<Turnstile> reference_stack F \<Lambda>\<close>
      by (auto simp add: asat_apure_precise_distrib2 elim!: asepconjE)
    have \<open>stack \<Turnstile>
        \<langle>distinct \<Lambda>\<rangle> \<star> reference_stack F \<Lambda>\<close>
      using reference_stack_distinct[
        where F=F and \<Phi>=\<Lambda>] stack_sat
      by (auto simp add: aentails_def asat_def)
    then show ?thesis
      by (simp add: asat_apure_precise_distrib)
  qed
  have member: \<open>r \<in> set \<Lambda>\<close>
    using split0 by simp
  have located:
    \<open>s \<Turnstile> (\<Squnion>\<Phi>\<^sub>1 \<Phi>\<^sub>2.
      reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<star>
      \<langle>\<Lambda> = \<Phi>\<^sub>1 @ [r] @ \<Phi>\<^sub>2\<rangle>)\<close>
    using reference_stack_pop_general[
      where F=F and \<Phi>=\<Lambda> and r=r and g=g, OF member] sat
    by (auto simp add: aentails_def asat_def asepconj_comm)
  from located obtain \<Phi>\<^sub>1 \<Phi>\<^sub>2 where
      popped: \<open>s \<Turnstile> reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2)\<close>
    and split1: \<open>\<Lambda> = \<Phi>\<^sub>1 @ [r] @ \<Phi>\<^sub>2\<close>
    by (auto simp add: asat_apure_precise_distrib2)
  have expected: \<open>remove1 r \<Lambda> = \<Phi> @ \<Psi>\<close>
    using remove1_distinct_split[OF distinct split0] .
  have actual: \<open>remove1 r \<Lambda> = \<Phi>\<^sub>1 @ \<Phi>\<^sub>2\<close>
    using remove1_distinct_split[OF distinct split1] .
  have \<open>\<Phi>\<^sub>1 @ \<Phi>\<^sub>2 = \<Phi> @ \<Psi>\<close>
    using expected actual
    by simp
  with popped show \<open>s \<Turnstile> reference_stack F (\<Phi> @ \<Psi>)\<close>
    by simp
qed

lemma reference_stack_pop[all_reference_specs]:
  \<open>(reference_stack F (\<Phi> @ [r]) \<star>
      r \<mapsto>\<langle>\<top>\<rangle> g) \<star> \<langle>F g\<rangle>
    \<longlongrightarrow> reference_stack F \<Phi>\<close>
  using reference_stack_pop_split[
    where \<Lambda>=\<open>\<Phi> @ [r]\<close> and \<Phi>=\<Phi> and \<Psi>=\<open>[]\<close>
      and F=F and r=r and g=g]
  by simp

lemma reference_stack_pop_at:
  \<open>(reference_stack F (\<Phi> @ r # \<Psi>) \<star>
      r \<mapsto>\<langle>\<top>\<rangle> g) \<star> \<langle>F g\<rangle>
    \<longlongrightarrow> reference_stack F (\<Phi> @ \<Psi>)\<close>
  using reference_stack_pop_split[
    where \<Lambda>=\<open>\<Phi> @ r # \<Psi>\<close> and \<Phi>=\<Phi> and \<Psi>=\<Psi>
      and F=F and r=r and g=g]
  by simp

lemma points_to_raw_aentails[intro]:
  assumes \<open>g0 = g1\<close>  
    shows \<open>r \<mapsto>\<langle>sh\<rangle> g0 \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> g1\<close>
using assms by (auto intro!: aentails_refl)

lemma points_to_aentails[intro]: 
  assumes \<open>g0 = g1\<close>  
      and \<open>v0 = v1\<close>
    shows \<open>r \<mapsto>\<langle>sh\<rangle> g0\<down>v0 \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> g1\<down>v1\<close>
using assms by (auto intro!: aentails_refl)

lemma aentails_split_single_points_to_assm:
  assumes \<open>points_to_localizes r g v \<Longrightarrow> \<flat> r \<mapsto>\<langle>sh\<rangle> g \<longlongrightarrow> \<phi>\<close>
  shows \<open>r\<mapsto>\<langle>sh\<rangle> g\<down>v \<longlongrightarrow> \<phi>\<close> 
  by (metis apure_precise_entailsL asepconj_comm assms reference_defs.points_to_def)

lemma aentails_split_top_points_to_assm:
  assumes \<open>points_to_localizes r g v \<Longrightarrow> \<flat> r \<mapsto>\<langle>sh\<rangle> g \<star> \<psi> \<longlongrightarrow> \<phi>\<close>
    shows \<open>r\<mapsto>\<langle>sh\<rangle> g\<down>v \<star> \<psi> \<longlongrightarrow> \<phi>\<close> 
by (metis aentails_split_single_points_to_assm assms awand_adjoint)

lemma aentails_cancel_points_to_raw_with_typed:
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>\<psi> \<longlongrightarrow> \<langle>points_to_localizes r g v\<rangle> \<star> \<phi>\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<star> \<psi> \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v \<star> \<phi>\<close> 
using assms points_to_def by (metis (no_types, lifting) asepconj_assoc asepconj_mono)

lemma aentails_cancel_points_to_raw_with_typed_0LR:
    notes asat_simp [simp]
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>points_to_localizes r g v\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v\<close>   
using assms by (simp add: aentails_def points_to_def asepconj_simp)

lemma aentails_cancel_points_to_raw_with_typed_0L:
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>\<phi> \<longlongrightarrow> \<langle>points_to_localizes r g v\<rangle>\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<star> \<phi> \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v\<close>   
using assms by (simp add: asepconj_mono points_to_def)

lemma aentails_cancel_points_to_raw_with_typed_0R:
  assumes \<open>rr' = \<flat> r\<close>
      and \<open>g' = g\<close>
      and \<open>emp \<longlongrightarrow> \<langle>points_to_localizes r g v\<rangle> \<star> \<psi>\<close>
    shows \<open>rr'\<mapsto>\<langle>sh\<rangle> g' \<longlongrightarrow> r\<mapsto>\<langle>sh\<rangle> g\<down>v \<star> \<psi>\<close>
  using aentails_cancel_points_to_raw_with_typed
  by (simp add: asepconj_assoc asepconj_mono5 assms(1,2,3) points_to_def)

declare reference_axioms [reference_axioms]
(*<*)
end

end
(*>*)
