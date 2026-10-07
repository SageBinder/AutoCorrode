(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Iterators
  imports Crush.Crush StdLib_References
begin
(*>*)

\<comment>\<open>Force one-by-one unrolling of loops\<close>
declare raw_for_loop_unroll_once_cong[crush_cong]

urust_fn [register_notation = false] find
  \<open>
  fn find(self_value: \<tau>\<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator\<close>, predicate: \<tau>\<open>('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body)\<close>) -> \<tau>\<open>'v option\<close> {
    for x in self_value {
      if predicate(x) { return Some(x); }
    };
    None
  }
  \<close>

urust_fn [abbrev, register_notation = false] enumerate_fn1
  \<open>
  fn enumerate_fn1(i: \<tau>\<open>nat\<close>, f: \<tau>\<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) function_body\<close>) -> \<tau>\<open>64 word \<times> 'v \<times> tnil\<close> {
    let feval = f();
    (\<llangle>word_of_nat i\<rrangle>, feval)
  }
  \<close>

definition enumerate :: \<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator \<Rightarrow>
      ('s, ('s, 64 word \<times> 'v \<times> tnil, 'abort, 'i prompt, 'o prompt_output) iterator, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>enumerate self \<equiv> FunctionBody (literal (make_iterator
    (mapi enumerate_fn1 (iterator_thunks self))))\<close>

urust_fn [register_notation = false] any
  \<open>
  fn any(self_value: \<tau>\<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator\<close>, predicate: \<tau>\<open>('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body)\<close>) -> bool {
     match self_value.find(predicate) {
       Some(_) \<Rightarrow> True,
       None    \<Rightarrow> False
     }
  }
  \<close>

urust_fn [register_notation = false] count
  \<open>
  fn count(self_value: \<tau>\<open>('s, 'v, 'abort, 'i prompt, 'o prompt_output) iterator\<close>) -> u64 {
    \<llangle>of_nat \<circ> length \<circ> iterator_thunks\<rrangle>\<^sub>1(self_value)
  }
  \<close>

context reference
begin

urust_fn [register_notation = false] iter_mut
  \<open>
  fn iter_mut(ref_value: \<tau>\<open>('a, 'b, 'v list) Global_Store.ref\<close>) -> \<tau>\<open>('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) iterator\<close> {
    let xs = *ref_value;
    \<llangle>make_iterator_from_list (List.map (\<lambda>i. (focus_nth i ref_value)) [0 ..< length xs])\<rrangle>
  }
  \<close>

(*<*)
end
(*>*)

subsection\<open>Debug printing\<close>

instantiation iterator :: (type, type, type, type, type)generate_debug
begin

definition generate_debug_iterator :: \<open>('a, 'b, 'c, 'd, 'e) iterator \<Rightarrow> log_data\<close> where
  \<open>generate_debug_iterator i \<equiv> [str ''<Iterator (length ='', LogNat (iterator_len i), str ''>'']\<close>

instance ..

end


definition iterator_find_contract :: \<open>'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>
  ('machine::sepalg, 'abort, 'i, 'o) striple_context \<Rightarrow>
  ('a \<Rightarrow> ('machine, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
  ('machine, 'a option, 'abort) function_contract\<close> where
  \<open>iterator_find_contract vs pred_pure \<Gamma> pred_rust \<equiv>
    let pre = \<langle>\<forall> i. \<Gamma>; pred_rust i \<Turnstile>\<^sub>F lift_pure_to_contract (pred_pure i)\<rangle> in
    let post = \<lambda> ret. \<langle>ret = List.find pred_pure vs\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto iterator_find_contract

declare lift_pure_to_contract_def [crush_contracts]
ucincl_auto lift_pure_to_contract

lemma iterator_find_spec:
  shows \<open>\<Gamma> ; StdLib_Iterators.find (make_iterator_from_list vs) pred_rust \<Turnstile>\<^sub>F iterator_find_contract vs pred_pure \<Gamma> pred_rust\<close>
proof (crush_boot f: StdLib_Iterators.find_def contract: iterator_find_contract_def, goal_cases)
  case 1
  note pred_spec = this[THEN spec]
  show ?case proof (crush_base inline: iterator_into_iter_def, induction vs)
    case Nil
    then show ?case
      by (crush_base simp add: raw_for_loop_def)
  next
    case (Cons a vs)
    note IH = this
    show ?case
      apply (crush_base specs add: pred_spec)
      apply (cases \<open>pred_pure a\<close>)
       apply crush_base
      apply (subst List.find.simps(2), simp)
      by (rule IH)
  qed
qed

(*<*)
end
(*>*)
