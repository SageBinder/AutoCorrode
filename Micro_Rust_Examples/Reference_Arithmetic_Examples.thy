(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Reference_Arithmetic_Examples
  imports
    Micro_Rust_Runtime.Runtime_Heap
    "HOL-Library.Code_Target_Numeral" \<comment>\<open>Word bounds such as \<open>2 ^ 64\<close> need target integers, not unary \<open>nat\<close>.\<close>
begin

section\<open>Checked compound assignment on word references\<close>

text\<open>
The reference helper is generic in the word length. Its compound-assignment overload is declared
for these examples only and removed afterwards. They exercise both word sizes and show that
overflow panics before the update, leaving every heap cell unchanged.

The heap backend exports the helper as \<^const>\<open>urust_heap_assign_add_ref\<close>, with code equations
over its executable reference functions. The heap's global value type needs a default for
unallocated cells, so the words live in a small datatype. A prism selects each word size, and its
focus types the references. Code evaluation inspects every heap cell through
\<^const>\<open>mem_to_alist\<close>, since heaps have no executable equality.
\<close>

datatype arith_gv = Small_Word \<open>32 word\<close> | Wide_Word \<open>64 word\<close> | Unset_Word

instantiation arith_gv :: default
begin
definition \<open>default_arith_gv \<equiv> Unset_Word\<close>
instance ..
end

definition \<open>the_small_word gv \<equiv> case gv of Small_Word w \<Rightarrow> Some w | _ \<Rightarrow> None\<close>
definition \<open>the_wide_word gv \<equiv> case gv of Wide_Word w \<Rightarrow> Some w | _ \<Rightarrow> None\<close>
definition \<open>arith_gv_prism_small \<equiv> make_prism Small_Word the_small_word\<close>
definition \<open>arith_gv_prism_wide \<equiv> make_prism Wide_Word the_wide_word\<close>

lemma arith_gv_prism_small_valid: \<open>is_valid_prism arith_gv_prism_small\<close>
  by (auto simp add: is_valid_prism_def the_small_word_def arith_gv_prism_small_def
    split!: arith_gv.splits)

lemma arith_gv_prism_wide_valid: \<open>is_valid_prism arith_gv_prism_wide\<close>
  by (auto simp add: is_valid_prism_def the_wide_word_def arith_gv_prism_wide_def
    split!: arith_gv.splits)

\<comment>\<open>Named foci keep code generation away from the validity-dependent \<^verbatim>\<open>prism_to_focus\<close>.\<close>
definition \<open>arith_gv_focus_small = \<integral>\<^sub>p arith_gv_prism_small\<close>
definition \<open>arith_gv_focus_wide = \<integral>\<^sub>p arith_gv_prism_wide\<close>
declare arith_gv_focus_small_def[symmetric, code_unfold]
declare arith_gv_focus_wide_def[symmetric, code_unfold]
declare prism_to_focus.rep_eq[OF arith_gv_prism_small_valid, folded arith_gv_focus_small_def, code]
declare prism_to_focus.rep_eq[OF arith_gv_prism_wide_valid, folded arith_gv_focus_wide_def, code]

definition small_word_ref :: \<open>(nat, arith_gv, 32 word) Global_Store.ref\<close>
  where \<open>small_word_ref \<equiv> make_focused (make_gref 0) arith_gv_focus_small\<close>

definition wide_word_ref :: \<open>(nat, arith_gv, 64 word) Global_Store.ref\<close>
  where \<open>wide_word_ref \<equiv> make_focused (make_gref 1) arith_gv_focus_wide\<close>

context
begin

adhoc_overloading assign_add_const \<rightleftharpoons> urust_heap_assign_add_ref

urust_fn [register_notation = false, state = \<open>arith_gv mem\<close>, abort = \<open>unit\<close>,
    input = \<open>unit prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn add_ref32(target: \<tau>\<open>(nat, arith_gv, 32 word) Global_Store.ref\<close>, amount: u32) -> () {
    target += amount;
  }
  \<close>

urust_fn [register_notation = false, state = \<open>arith_gv mem\<close>, abort = \<open>unit\<close>,
    input = \<open>unit prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn add_ref64(target: \<tau>\<open>(nat, arith_gv, 64 word) Global_Store.ref\<close>, amount: u64) -> () {
    target += amount;
  }
  \<close>

definition arith_heap :: \<open>32 word \<Rightarrow> 64 word \<Rightarrow> arith_gv mem\<close>
  where \<open>arith_heap small wide \<equiv> mem_from_alist [(0, Small_Word small), (1, Wide_Word wide)]\<close>

lemma add_ref32_success:
  \<open>case deep_evaluate_det yield_handler_det_no_yield (call (add_ref32 small_word_ref 2))
      (arith_heap 40 7) of
     continuation.Success () \<sigma> \<Rightarrow> mem_to_alist \<sigma> = mem_to_alist (arith_heap 42 7)
   | _ \<Rightarrow> False\<close>
  by eval

lemma add_ref64_success:
  \<open>case deep_evaluate_det yield_handler_det_no_yield (call (add_ref64 wide_word_ref 2))
      (arith_heap 7 40) of
     continuation.Success () \<sigma> \<Rightarrow> mem_to_alist \<sigma> = mem_to_alist (arith_heap 7 42)
   | _ \<Rightarrow> False\<close>
  by eval

lemma add_ref32_overflow:
  \<open>case deep_evaluate_det yield_handler_det_no_yield (call (add_ref32 small_word_ref 1))
      (arith_heap (-1) 7) of
     continuation.Abort (Panic message) \<sigma> \<Rightarrow>
       message = overflow_err_msg \<and> mem_to_alist \<sigma> = mem_to_alist (arith_heap (-1) 7)
   | _ \<Rightarrow> False\<close>
  by eval

lemma add_ref64_overflow:
  \<open>case deep_evaluate_det yield_handler_det_no_yield (call (add_ref64 wide_word_ref 1))
      (arith_heap 7 (-1)) of
     continuation.Abort (Panic message) \<sigma> \<Rightarrow>
       message = overflow_err_msg \<and> mem_to_alist \<sigma> = mem_to_alist (arith_heap 7 (-1))
   | _ \<Rightarrow> False\<close>
  by eval

ML_val\<open>
  (case Term.head_of (Syntax.read_term \<^context> "assign_add_const small_word_ref (1 :: 32 word)") of
     Const (name, _) =>
       if name = \<^const_name>\<open>urust_heap_assign_add_ref\<close> then ()
       else error ("compound reference addition did not select the heap helper: " ^ name)
   | _ => error "compound reference addition did not select the heap helper")
\<close>

no_adhoc_overloading assign_add_const \<rightleftharpoons> urust_heap_assign_add_ref

end

text\<open>An unnamed context keeps the theory target, so the overload is removed explicitly.\<close>

ML_val\<open>
  (case Term.head_of (Syntax.read_term \<^context> "assign_add_const small_word_ref (1 :: 32 word)") of
     Const (name, _) =>
       if name = \<^const_name>\<open>assign_add_const\<close> then ()
       else error ("compound reference addition overload escaped its examples: " ^ name)
   | _ => error "compound reference addition overload escaped its examples")
\<close>

ML_val\<open>
  if null (Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NFunction "assign_add_ref")
  then ()
  else error "generic reference addition helper unexpectedly registered a Rust call notation"
\<close>

end
