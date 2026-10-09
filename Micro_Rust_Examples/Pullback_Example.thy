(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Pullback_Example
  imports
    Separation_Lenses.SLens_Pullback
    Separation_Lenses.SLens_Examples
    Micro_Rust_Runtime.Runtime_Heap
    Micro_Rust_Std_Lib.StdLib_All
begin

text\<open>In this theory, we demonstrate how to 'pull back' the standard library's uRust heap
implementation to a larger separation algebra.

For simplicity, we use the product separation algebra of the uRust heap and some optional value
(which is of no further relevance).\<close>

text\<open>Our test separation algebra. It inherits a separation algebra structure by virtue of
\<^verbatim>\<open>prod\<close> and \<^verbatim>\<open>option\<close> being marked as \<^verbatim>\<open>(sepalg, sepalg) sepalg\<close> and \<^verbatim>\<open>(type) sepalg\<close>,
respectively.\<close>
type_synonym test_algebra = \<open>nat Permissioned_Heap.mem \<times> nat option\<close>

instantiation nat :: default
begin
definition \<open>default_nat \<equiv> 0::nat\<close>
instance ..
end

text\<open>The lens projecting to the standard uRust heap implementation:\<close>
abbreviation test_lens :: \<open>(test_algebra, nat Permissioned_Heap.mem) lens\<close> where \<open>test_lens \<equiv> prod_lens_fst\<close>
print_locale reference_transfer
text\<open>First, we transfer the parameters of the reference locale along the separation lens:\<close>
global_interpretation Heap_Example_Transfer: reference_transfer test_lens
  \<open>\<lambda>_ _ _ _ _ _. ()\<close>
  urust_heap_update_raw_fun
  urust_heap_dereference_raw_fun
  urust_heap_reference_raw_fun
  urust_heap_points_to_raw'
  \<open>\<lambda>_. UNIV\<close> UNIV
  urust_heap_can_alloc_reference
   defines update_raw_fun = \<open>Heap_Example_Transfer.update_raw_fun\<close>
       and dereference_raw_fun = \<open>Heap_Example_Transfer.dereference_raw_fun\<close>
       and reference_raw_fun = \<open>Heap_Example_Transfer.reference_raw_fun\<close>
  by (standard, simp add: prod_slens_fst_valid)

text\<open>Next, we instantiate the reference locale with the transferred parameters.

The real work has been done in \<^verbatim>\<open>reference_transfer\<close>, which proves the reference axioms for the
transferred parameters already. However, because of an issue with code generation and sublocales,
we do not register \<^verbatim>\<open>reference\<close> as a sublocale of \<^verbatim>\<open>reference_transfer\<close>, but globally interpret
here explicitly:\<close>
global_interpretation Heap_Example: rust_reference \<open>\<lambda> _ _ _ _ _ _. ()\<close>
  update_raw_fun
  dereference_raw_fun
  reference_raw_fun
  Heap_Example_Transfer.points_to_raw'
  \<open>\<lambda>_. UNIV\<close> UNIV
  Heap_Example_Transfer.can_alloc_reference
  defines
           reference_fun = \<open>Heap_Example.reference_fun\<close>
       and dereference_fun = \<open>Heap_Example.dereference_fun\<close>
       and ro_dereference_fun = \<open>Heap_Example.ro_dereference_fun\<close>
       and modify_raw_fun = \<open>Heap_Example.modify_raw_fun\<close>
       and modify_fun = \<open>Heap_Example.modify_fun\<close>
       and update_fun = \<open>Heap_Example.update_fun\<close>

       and slice_index = \<open>Heap_Example.slice_index\<close>
       and slice_index_array = \<open>Heap_Example.slice_index_array\<close>
       and take_mut_ref_option = \<open>Heap_Example.take_mut_ref_option\<close>
       and option_as_mut = \<open>Heap_Example.option_as_mut\<close>
       and iter_mut = \<open>Heap_Example.iter_mut\<close>
  using Heap_Example_Transfer.reference_lifted by simp

text\<open>Checking that code generation does indeed work...\<close>

declare function_pull_back_def[code_unfold]

export_code (* Transferred core reference data *)
            update_raw_fun dereference_raw_fun reference_raw_fun
            (* Derived definitions *)
            \<comment>\<open>\<^verbatim>\<open>reference_fun\<close> cannot be extracted because \<^verbatim>\<open>prism_to_focus\<close> has no unconditional
               code equations. Only specific instances can be extracted.\<close>
            \<comment>\<open>\<^verbatim>\<open>reference_fun\<close>\<close>
            dereference_fun
            ro_dereference_fun
            modify_raw_fun
            modify_fun
            update_fun

            slice_index
            slice_index_array
            take_mut_ref_option
            option_as_mut
            iter_mut
  in OCaml

adhoc_overloading store_update_const \<rightleftharpoons> update_fun
adhoc_overloading store_dereference_const \<rightleftharpoons> dereference_fun ro_dereference_fun

end
