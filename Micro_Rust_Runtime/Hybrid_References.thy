(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Hybrid_References
  imports 
    Runtime_Heap
    Raw_Physical_References
    Micro_Rust_Interfaces.Pair_References
    Separation_Lenses.SLens_Examples
begin

section\<open>Hybrid heap+memory-based reference implementation\<close>

text\<open>This theory illustrates how to use the pullback and disjoint union operations
on \<^locale>\<open>reference\<close> interpretations to build an interpretation supporting both
heap-backed and memory-backed references.\<close>

subsection\<open>Base separation algebra\<close>

type_synonym phys = \<open>unit tagged_physical_memory\<close>

text\<open>The separation algebra hosting desired interpretation is the product of the
uRust runtime heap and the physical memory trie implementation:\<close>
type_synonym 'a hybrid_ref_sa = \<open>'a Permissioned_Heap.mem \<times> phys\<close>

text\<open>Note that \<^verbatim>\<open>'a hybrid_ref_sa\<close> automatically inherits a separation algebra structure
from \<^verbatim>\<open>'a heap_gv Share_Map.mem\<close> and \<^verbatim>\<open>physical_memory\<close>.

We also note that the projections onto the components of \<^verbatim>\<open>hybrid_ref_sa\<close> are
separation lenses:\<close>

abbreviation SL_Heap :: \<open>('a hybrid_ref_sa, 'a Permissioned_Heap.mem) lens\<close> where
  \<open>SL_Heap \<equiv> prod_lens_fst\<close>

abbreviation SL_PMem :: \<open>('a hybrid_ref_sa, phys) lens\<close> where
  \<open>SL_PMem \<equiv> prod_lens_snd\<close>

subsection\<open>Pulling back the heap implementation\<close>

text\<open>First, we pull back the heap-based reference implementation. This follows
\<^verbatim>\<open>Pullback_Example.thy\<close>.\<close>

global_interpretation Heap_Transfer: reference_transfer SL_Heap \<open>\<lambda>_ _ _ _ _ _. ()\<close>
  urust_heap_update_raw_fun
  urust_heap_dereference_raw_fun
  urust_heap_reference_raw_fun
  urust_heap_points_to_raw'
  \<open>\<lambda>_. UNIV\<close> UNIV
  urust_heap_can_alloc_reference
   defines pb_urust_heap_update_raw_fun = \<open>Heap_Transfer.update_raw_fun\<close>
       and pb_urust_heap_dereference_raw_fun = \<open>Heap_Transfer.dereference_raw_fun\<close>
       and pb_urust_heap_reference_raw_fun = \<open>Heap_Transfer.reference_raw_fun\<close>  
  by (standard, simp add: prod_slens_fst_valid)

export_code
  pb_urust_heap_update_raw_fun
  pb_urust_heap_dereference_raw_fun
  pb_urust_heap_reference_raw_fun
  in OCaml

global_interpretation PB_Heap: rust_reference \<open>\<lambda> _ _ _ _ _ _. ()\<close>
  pb_urust_heap_update_raw_fun
  pb_urust_heap_dereference_raw_fun
  pb_urust_heap_reference_raw_fun
  Heap_Transfer.points_to_raw'
  \<open>\<lambda>_. UNIV\<close> UNIV
  Heap_Transfer.can_alloc_reference 
  defines 
           pb_urust_heap_reference_fun = \<open>PB_Heap.reference_fun\<close>
       and pb_urust_heap_dereference_fun = \<open>PB_Heap.dereference_fun\<close>
       and pb_urust_heap_ro_dereference_fun = \<open>PB_Heap.ro_dereference_fun\<close>
       and pb_urust_heap_modify_raw_fun = \<open>PB_Heap.modify_raw_fun\<close>
       and pb_urust_heap_modify_fun = \<open>PB_Heap.modify_fun\<close>
       and pb_urust_heap_update_fun = \<open>PB_Heap.update_fun\<close>

       and pb_urust_heap_slice_index = \<open>PB_Heap.slice_index\<close>
       and pb_urust_heap_slice_index_array = \<open>PB_Heap.slice_index_array\<close>
       and pb_urust_heap_take_mut_ref_option = \<open>PB_Heap.take_mut_ref_option\<close>
       and pb_urust_heap_option_as_mut = \<open>PB_Heap.option_as_mut\<close>
       and pb_urust_heap_iter_mut = \<open>PB_Heap.iter_mut\<close>
  using Heap_Transfer.reference_lifted by simp

export_code 
\<comment>\<open>\<^verbatim>\<open>pb_urust_heap_reference_fun\<close> cannot be extracted because \<^verbatim>\<open>prism_to_focus\<close> has no unconditional
               code equations. Only specific instances can be extracted.\<close>
  \<comment>\<open>\<^verbatim>\<open>pb_urust_heap_reference_fun\<close>\<close>
  pb_urust_heap_dereference_fun 
  pb_urust_heap_ro_dereference_fun
  pb_urust_heap_modify_raw_fun
  pb_urust_heap_modify_fun 
  pb_urust_heap_update_fun
  pb_urust_heap_slice_index
  pb_urust_heap_slice_index_array
  pb_urust_heap_take_mut_ref_option
  pb_urust_heap_option_as_mut 
  pb_urust_heap_iter_mut
  in OCaml

subsection\<open>Pulling back the physical memory implementation\<close>

text\<open>Analogously, we extend the physical memory based references to our
product separation algebra through pull back:\<close>

global_interpretation PMemRefs_Transfer: reference_transfer SL_PMem \<open>\<lambda>_ _ _ _ _ _. ()\<close>
  raw_pmem_trie_update_raw_fun 
  raw_pmem_trie_dereference_raw_fun 
  raw_pmem_trie_reference_raw_fun 
  raw_pmem_trie_memrefs.points_to_raw'
  raw_pmem_trie_memrefs.gref_can_store
  raw_pmem_trie_memrefs.new_gref_can_store
  raw_pmem_trie_memrefs.can_alloc_reference
   defines raw_pmem_trie_update_raw_fun = \<open>PMemRefs_Transfer.update_raw_fun\<close>
       and raw_pmem_trie_dereference_raw_fun = \<open>PMemRefs_Transfer.dereference_raw_fun\<close>
       and raw_pmem_trie_reference_raw_fun = \<open>PMemRefs_Transfer.reference_raw_fun\<close>  
  by (standard, simp add: prod_slens_snd_valid)

export_code
  raw_pmem_trie_update_raw_fun
  raw_pmem_trie_dereference_raw_fun
  raw_pmem_trie_reference_raw_fun
  in OCaml

global_interpretation PB_PMemRefs: rust_reference \<open>\<lambda> _ _ _ _ _ _. ()\<close>
  raw_pmem_trie_update_raw_fun
  raw_pmem_trie_dereference_raw_fun
  raw_pmem_trie_reference_raw_fun
  PMemRefs_Transfer.points_to_raw'
  raw_pmem_trie_memrefs.gref_can_store
  raw_pmem_trie_memrefs.new_gref_can_store
  PMemRefs_Transfer.can_alloc_reference
  defines 
           pb_raw_pmem_trie_reference_fun = \<open>PB_PMemRefs.reference_fun\<close>
       and pb_raw_pmem_trie_dereference_fun = \<open>PB_PMemRefs.dereference_fun\<close>
       and pb_raw_pmem_trie_ro_dereference_fun = \<open>PB_PMemRefs.ro_dereference_fun\<close>
       and pb_raw_pmem_trie_modify_raw_fun = \<open>PB_PMemRefs.modify_raw_fun\<close>
       and pb_raw_pmem_trie_modify_fun = \<open>PB_PMemRefs.modify_fun\<close>
       and pb_raw_pmem_trie_update_fun = \<open>PB_PMemRefs.update_fun\<close>

       and pb_raw_pmem_trie_slice_index = \<open>PB_PMemRefs.slice_index\<close>
       and pb_raw_pmem_trie_slice_index_array = \<open>PB_PMemRefs.slice_index_array\<close>
       and pb_raw_pmem_trie_take_mut_ref_option = \<open>PB_PMemRefs.take_mut_ref_option\<close>
       and pb_raw_pmem_trie_option_as_mut = \<open>PB_PMemRefs.option_as_mut\<close>
       and pb_raw_pmem_trie_iter_mut = \<open>PB_PMemRefs.iter_mut\<close>
  using PMemRefs_Transfer.reference_lifted by simp

export_code 
\<comment>\<open>\<^verbatim>\<open>pb_raw_pmem_trie_reference_fun\<close> cannot be extracted because \<^verbatim>\<open>prism_to_focus\<close> has no unconditional
               code equations. Only specific instances can be extracted.\<close>
  \<comment>\<open>\<^verbatim>\<open>pb_raw_pmem_trie_reference_fun\<close>\<close>
  pb_raw_pmem_trie_dereference_fun 
  pb_raw_pmem_trie_ro_dereference_fun
  pb_raw_pmem_trie_modify_raw_fun
  pb_raw_pmem_trie_modify_fun 
  pb_raw_pmem_trie_update_fun
  pb_raw_pmem_trie_slice_index
  pb_raw_pmem_trie_slice_index_array
  pb_raw_pmem_trie_take_mut_ref_option
  pb_raw_pmem_trie_option_as_mut 
  pb_raw_pmem_trie_iter_mut
  in OCaml

subsection\<open>Constructing the hybrid reference implementation\<close>

global_interpretation RefPair: Reference_Pair \<open>\<lambda>_ _ _ _ _ _. ()\<close> \<open>\<lambda>_ _ _ _ _ _. ()\<close>
  \<comment>\<open>Heap based implementation\<close>
  pb_urust_heap_update_raw_fun
  pb_urust_heap_dereference_raw_fun
  pb_urust_heap_reference_raw_fun
  Heap_Transfer.points_to_raw'
  \<open>\<lambda>_. UNIV\<close> UNIV
  Heap_Transfer.can_alloc_reference 
  \<comment>\<open>Physical memory based implementation\<close>
  raw_pmem_trie_update_raw_fun
  raw_pmem_trie_dereference_raw_fun
  raw_pmem_trie_reference_raw_fun
  PMemRefs_Transfer.points_to_raw'
  raw_pmem_trie_memrefs.gref_can_store
  raw_pmem_trie_memrefs.new_gref_can_store
  PMemRefs_Transfer.can_alloc_reference
   defines hybrid_update_raw_fun = \<open>RefPair.update_raw_fun\<close>
       and hybrid_dereference_raw_fun = \<open>RefPair.dereference_raw_fun\<close>
       and hybrid_reference_raw_fun = \<open>RefPair.reference_raw_fun\<close>  ..

export_code 
  hybrid_update_raw_fun
  hybrid_dereference_raw_fun
  hybrid_reference_raw_fun
  in OCaml

global_interpretation Hybrid_Refs: rust_reference \<open>\<lambda>_ _ _ _ _ _. ()\<close>
   hybrid_update_raw_fun
   hybrid_dereference_raw_fun
   hybrid_reference_raw_fun
   RefPair.points_to_raw'
   RefPair.gref_can_store
   RefPair.new_gref_can_store
   RefPair.can_alloc_reference
   defines 
           hybrid_reference_fun = \<open>Hybrid_Refs.reference_fun\<close>
       and hybrid_dereference_fun = \<open>Hybrid_Refs.dereference_fun\<close>
       and hybrid_ro_dereference_fun = \<open>Hybrid_Refs.ro_dereference_fun\<close>
       and hybrid_modify_raw_fun = \<open>Hybrid_Refs.modify_raw_fun\<close>
       and hybrid_modify_fun = \<open>Hybrid_Refs.modify_fun\<close>
       and hybrid_update_fun = \<open>Hybrid_Refs.update_fun\<close>

       and hybrid_slice_index = \<open>Hybrid_Refs.slice_index\<close>
       and hybrid_slice_index_array = \<open>Hybrid_Refs.slice_index_array\<close>
       and hybrid_take_mut_ref_option = \<open>Hybrid_Refs.take_mut_ref_option\<close>
       and hybrid_option_as_mut = \<open>Hybrid_Refs.option_as_mut\<close>
       and hybrid_iter_mut = \<open>Hybrid_Refs.iter_mut\<close>
  using RefPair.pair_reference_sublocale by force

export_code 
\<comment>\<open>\<^verbatim>\<open>hybrid_reference_fun\<close> cannot be extracted because \<^verbatim>\<open>prism_to_focus\<close> has no unconditional
               code equations. Only specific instances can be extracted.\<close>
  \<comment>\<open>\<^verbatim>\<open>hybrid_reference_fun\<close>\<close>
  hybrid_dereference_fun 
  hybrid_ro_dereference_fun
  hybrid_modify_raw_fun
  hybrid_modify_fun 
  hybrid_update_fun
  hybrid_slice_index
  hybrid_slice_index_array
  hybrid_take_mut_ref_option
  hybrid_option_as_mut 
  hybrid_iter_mut
  in OCaml

subsection\<open>Instantiations\<close>

text\<open>Finally, we check that we can instantiate the polymorphic global value type in the above
hybrid reference implementation:\<close>

experiment
begin

interpretation Hybrid_Refs: rust_reference \<open>\<lambda>_ _ (_ :: unit + byte list) _ _ _. ()\<close>
   hybrid_update_raw_fun
   hybrid_dereference_raw_fun
   hybrid_reference_raw_fun
   RefPair.points_to_raw'
   RefPair.gref_can_store
   RefPair.new_gref_can_store
   RefPair.can_alloc_reference ..

end

end
