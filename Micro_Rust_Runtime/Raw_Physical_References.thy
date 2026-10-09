(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Raw_Physical_References
  imports
    Separation_Lenses.SLens
    Byte_Level_Encoding.Niche_Encoding_Option_NonNull
    Micro_Rust_Std_Lib.StdLib_All
    Micro_Rust_Interfaces.Raw_Physical_Memory_References
    Raw_Physical_Memory_Trie
begin

context rust_reference
begin
no_adhoc_overloading index_const \<rightleftharpoons>
  slice_index
  slice_index_array
end

global_interpretation raw_pmem_trie_memrefs: raw_tagged_physical_memory_references
  memset_tagged_phys
  memset_tagged_phys_block
  points_to_tagged_phys_byte
  store_tagged_physical_address
  load_tagged_physical_address
  tag_physical_page
  defines
        raw_pmem_trie_update_raw_fun = \<open>raw_pmem_trie_memrefs.update_raw_fun\<close>
    and raw_pmem_trie_reference_raw_fun = \<open>raw_pmem_trie_memrefs.reference_raw_fun\<close>
    and raw_pmem_trie_dereference_raw_fun = \<open>raw_pmem_trie_memrefs.dereference_raw_fun\<close>
  by (simp add: raw_tagged_physical_memory_references_def
    Raw_Tagged_Physical_Memory_Trie.raw_tagged_physical_memory_axioms)

export_code
  raw_pmem_trie_update_raw_fun
  raw_pmem_trie_reference_raw_fun
  raw_pmem_trie_dereference_raw_fun
  in OCaml

global_interpretation raw_pmem_trie_refs: rust_reference \<open>\<lambda>_ _ _ _ _ _. ()\<close>
  raw_pmem_trie_update_raw_fun
  raw_pmem_trie_dereference_raw_fun
  raw_pmem_trie_reference_raw_fun
  raw_pmem_trie_memrefs.points_to_raw'
  raw_pmem_trie_memrefs.gref_can_store
  raw_pmem_trie_memrefs.new_gref_can_store
  raw_pmem_trie_memrefs.can_alloc_reference
   defines raw_pmem_trie_reference_fun = \<open>raw_pmem_trie_refs.reference_fun\<close>
       and raw_pmem_trie_dereference_fun = \<open>raw_pmem_trie_refs.dereference_fun\<close>
       and raw_pmem_trie_ro_dereference_fun = \<open>raw_pmem_trie_refs.ro_dereference_fun\<close>
       and raw_pmem_trie_modify_raw_fun = \<open>raw_pmem_trie_refs.modify_raw_fun\<close>
       and raw_pmem_trie_modify_fun = \<open>raw_pmem_trie_refs.modify_fun\<close>
       and raw_pmem_trie_update_fun = \<open>raw_pmem_trie_refs.update_fun\<close>
       and raw_pmem_trie_slice_index = \<open>raw_pmem_trie_refs.slice_index\<close>
       and raw_pmem_trie_slice_index_array = \<open>raw_pmem_trie_refs.slice_index_array\<close>
       and raw_pmem_trie_take_mut_ref_option = \<open>raw_pmem_trie_refs.take_mut_ref_option\<close>
       and raw_pmem_trie_option_as_mut = \<open>raw_pmem_trie_refs.option_as_mut\<close>
       and raw_pmem_trie_iter_mut = \<open>raw_pmem_trie_refs.iter_mut\<close>
  by (simp add: raw_pmem_trie_memrefs.reference_sublocale)

export_code
  \<comment>\<open>\<^verbatim>\<open>raw_pmem_trie_reference_fun\<close> cannot be extracted because \<^verbatim>\<open>prism_to_focus\<close> has no unconditional
               code equations. Only specific instances can be extracted.\<close>
  (* raw_pmem_trie_reference_fun *)
  raw_pmem_trie_dereference_fun
  raw_pmem_trie_ro_dereference_fun
  raw_pmem_trie_modify_raw_fun
  raw_pmem_trie_modify_fun
  raw_pmem_trie_update_fun
  raw_pmem_trie_slice_index
  raw_pmem_trie_slice_index_array
  raw_pmem_trie_take_mut_ref_option
  raw_pmem_trie_option_as_mut
  raw_pmem_trie_iter_mut
  in OCaml

end
