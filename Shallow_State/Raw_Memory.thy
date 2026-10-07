(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Raw_Memory
  imports
    Byte_Trie
    Global_Store
begin

section\<open>Raw partial memories\<close>

type_synonym ('address, 'cell) raw_memory =
  \<open>'address \<Rightarrow> 'cell option\<close>

definition empty_raw_memory :: \<open>('address, 'cell) raw_memory\<close>
  where \<open>empty_raw_memory \<equiv> \<lambda>_. None\<close>

definition raw_memory_read ::
    \<open>('address, 'cell) raw_memory \<Rightarrow> 'address \<Rightarrow> 'cell option\<close>
  where \<open>raw_memory_read memory addr \<equiv> memory addr\<close>

definition raw_memory_write ::
    \<open>('address, 'cell) raw_memory \<Rightarrow>
      'address \<Rightarrow> 'cell \<Rightarrow>
      ('address, 'cell) raw_memory option\<close>
  where
    \<open>raw_memory_write memory addr value \<equiv>
       if memory addr = None
       then None
       else Some (memory(addr := Some value))\<close>

definition raw_memory_map ::
    \<open>('address, 'cell) raw_memory \<Rightarrow>
      'address \<Rightarrow> 'cell \<Rightarrow>
      ('address, 'cell) raw_memory option\<close>
  where
    \<open>raw_memory_map memory addr value \<equiv>
       if memory addr = None
       then Some (memory(addr := Some value))
       else None\<close>

definition raw_memory_unmap ::
    \<open>('address, 'cell) raw_memory \<Rightarrow>
      'address \<Rightarrow>
      ('address, 'cell) raw_memory\<close>
  where \<open>raw_memory_unmap memory addr \<equiv> memory(addr := None)\<close>

definition raw_memory_domain ::
    \<open>('address, 'cell) raw_memory \<Rightarrow> 'address set\<close>
  where \<open>raw_memory_domain memory \<equiv> {addr. memory addr \<noteq> None}\<close>

lemma raw_memory_read_empty [simp]:
  \<open>raw_memory_read empty_raw_memory addr = None\<close>
  by (simp add: raw_memory_read_def empty_raw_memory_def)

lemma raw_memory_write_read [simp]:
  assumes
    \<open>raw_memory_write memory addr value = Some memory'\<close>
  shows \<open>raw_memory_read memory' addr = Some value\<close>
  using assms
  by (auto simp add: raw_memory_write_def raw_memory_read_def
      split: if_splits)

lemma raw_memory_write_other:
  assumes
    \<open>raw_memory_write memory addr value = Some memory'\<close>
    \<open>other \<noteq> addr\<close>
  shows
    \<open>raw_memory_read memory' other = raw_memory_read memory other\<close>
  using assms
  by (auto simp add: raw_memory_write_def raw_memory_read_def
      split: if_splits)

lemma raw_memory_map_read [simp]:
  assumes
    \<open>raw_memory_map memory addr value = Some memory'\<close>
  shows
    \<open>raw_memory_read memory' addr = Some value\<close>
    \<open>raw_memory_read memory addr = None\<close>
  using assms
  by (auto simp add: raw_memory_map_def raw_memory_read_def
      split: if_splits)

lemma raw_memory_unmap_read [simp]:
  \<open>raw_memory_read (raw_memory_unmap memory addr) addr = None\<close>
  by (simp add: raw_memory_unmap_def raw_memory_read_def)

lemma raw_memory_domain_empty [simp]:
  \<open>raw_memory_domain empty_raw_memory = {}\<close>
  by (auto simp add: raw_memory_domain_def empty_raw_memory_def)

subsection\<open>Allocation policies\<close>

text\<open>Allocation is kept separate from the raw-memory representation. This
locale turns any deterministic fresh-address policy into the allocation
operation expected by an abstract global store.\<close>

locale raw_memory_allocator =
  fixes fresh_address ::
    \<open>('address, 'cell) raw_memory \<Rightarrow> 'address option\<close>
  assumes fresh_address_is_unmapped:
    \<open>fresh_address memory = Some addr \<Longrightarrow> memory addr = None\<close>
begin

definition allocate_raw_memory ::
    \<open>'cell \<Rightarrow>
      ('address, 'cell) raw_memory \<Rightarrow>
      ('address \<times> ('address, 'cell) raw_memory) option\<close>
  where
    \<open>allocate_raw_memory initial memory \<equiv>
       case fresh_address memory of
         None \<Rightarrow> None
       | Some addr \<Rightarrow>
           Some (addr, memory(addr := Some initial))\<close>

lemma allocate_raw_memory_read:
  assumes
    \<open>allocate_raw_memory initial memory = Some (addr, memory')\<close>
  shows
    \<open>raw_memory_read memory' addr = Some initial\<close>
    \<open>raw_memory_read memory addr = None\<close>
  using assms fresh_address_is_unmapped
  by (auto simp add: allocate_raw_memory_def raw_memory_read_def
      split: option.splits)

end

end
