(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Runtime_Heap
  imports
    Micro_Rust_Std_Lib.StdLib_All
    Micro_Rust_Interfaces.Transfer_References
    Micro_Rust_Interfaces.Global_Perm_Store
    Shallow_State_Logic.Apartness
    Shallow_State_Logic.Separation_Algebra
    Shallow_State_Logic.Tree_Shares
    Shallow_Micro_Rust_Logic.Rust_Weakest_Precondition
    Shallow_Separation_Logic.Share_Map
    Shallow_Separation_Logic.Permissioned_Heap
begin
(*>*)

subsection\<open>Concrete machines implement a global store\<close>

global_interpretation Global_Store: global_store read_mem write_mem alloc_mem
  defines urust_heap_update_raw_fun = \<open>Global_Store.update_raw_fun\<close>
      and urust_heap_dereference_raw_fun = \<open>Global_Store.dereference_by_value_raw_fun\<close>
      and urust_heap_reference_raw_fun = \<open>Global_Store.reference_raw_fun\<close>

      and urust_heap_update_raw' = \<open>Global_Store.update_raw\<close>
      and urust_heap_modify_raw' = \<open>Global_Store.modify_raw\<close>
      and urust_heap_dereference_raw = \<open>Global_Store.dereference_by_value_raw\<close>
      and urust_heap_reference_raw = \<open>Global_Store.reference_raw\<close>
proof
  fix \<sigma> :: \<open>'v mem\<close> and k v
  show \<open>\<And>\<sigma>'. write_mem \<sigma> k v = Some \<sigma>' \<Longrightarrow> read_mem \<sigma>' k = Some v\<close> 
    by (simp add: read_mem_write_mem_commute)
next
  fix k k' :: \<open>nat\<close> and v v' and \<sigma> :: \<open>'v mem\<close> 
  assume \<open>k \<noteq> k'\<close>
  from this show \<open>Option.bind (write_mem \<sigma> k v) (\<lambda>\<sigma>'. write_mem \<sigma>' k' v') =
                  Option.bind (write_mem \<sigma> k' v') (\<lambda>\<sigma>'. write_mem \<sigma>' k v)\<close> 
    by (simp add: write_mem_self_commute')
next
  fix \<sigma> :: \<open>'v mem\<close> and k v v'
  show \<open>\<And>\<sigma>'. write_mem \<sigma> k v = Some \<sigma>' \<Longrightarrow> write_mem \<sigma>' k v' = write_mem \<sigma> k v'\<close> 
    by (meson write_mem_collapse)
next
  fix \<sigma> :: \<open>'v::default mem\<close> and f \<sigma>' v
  assume \<open>alloc_mem \<sigma> = Some (f, \<sigma>')\<close>
  then show \<open>\<exists>\<sigma>''. write_mem \<sigma>' f v = Some \<sigma>''\<close>
    using write_mem_success[where sh=top and vold=\<open>default::'v\<close> and m=\<sigma>' and a=f]
    by (meson alloc_mem_success_reverse'(5))
qed

global_interpretation Global_Perm_Store: global_perm_store read_mem write_mem alloc_mem
  mem_perm_map mem_alloc_pool mem_can_alloc
  defines urust_heap_points_to_raw' = Global_Perm_Store.points_to_raw' 
      and urust_heap_can_alloc_reference = Global_Perm_Store.can_alloc_reference
proof 
  fix s :: \<open>'a mem\<close>
  show \<open>mem_alloc_pool s = {} \<or> infinite (mem_alloc_pool s)\<close>
    using infinite_Ici [where 'a=nat]
    by (auto simp: Permissioned_Heap.mem_alloc_pool_def atLeast_def)
next
  fix s1 s2 :: \<open>'a mem\<close>
  assume \<open>s1 \<sharp> s2\<close>
  then show \<open>mem_alloc_pool s1 = {} \<or> mem_alloc_pool s2 = {}\<close>       
    by (auto simp: Permissioned_Heap.mem_alloc_pool_def Permissioned_Heap.disjoint_mem_def 
      disjoint_option_def)
next
  fix s :: \<open>'v mem\<close> and a
  show \<open>0 < mem_perm_map s a = (\<exists>v. read_mem s a = Some v)\<close>
    using Rep_nonempty_share 
    by (auto simp: Permissioned_Heap.mem_perm_map_def 
        Permissioned_Heap.read_mem_def zero_share_def shareable_value_to_share_def
      split: shareable_value.splits)
next
  fix s :: \<open>'b mem\<close> and a :: nat and v :: \<open>'b\<close>
  show \<open>(mem_perm_map s a = \<top>) = (\<exists>s'. write_mem s a v = Some s')\<close>
    using write_mem_success_perm_map by fastforce
next
  fix s :: \<open>'b::default mem\<close>
  show \<open>(mem_alloc_pool s \<noteq> {}) = (\<exists>a s'. alloc_mem s = Some (a, s'))\<close>
  proof -
    have \<open>(memory_allocator s \<noteq> None) = (\<exists>a s'. alloc_mem s = Some (a, s'))\<close>
      by (metis alloc_mem_fail alloc_mem_success not_None_eq)
    moreover have \<open>memory_allocator s \<noteq> None \<longleftrightarrow> mem_alloc_pool s \<noteq> {}\<close> 
      using mem_alloc_pool_def by auto
    ultimately show ?thesis by blast
  qed
next
  fix s1 s2 :: \<open>'a mem\<close>
  assume \<open>s1 \<sharp> s2\<close>
  then show \<open>\<forall>a. mem_perm_map s1 a \<sharp> mem_perm_map s2 a\<close>
    apply (simp add: Permissioned_Heap.disjoint_mem_def Permissioned_Heap.mem_perm_map_def 
        disjoint_share_def shareable_value_to_share_def split: shareable_value.splits)
    by (metis disjoint_fun_def disjoint_rbt_share_map_def disjoint_share_def disjoint_shareable_value.simps(3))
next
  fix s1 s2 :: \<open>'a mem\<close>
  assume \<open>s1 \<sharp> s2\<close>
  then show \<open>mem_alloc_pool s1 \<sharp> mem_alloc_pool s2\<close> 
    by (clarsimp simp add: mem_alloc_pool_def disjoint_mem_def disjoint_option_def
      disjoint_set_def split!: option.splits)
next
  fix s1 s2 :: \<open>'a mem\<close> and a
  assume \<open>s1 \<sharp> s2\<close>
  from this show \<open>mem_perm_map (s1+s2) a = mem_perm_map s1 a \<squnion> mem_perm_map s2 a\<close>
    by (clarsimp simp add: mem_alloc_pool_def disjoint_mem_def plus_mem_components[OF \<open>s1 \<sharp> s2\<close>]
      mem_perm_map_def plus_fun_def plus_rbt_share_map_def add_rbt_share_map_\<alpha>' disjoint_rbt_share_map_def
      disjoint_fun_def shareable_value_to_share_plus plus_share_def)
next
  fix s1 s2 :: \<open>'a mem\<close>
  assume \<open>s1 \<sharp> s2\<close>
  then show \<open>mem_alloc_pool (s1 + s2) = mem_alloc_pool s1 \<union> mem_alloc_pool s2\<close>
    by (auto simp add: mem_alloc_pool_def disjoint_mem_def plus_mem_components[OF \<open>s1 \<sharp> s2\<close>]
       plus_option_def disjoint_option_def split!: option.splits)
next
  fix s1 s2 :: \<open>'a mem\<close> and a v
  assume \<open>s1 \<sharp> s2\<close> and \<open>read_mem s1 a = Some v\<close>
  then show \<open>read_mem (s1 + s2) a = Some v\<close>
    by (simp add: read_mem_local_action)
next
  fix s1 s1' s2 :: \<open>'a mem\<close> and a v
  assume \<open>s1 \<sharp> s2\<close> and \<open>write_mem s1 a v = Some s1'\<close>
  then show \<open>write_mem (s1 + s2) a v = Some (s1' + s2) \<and> s1' \<sharp> s2\<close> 
    using write_mem_local_action by force
next
  fix s1 s1' s2 :: \<open>'a mem\<close> and a
  assume \<open>s1 \<sharp> s2\<close> and \<open>alloc_mem s1 = Some (a, s1')\<close>
  then show \<open>alloc_mem (s1 + s2) = Some (a, s1' + s2) \<and> s1' \<sharp> s2\<close>
    using alloc_mem_local_action by force
next
  fix s :: \<open>'b mem\<close> and a v s'
  assume \<open>write_mem s a v = Some s'\<close>
  then show \<open>mem_alloc_pool s = mem_alloc_pool s'\<close>
    by (simp add: mem_alloc_pool_def write_mem_success_reverse'(1))
next
  fix s s' :: \<open>'b::default mem\<close> and a
  assume \<open>alloc_mem s = Some (a, s')\<close>
  show \<open>a \<in> mem_alloc_pool s \<and> mem_alloc_pool s' = mem_alloc_pool s - {a} \<and> mem_perm_map s' a = \<top>\<close>
    using alloc_mem_success_reverse'[OF \<open>alloc_mem s = Some (a, s')\<close>]
    by (simp add: mem_perm_map_def shareable_value_to_share_def nonempty_share_top_eq) 
next
  fix s1 s2 :: \<open>'b mem\<close>
  assume \<open>s1 \<sharp> s2\<close> and \<open>mem_can_alloc s1\<close>
  from this show \<open>mem_can_alloc (s1 + s2)\<close>
    by (clarsimp simp add: plus_mem_components mem_can_alloc_def plus_option_def)
next
  fix s :: \<open>'b mem\<close> and a v s'
  assume \<open>mem_can_alloc s\<close> and \<open>write_mem s a v = Some s'\<close>
  from this show \<open>mem_can_alloc s'\<close>
    unfolding mem_can_alloc_def by (simp add: write_mem_success_reverse'(1))
next
  fix s :: \<open>'b::default mem\<close> and a s' assume \<open>mem_can_alloc s\<close> and \<open>alloc_mem s = Some (a,s')\<close>
  then show \<open>mem_can_alloc s'\<close>
    using alloc_mem_preserves_valid by blast
next
  fix s :: \<open>'v mem\<close>
  assume \<open>mem_can_alloc s\<close>
  from this show \<open>\<exists>s1 s2. s = s1 + s2 \<and> s1 \<sharp> s2 \<and> mem_can_alloc s1 \<and>
    mem_alloc_pool s1 = mem_alloc_pool s \<and> mem_alloc_pool s2 = {} \<and>
      (\<forall>a. mem_perm_map s1 a = \<bottom>) \<and> (\<forall>a. mem_perm_map s2 a = mem_perm_map s a)\<close> 
    using mem_split_allocator by blast
next
  fix s :: \<open>'v mem\<close> and p1 p2
  assume \<open>p1 \<sharp> p2\<close> and \<open>mem_perm_map s = p1+p2\<close> 
  then show \<open>\<exists>s1 s2. s1 \<sharp> s2 \<and> s = s1 + s2 \<and> mem_perm_map s1 = p1 \<and> mem_perm_map s2 = p2\<close> 
    by (simp add: mem_split_perm)
qed

global_interpretation References: reference \<open>\<lambda>_ _ _ _ _ _. ()\<close> 
  urust_heap_update_raw_fun 
  urust_heap_dereference_raw_fun 
  urust_heap_reference_raw_fun 
  urust_heap_points_to_raw' 
  \<open>\<lambda>_. UNIV\<close> UNIV
  urust_heap_can_alloc_reference
   defines urust_heap_reference_fun = \<open>References.reference_fun\<close>
       and urust_heap_dereference_fun = \<open>References.dereference_fun\<close>
       and urust_heap_ro_dereference_fun = \<open>References.ro_dereference_fun\<close>
       and urust_heap_modify_raw_fun = \<open>References.modify_raw_fun\<close>
       and urust_heap_modify_fun = \<open>References.modify_fun\<close>
       and urust_heap_update_fun = \<open>References.update_fun\<close>
       and urust_heap_slice_index = \<open>References.slice_index\<close>
       and urust_heap_slice_index_array = \<open>References.slice_index_array\<close>
       and urust_heap_take_mut_ref_option = \<open>References.take_mut_ref_option\<close>
       and urust_heap_option_as_mut = \<open>References.option_as_mut\<close>
       and urust_heap_iter_mut = \<open>References.iter_mut\<close>
  using Global_Perm_Store.reference_sublocale by simp

(*<*)
end
(*>*)
