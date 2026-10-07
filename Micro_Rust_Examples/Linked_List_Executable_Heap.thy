(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Linked_List_Executable_Heap
  imports
    Linked_List
    Micro_Rust_Std_Lib.StdLib_References  
    Micro_Rust_Runtime.Runtime_Heap
begin
(*>*)

section\<open>Executing the Linked List example using the runtime heap\<close>

text\<open>In this section, we provide a minimal environment supporting the linked list example above,
and use it to run a few tests. We use \<^verbatim>\<open>nat\<close> as the value type on the linked list nodes.\<close>

text\<open>First, we need a global value type \<^verbatim>\<open>'fv\<close> for the uRust heap. Here, we face two requirements:

First, it must contain \<^verbatim>\<open>('addr, 'fv) gref option\<close>, which in our case is isomorphic to \<^verbatim>\<open>'addr option\<close>.
Second, it must support a focus to \<^verbatim>\<open>('addr, 'fv, 't) ll_node_raw\<close>, which is isomorphic to
\<^verbatim>\<open>'t \<times> 'addr option\<close>.\<close>                        

type_synonym addr_ty = nat
type_synonym val_ty = nat

\<comment>\<open>TODO: Building those prism and foci by hand is unfortunately still quite cumbersome. Improve automation.
For example, auto-derive prisms for \<^verbatim>\<open>datatype\<close> in the same way as lense are auto-derived for \<^verbatim>\<open>datatype_record\<close>.\<close>
datatype ll_example_gv = 
      raw_ref \<open>addr_ty option\<close>
    | ll_node_raw \<open>val_ty \<times> addr_ty option\<close>
    | Uninitialized

instantiation "ll_example_gv" :: default
begin
definition \<open>default_ll_example_gv \<equiv> ll_example_gv.Uninitialized\<close>
instance ..
end

type_synonym ll_node_raw_concrete = \<open>(addr_ty, ll_example_gv, val_ty) ll_node_raw\<close>

definition ll_node_isoprism :: \<open>(val_ty \<times> addr_ty option, ll_node_raw_concrete) prism\<close>
  where \<open>ll_node_isoprism \<equiv> iso_prism (\<lambda>p. make_ll_node_raw (fst p) (map_option make_gref (snd p)))
                                          (\<lambda>n. (ll_node_raw.data n, map_option gref_address (ll_node_raw.next n)))\<close>
lemma ll_node_isoprism_valid: \<open>is_valid_prism ll_node_isoprism\<close> 
  unfolding ll_node_isoprism_def by (auto intro!: iso_prism_valid simp add: ll_node_raw.expand 
    option.expand option.map_sel prod.expand)

definition \<open>the_ll_node_raw gv \<equiv> case gv of ll_node_raw n \<Rightarrow> Some n | _ \<Rightarrow> None\<close>
definition \<open>the_raw_ref gv \<equiv> case gv of raw_ref r \<Rightarrow> Some r | _ \<Rightarrow> None\<close>
definition \<open>ll_example_gv_prism_raw_ref \<equiv> make_prism raw_ref the_raw_ref\<close>
definition \<open>ll_example_gv_prism_ll_node_raw \<equiv> make_prism ll_node_raw the_ll_node_raw\<close>
definition \<open>ll_example_gv_prism_ll_node = prism_compose ll_example_gv_prism_ll_node_raw ll_node_isoprism\<close>
lemma ll_example_gv_prism_raw_ref_valid: \<open>is_valid_prism ll_example_gv_prism_raw_ref\<close>
  by (auto simp add: is_valid_prism_def the_raw_ref_def ll_example_gv_prism_raw_ref_def split!: ll_example_gv.splits)
lemma ll_example_gv_prism_ll_node_raw_valid: \<open>is_valid_prism ll_example_gv_prism_ll_node_raw\<close> 
  by (auto simp add: is_valid_prism_def the_ll_node_raw_def ll_example_gv_prism_ll_node_raw_def split!: ll_example_gv.splits)
lemma ll_example_gv_prism_ll_node_valid: \<open>is_valid_prism ll_example_gv_prism_ll_node\<close>  
  by (simp add: ll_example_gv_prism_ll_node_def ll_example_gv_prism_ll_node_raw_valid ll_node_isoprism_valid prism_compose_valid)

\<comment>\<open>The following is necessary to avoid code generation failing for \<^verbatim>\<open>\<integral>\<^sub>p ll_example_gv_prism_ll_node\<close>.\<close>
definition \<open>ll_example_gv_focus_ll_node = \<integral>\<^sub>p ll_example_gv_prism_ll_node\<close>
declare ll_example_gv_focus_ll_node_def[symmetric, code_unfold]
declare prism_to_focus.rep_eq[OF ll_example_gv_prism_ll_node_valid, 
                              folded ll_example_gv_focus_ll_node_def, code]

definition gref_opt_prism :: "(addr_ty option, (addr_ty, ll_example_gv) gref option) prism" where
  \<open>gref_opt_prism \<equiv> iso_prism (Option.map_option State_References.make_gref)
                                       (Option.map_option State_References.gref_address)\<close>

lemma gref_opt_prism_valid: \<open>is_valid_prism gref_opt_prism\<close>
  by (simp add: iso_prism_valid gref_opt_prism_def option.expand option.map_sel)

definition \<open>ll_example_gv_prism_gref_opt \<equiv> prism_compose ll_example_gv_prism_raw_ref gref_opt_prism\<close>

lemma ll_example_gv_prism_ref_opt_valid: \<open>is_valid_prism ll_example_gv_prism_gref_opt\<close>
  by (simp add: gref_opt_prism_valid ll_example_gv_prism_gref_opt_def ll_example_gv_prism_raw_ref_valid 
    prism_compose_valid)

text\<open>We use the heap's address type as the concrete address type in the linked list nodes.
This would be different for a memory-backed linked list: There, the logical reference type
would include heap addresses and physical addresses, but the concrete address type in the list
nodes would be restricted to physical addresses.\<close>
definition ll_example_caddr_id_prism :: \<open>(addr_ty, addr_ty) prism\<close> where
  \<open>ll_example_caddr_id_prism \<equiv> iso_prism id id\<close>                             
lemma ll_example_caddr_id_prism_valid: \<open>is_valid_prism ll_example_caddr_id_prism\<close>              
  by (simp add: iso_prism_valid ll_example_caddr_id_prism_def)
    
global_interpretation ll_example_ctxt: ll_example        
  urust_heap_update_raw_fun 
  urust_heap_dereference_raw_fun 
  urust_heap_reference_raw_fun                                  
  urust_heap_points_to_raw' 
  \<open>\<lambda>_. UNIV\<close> UNIV       
  urust_heap_can_alloc_reference
  \<open>\<lambda> _ _ _ _ _ _. ()\<close>                   
  ll_example_gv_prism_gref_opt
  ll_example_caddr_id_prism
  ll_example_gv_focus_ll_node
  \<comment>\<open>I \<^emph>\<open>think\<close> the following rewrites are necessary because the general heap implementation is more
  polymorphic than our specific instantiation, and in that case the folding does not work automatically.\<close>
  rewrites \<open>reference_defs.dereference_fun urust_heap_dereference_raw_fun = urust_heap_dereference_fun\<close>
    and \<open>reference_defs.update_fun urust_heap_update_raw_fun urust_heap_dereference_raw_fun = urust_heap_update_fun\<close>
    and \<open>reference_defs.reference_fun urust_heap_reference_raw_fun = urust_heap_reference_fun\<close>
  defines reverse_unlink = \<open>ll_example_ctxt.reverse_unlink\<close>
      and reverse_unlink' = \<open>ll_example_ctxt.reverse_unlink'\<close>
      and ref_gref_opt_new = \<open>ll_example_ctxt.ref_gref_opt.new\<close>
      and ref_gref_opt_focus = \<open>ll_example_ctxt.ref_gref_opt.focus\<close>
proof -
  show \<open>ll_example urust_heap_update_raw_fun urust_heap_dereference_raw_fun urust_heap_reference_raw_fun
     urust_heap_points_to_raw' (\<lambda>_. UNIV) UNIV urust_heap_can_alloc_reference ll_example_gv_prism_gref_opt
     ll_example_caddr_id_prism\<close>
    apply standard
    apply (simp add: ll_example_caddr_id_prism_valid)
    apply (simp add: ll_example_gv_prism_ref_opt_valid)  
    apply (simp add: References.can_create_gref_for_prism_def)
    done
qed (auto simp add: urust_heap_dereference_fun_def urust_heap_update_fun_def urust_heap_reference_fun_def)

context
begin

private lift_definition mem_from_alist :: \<open>(nat \<times> 'v) list \<Rightarrow> 'v mem\<close>
  is \<open>\<lambda>l. make_mem_raw (rbt_share_map_bulkload_top l) (Some (1 + Max (fst ` set l)))\<close>
  apply (clarsimp simp add: mem_is_valid_def rbt_share_map_\<alpha>_def rbt_share_map_bulkload_top_def
    rbt_share_map_bulkload_def shareable_value_option_def split: option.splits)
  apply transfer'
  apply (clarsimp simp add: lookup_bulkload map_of_map)
  apply (metis Max_ge domI dom_map_of_conv_image_fst finite_dom_map_of le_imp_less_Suc)
  done

private lift_definition mem_to_alist :: \<open>'v mem \<Rightarrow> (nat \<times> 'v) list\<close>
  is \<open>\<lambda>m.  List.map (\<lambda> (k, v, _). (k, v)) (rbt_share_map_entries (memory_rbt m))\<close> .

private definition map_continuation :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'v, 'r, unit, unit prompt, unit prompt_output) continuation \<Rightarrow> ('b, 'v, 'r, unit, unit prompt, unit prompt_output) continuation\<close>
  where \<open>map_continuation f c \<equiv> case c of
    Abort a \<sigma> \<Rightarrow> Abort a (f \<sigma>)
  | Success v \<sigma> \<Rightarrow> Success v (f \<sigma>)
  | Return r \<sigma> \<Rightarrow> Return r (f \<sigma>)
  | _ \<Rightarrow> undefined\<close>

private definition \<open>simplify \<equiv> map_continuation mem_to_alist\<close>
private definition \<open>run_it st f \<equiv> simplify (deep_evaluate_det yield_handler_det_no_yield (call f) st :: (_, _, unit, unit, unit prompt, unit prompt_output) continuation)\<close>

private definition \<sigma> :: \<open>ll_example_gv mem\<close> 
  where \<open>\<sigma> \<equiv> let \<epsilon> = prism_embed ll_example_gv_prism_ll_node in 
              mem_from_alist [(42, \<epsilon> \<lparr> data = 0, next = Some (make_gref 43) \<rparr>),
                              (43, \<epsilon> \<lparr> data = 1, next = Some (make_gref 44) \<rparr>),
                              (44, \<epsilon> \<lparr> data = 1, next = Some (make_gref 45) \<rparr>),
                              (45, \<epsilon> \<lparr> data = 2, next = Some (make_gref 46) \<rparr>),
                              (46, \<epsilon> \<lparr> data = 3, next = Some (make_gref 47) \<rparr>),
                              (47, \<epsilon> \<lparr> data = 4, next = Some (make_gref 48) \<rparr>),
                              (48, \<epsilon> \<lparr> data = 5, next = None \<rparr>) \<comment>\<open>end of linked list\<close>
                            ]\<close>

private definition ll_head         where \<open>ll_head \<equiv> Some (make_gref 42)\<close>
private definition ll_head_invalid where \<open>ll_head_invalid \<equiv> Some (make_gref 40)\<close>

\<comment>\<open>\<^verbatim>\<open>Success (Some (make_gref 45), Some (make_gref 46))
  [(42, ll_node_raw (0, None)), 
   (43, ll_node_raw (1, Some 42)), 
   (44, ll_node_raw (1, Some 43)), 
   (45, ll_node_raw (2, Some 44)),  (* Start of reversed prefix*)
   (46, ll_node_raw (3, Some 47)),  (* Unmodified suffix *)
   (47, ll_node_raw (4, Some 48)), 
   (48, ll_node_raw (5, None)),
   (49, raw_ref (Some 46)),
   (50, raw_ref (Some 45)),]"\<close>\<close>
value[code] \<open>run_it \<sigma> (reverse_unlink' 4 ll_head)\<close>

(* "Abort DanglingPointer" *)
value[code] \<open>run_it \<sigma> (reverse_unlink' 7 ll_head_invalid)\<close> 

(* "Abort (Panic STR ''Unexpectedly short linked list'')" *)
value[code] \<open>run_it \<sigma> (reverse_unlink' 8 ll_head)\<close> 

end

(*<*)
end
(*>*)