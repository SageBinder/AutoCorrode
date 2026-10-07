(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Global_Store
  imports
    State_References
    Shallow_Computation.Core_Expression
begin

section\<open>Abstract global stores\<close>

named_theorems global_store_simps

text\<open>An abstract global store supports partial reads and writes together with
allocation of fresh locations. The locale states the laws needed by the generic
reference computations below.\<close>

locale global_store =
  fixes
    read_store :: \<open>'state \<Rightarrow> 'address \<rightharpoonup> 'cell\<close> and
    write_store ::
      \<open>'state \<Rightarrow> 'address \<Rightarrow> 'cell \<Rightarrow> 'state option\<close> and
    allocate_store :: \<open>'state \<Rightarrow> ('address \<times> 'state) option\<close>
  assumes
    write_store_read_store [global_store_simps]:
      \<open>write_store \<sigma> k v = Some \<sigma>' \<Longrightarrow>
       read_store \<sigma>' k = Some v\<close> and
    write_store_rearrange [global_store_simps]:
      \<open>k \<noteq> k' \<Longrightarrow>
       Option.bind (write_store \<sigma> k v)
         (\<lambda>\<sigma>'. write_store \<sigma>' k' v') =
       Option.bind (write_store \<sigma> k' v')
         (\<lambda>\<sigma>'. write_store \<sigma>' k v)\<close> and
    write_store_write_store [global_store_simps]:
      \<open>write_store \<sigma> k v = Some \<sigma>' \<Longrightarrow>
       write_store \<sigma>' k v' = write_store \<sigma> k v'\<close> and
    allocate_write_succeeds:
      \<open>allocate_store \<sigma> = Some (fresh, \<sigma>') \<Longrightarrow>
       \<exists>\<sigma>''. write_store \<sigma>' fresh v = Some \<sigma>''\<close>
begin

definition reference_raw ::
    \<open>'cell \<Rightarrow>
      ('state, ('address, 'cell) gref, 'return, 'abort, 'input, 'output)
        expression\<close>
  where
    \<open>reference_raw value \<equiv> Expression (\<lambda>\<sigma>.
       case allocate_store \<sigma> of
         None \<Rightarrow> Abort AssertionFailed \<sigma>
       | Some (addr, \<sigma>') \<Rightarrow>
           (case write_store \<sigma>' addr value of
              None \<Rightarrow> Abort AssertionFailed \<sigma>'
            | Some \<sigma>'' \<Rightarrow> Success (make_gref addr) \<sigma>''))\<close>

definition reference_raw_fun ::
    \<open>'cell \<Rightarrow>
      ('state, ('address, 'cell) gref, 'abort, 'input, 'output)
        function_body\<close>
  where
    \<open>reference_raw_fun value \<equiv> FunctionBody (reference_raw value)\<close>

definition modify_raw ::
    \<open>('address, 'cell) gref \<Rightarrow>
      ('cell \<Rightarrow> 'cell) \<Rightarrow>
      ('state, unit, 'return, 'abort, 'input, 'output) expression\<close>
  where
    \<open>modify_raw ref f \<equiv>
       bind (get read_store) (\<lambda>store.
         case store (address ref) of
           None \<Rightarrow> abort DanglingPointer
         | Some old \<Rightarrow>
             put_assert
               (\<lambda>\<sigma>. write_store \<sigma> (address ref) (f old))
               DanglingPointer)\<close>

definition modify_raw_fun ::
    \<open>('address, 'cell) gref \<Rightarrow>
      ('cell \<Rightarrow> 'cell) \<Rightarrow>
      ('state, unit, 'abort, 'input, 'output) function_body\<close>
  where
    \<open>modify_raw_fun ref f \<equiv> FunctionBody (modify_raw ref f)\<close>

definition update_raw ::
    \<open>('address, 'cell) gref \<Rightarrow>
      'cell \<Rightarrow>
      ('state, unit, 'return, 'abort, 'input, 'output) expression\<close>
  where \<open>update_raw ref value \<equiv> modify_raw ref (\<lambda>_. value)\<close>

definition update_raw_fun ::
    \<open>('address, 'cell) gref \<Rightarrow>
      'cell \<Rightarrow>
      ('state, unit, 'abort, 'input, 'output) function_body\<close>
  where
    \<open>update_raw_fun ref value \<equiv> FunctionBody (update_raw ref value)\<close>

definition dereference_by_value_raw ::
    \<open>('address, 'cell) gref \<Rightarrow>
      ('state, 'cell, 'return, 'abort, 'input, 'output) expression\<close>
  where
    \<open>dereference_by_value_raw ref \<equiv>
       bind (get read_store) (\<lambda>store.
         case store (address ref) of
           None \<Rightarrow> abort DanglingPointer
         | Some value \<Rightarrow> literal value)\<close>

definition dereference_by_value_raw_fun ::
    \<open>('address, 'cell) gref \<Rightarrow>
      ('state, 'cell, 'abort, 'input, 'output) function_body\<close>
  where
    \<open>dereference_by_value_raw_fun ref \<equiv>
       FunctionBody (dereference_by_value_raw ref)\<close>

end

end
