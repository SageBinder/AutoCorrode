(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Scalar_Profile
  imports
    Shallow_Computation.Core_Expression
    "Word_Lib.Signed_Words"
begin

section\<open>Prototype C scalar profile\<close>

text\<open>
The first C frontend slice uses a deliberately fixed scalar profile. Plain C
\<^verbatim>\<open>int\<close> is a signed 32-bit word, independently of the host running Isabelle.
The abort payload is provisional and contains only the undefined behaviour needed by this slice.
\<close>

type_synonym c_int = \<open>32 sword\<close>

datatype c_abort =
  SignedOverflow

definition c_signed_add ::
  \<open>c_int \<Rightarrow> c_int \<Rightarrow> ('s, c_int, 'r, c_abort, 'i, 'o) expression\<close>
where [shallow_computation_simps]:
  \<open>c_signed_add a b \<equiv>
     let result = sint a + sint b in
       if result < -2147483648 \<or> result > 2147483647 then
         abort (CustomAbort SignedOverflow)
       else
         literal (word_of_int result)\<close>

end
