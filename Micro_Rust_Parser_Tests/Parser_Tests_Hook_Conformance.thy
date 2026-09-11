(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Tests_Hook_Conformance
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Term_Hook
begin

declare [[urust_term_hook_conformance_check = true]]

section\<open> Hook conformance corpus \<close>

text\<open>
This theory contains the 33 rows from \<open>Conformance_Corpus.thy\<close> whose exact mechanical
replacement of every legacy \<open>\<lbrakk>src\<rbrakk>\<close> embedding by
\<open>\<mu>\<open>src\<close>\<close> is accepted. Each equality retains the original legacy RHS and must close by
\<open>refl\<close>. Rejected replacements are tested in
\<open>Parser_Tests_Hook_Negative_Conformance.thy\<close>.
\<close>

section\<open> Expression goldens \<close>

subsection\<open>Literals and Basic Values\<close>

subsubsection\<open>Numeric Literals\<close>

lemma \<open>\<mu>\<open> 0 \<close> = \<lbrakk> 0 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 1 \<close> = \<lbrakk> 1 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 42 \<close> = \<lbrakk> 42 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0xff \<close> = \<lbrakk> 0xff \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Unit Literal\<close>

lemma \<open>\<mu>\<open> () \<close> = \<lbrakk> () \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> (); () \<close> = \<lbrakk> (); () \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> (); (); \<close> = \<lbrakk> (); (); \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> return (); \<close> = \<lbrakk> return (); \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> return; \<close> = \<lbrakk> return; \<rbrakk>\<close> by (rule refl)

subsection\<open>Numeric Ascriptions\<close>

lemma \<open>\<mu>\<open> 0_u8 \<close> = \<lbrakk> 0_u8 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 1_u8 \<close> = \<lbrakk> 1_u8 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0x4_u8 \<close> = \<lbrakk> 0x4_u8 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0_u16 \<close> = \<lbrakk> 0_u16 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 1_u16 \<close> = \<lbrakk> 1_u16 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0x12_u16 \<close> = \<lbrakk> 0x12_u16 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0_u32 \<close> = \<lbrakk> 0_u32 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 1_u32 \<close> = \<lbrakk> 1_u32 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0x2000_u32 \<close> = \<lbrakk> 0x2000_u32 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0_u64 \<close> = \<lbrakk> 0_u64 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 1_u64 \<close> = \<lbrakk> 1_u64 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0x2f0_u64 \<close> = \<lbrakk> 0x2f0_u64 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0_usize \<close> = \<lbrakk> 0_usize \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 1_usize \<close> = \<lbrakk> 1_usize \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0xffffffff0_usize \<close> = \<lbrakk> 0xffffffff0_usize \<rbrakk>\<close> by (rule refl)

subsection\<open>Control Flow\<close>

lemma \<open>(FunctionBody \<mu>\<open> { () } () \<close>) = (FunctionBody \<lbrakk> { () } () \<rbrakk>)\<close>
  by (rule refl)
lemma \<open>\<mu>\<open> unsafe { () } () \<close> = \<lbrakk> unsafe { () } () \<rbrakk>\<close>
  by (rule refl)
lemma \<open>\<mu>\<open> return; \<close> = \<lbrakk> return; \<rbrakk>\<close>
  by (rule refl)
lemma \<open>(FunctionBody \<mu>\<open> ({return;}) == (); return; \<close>) =
    (FunctionBody \<lbrakk> ({return;}) == (); return; \<rbrakk>)\<close>
  by (rule refl)

subsection\<open>Closures\<close>

lemma \<open>\<mu>\<open> |x| x \<close> = \<lbrakk> |x| x \<rbrakk>\<close> by (rule refl)

subsection\<open>Yield\<close>

lemma \<open>\<mu>\<open> \<y>\<i>\<e>\<l>\<d> \<close> = \<lbrakk> \<y>\<i>\<e>\<l>\<d> \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> \<y>\<i>\<e>\<l>\<d>; () \<close> = \<lbrakk> \<y>\<i>\<e>\<l>\<d>; () \<rbrakk>\<close>
  by (rule refl)

subsection\<open>Array and Slice Expression Literals\<close>

lemma \<open>\<mu>\<open> & mut [] \<close> = \<lbrakk> & mut [] \<rbrakk>\<close> by (rule refl)

subsection\<open>Expected Types\<close>

lemma \<open>(\<mu>\<open> 1 \<close> :: ('s, nat, 'r, 'abort, 'i, 'o) expression) =
    (\<lbrakk> 1 \<rbrakk> :: ('s, nat, 'r, 'abort, 'i, 'o) expression)\<close>
  by (rule refl)

end
