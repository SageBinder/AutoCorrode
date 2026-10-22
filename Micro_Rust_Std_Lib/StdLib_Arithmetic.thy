(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Arithmetic
  imports Crush.Crush StdLib_References
begin
(*>*)

subsection\<open>Arithmetic\<close>

definition overflowing_mul :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_mul x y \<equiv> FunctionBody(literal (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil))\<close>

definition overflowing_add :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_add x y \<equiv> FunctionBody (literal (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil))\<close>

definition wrapping_add_unsigned :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('machine, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>wrapping_add_unsigned \<equiv> \<lambda>self rhs. FunctionBody (literal (self + rhs))\<close>

definition word_sub_saturating_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word\<close> where
  \<open>word_sub_saturating_core e f \<equiv> if e < f then 0 else e - f\<close>

definition saturating_sub :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>saturating_sub e f \<equiv> FunctionBody (literal (word_sub_saturating_core e f))\<close>

definition checked_mul_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_mul_core w v \<equiv>
     if unat w * unat v \<ge> 2^LENGTH('a) then None else Some (w * v)\<close>

definition checked_add_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_add_core w v \<equiv>
     if unat w + unat v \<ge> 2^LENGTH('a) then None else Some (w + v)\<close>

definition checked_mul :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_mul w v \<equiv> FunctionBody (literal (checked_mul_core w v))\<close>

definition checked_add :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_add w v \<equiv> FunctionBody (literal (checked_add_core w v))\<close>

definition div_ceil_pure :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close> where
  \<open>div_ceil_pure x y \<equiv> (x + y - 1) div y\<close>

definition div_ceil :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('machine, 'a word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>div_ceil x y \<equiv> FunctionBody (literal (div_ceil_pure x y))\<close>

\<comment> \<open>Contracts and verifications\<close>

definition overflowing_mul_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close> where
  [crush_contracts]: \<open>overflowing_mul_contract x y \<equiv>
    let pre = emp in \<comment> \<open>Any inputs are acceptable, and no resource is needed\<close>
    let post = \<lambda>ret. \<langle>ret = (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil)\<rangle> in
      make_function_contract pre post\<close>

lemma overflowing_mul_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_mul x y \<Turnstile>\<^sub>F overflowing_mul_contract x y\<close>
by (crush_boot f: overflowing_mul_def contract: overflowing_mul_contract_def) crush_base

definition overflowing_add_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close>where
  [crush_contracts]: \<open>overflowing_add_contract x y \<equiv>
    let pre = emp in
    let post = \<lambda>ret. \<langle>ret = (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil)\<rangle> in
      make_function_contract pre post\<close>

lemma overflowing_add_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_add x y \<Turnstile>\<^sub>F overflowing_add_contract x y\<close>
by (crush_boot f: overflowing_add_def contract: overflowing_add_contract_def) crush_base

definition wrapping_add_unsigned_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wrapping_add_unsigned_contract x y \<equiv>
    let pre = emp in
    let post = \<lambda>ret. \<langle>ret = x + y\<rangle> in
      make_function_contract pre post\<close>

lemma wrapping_add_unsigned_spec [crush_specs]:
  shows \<open>\<Gamma> ; wrapping_add_unsigned x y \<Turnstile>\<^sub>F wrapping_add_unsigned_contract x y\<close>
by (crush_boot f: wrapping_add_unsigned_def contract: wrapping_add_unsigned_contract_def) crush_base

definition saturating_sub_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>saturating_sub_contract x y \<equiv>
    let pre = emp in
    let post = \<lambda>ret. \<langle>ret = (if x < y then 0 else x - y)\<rangle> in
      make_function_contract pre post\<close>

lemma saturating_sub_spec [crush_specs]:
  shows \<open>\<Gamma> ; saturating_sub x y \<Turnstile>\<^sub>F saturating_sub_contract x y\<close>
by (crush_boot f: saturating_sub_def contract: saturating_sub_contract_def)
  (crush_base simp add: word_sub_saturating_core_def)

definition div_ceil_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>div_ceil_contract x y \<equiv>
    let pre  = emp;
        post = \<lambda>ret. \<langle>ret = (x + y - 1) div y\<rangle>
     in make_function_contract pre post\<close>

lemma div_ceil_spec [crush_specs]:
  shows \<open>\<Gamma> ; div_ceil x y \<Turnstile>\<^sub>F div_ceil_contract x y\<close>
by (crush_boot f: div_ceil_def contract: div_ceil_contract_def) (crush_base simp add: div_ceil_pure_def)

section\<open>Primitive integer bounds\<close>

text\<open>The associated constants \<^verbatim>\<open>MIN\<close> and \<^verbatim>\<open>MAX\<close> of the primitive integer types that the
uRust type registry maps by default, written with Rust's primitive path heads, for example
\<^verbatim>\<open>u64::MAX\<close>. Signed types share the word type of the unsigned type of the same width, so
their bounds are two's-complement bit patterns.\<close>

definition u8_min :: \<open>8 word\<close> where \<open>u8_min \<equiv> 0\<close>
definition u8_max :: \<open>8 word\<close> where \<open>u8_max \<equiv> - 1\<close>
definition u16_min :: \<open>16 word\<close> where \<open>u16_min \<equiv> 0\<close>
definition u16_max :: \<open>16 word\<close> where \<open>u16_max \<equiv> - 1\<close>
definition u32_min :: \<open>32 word\<close> where \<open>u32_min \<equiv> 0\<close>
definition u32_max :: \<open>32 word\<close> where \<open>u32_max \<equiv> - 1\<close>
definition u64_min :: \<open>64 word\<close> where \<open>u64_min \<equiv> 0\<close>
definition u64_max :: \<open>64 word\<close> where \<open>u64_max \<equiv> - 1\<close>
definition usize_min :: \<open>64 word\<close> where \<open>usize_min \<equiv> 0\<close>
definition usize_max :: \<open>64 word\<close> where \<open>usize_max \<equiv> - 1\<close>
definition i32_min :: \<open>32 word\<close> where \<open>i32_min \<equiv> 0x80000000\<close>
definition i32_max :: \<open>32 word\<close> where \<open>i32_max \<equiv> 0x7FFFFFFF\<close>
definition i64_min :: \<open>64 word\<close> where \<open>i64_min \<equiv> 0x8000000000000000\<close>
definition i64_max :: \<open>64 word\<close> where \<open>i64_max \<equiv> 0x7FFFFFFFFFFFFFFF\<close>

urust_notation (literal) u8_min ("u8::MIN")
urust_notation (literal) u8_max ("u8::MAX")
urust_notation (literal) u16_min ("u16::MIN")
urust_notation (literal) u16_max ("u16::MAX")
urust_notation (literal) u32_min ("u32::MIN")
urust_notation (literal) u32_max ("u32::MAX")
urust_notation (literal) u64_min ("u64::MIN")
urust_notation (literal) u64_max ("u64::MAX")
urust_notation (literal) usize_min ("usize::MIN")
urust_notation (literal) usize_max ("usize::MAX")
urust_notation (literal) i32_min ("i32::MIN")
urust_notation (literal) i32_max ("i32::MAX")
urust_notation (literal) i64_min ("i64::MIN")
urust_notation (literal) i64_max ("i64::MAX")

section\<open>\<^verbatim>\<open>NonZeroU64\<close>\<close>

typedef nonzero_u64 = \<open>{ w::64 word. w \<noteq> 0 }\<close>
  morphisms nonzero_u64_project nonzero_u64_inject
proof -
  have \<open>1 \<in> { w::64 word. w \<noteq> 0 }\<close>
    by simp
  from this show ?thesis
    by blast
qed

urust_type "NonZeroU64" = \<open>nonzero_u64\<close>

setup_lifting type_definition_nonzero_u64

lift_definition (code_dt) nonzerou64_new_core :: \<open>64 word \<Rightarrow> nonzero_u64 option\<close> is
  \<open>\<lambda>(n::64 word). if n = 0 then None else Some n\<close> by simp

definition nonzerou64_new :: \<open>64 word \<Rightarrow> ('machine, nonzero_u64 option, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzerou64_new n \<equiv> FunctionBody (if n = 0 then literal None else literal (Some (nonzero_u64_inject n)))\<close>
micro_rust_notation (call) nonzerou64_new ("NonZeroU64::new")

definition nonzerou64_new_contract :: \<open>64 word \<Rightarrow>
      ('machine::{sepalg}, nonzero_u64 option, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzerou64_new_contract n \<equiv>
     let pre  = emp;
         post = \<lambda>res. \<langle>res = nonzerou64_new_core n\<rangle>
      in make_function_contract pre post\<close>

lemma nonzerou64_new_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzerou64_new n \<Turnstile>\<^sub>F nonzerou64_new_contract n\<close>
by (crush_boot f: nonzerou64_new_def contract: nonzerou64_new_contract_def) (crush_base simp add: nonzerou64_new_core_def)

definition nonzerou64_get :: \<open>nonzero_u64 \<Rightarrow> ('machine, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzerou64_get self \<equiv> FunctionBody (literal (nonzero_u64_project self))\<close>

definition nonzerou64_get_contract :: \<open>nonzero_u64 \<Rightarrow> ('machine::{sepalg}, 64 word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzerou64_get_contract nz \<equiv>
     let pre  = emp;
         post = \<lambda>res. \<langle>res = nonzero_u64_project nz\<rangle>
      in make_function_contract pre post\<close>

lemma nonzero_u64_get_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzerou64_get nz \<Turnstile>\<^sub>F nonzerou64_get_contract nz\<close>
by (crush_boot f: nonzerou64_get_def contract: nonzerou64_get_contract_def) crush_base

(*<*)
end
(*>*)
