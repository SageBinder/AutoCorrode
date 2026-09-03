(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Conformance_Corpus
  imports Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
begin

section\<open> Conformance corpus \<close>

text\<open>
The inner-syntax frontend is the oracle. Expression goldens use
\<open>undefined = \<lbrakk>src\<rbrakk>\<close>; parser equality is tested in
\<open>Parser_Test_Conformance.thy\<close>. Definition goldens specify future item
commands, and the final tier records frontend rejections. Proofs remain \<open>sorry\<close>,
so the session uses \<open>quick_and_dirty\<close>. \<open>**\<close> and \<open>!!\<close> mean double
dereference and negation.
\<close>


section\<open> Expression goldens \<close>

subsection\<open>Literals and Basic Values\<close>

subsubsection\<open>Numeric Literals\<close>

lemma \<open>undefined = \<lbrakk> 0 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 1 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 42 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0xff \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>255 :: 8 word\<rrangle> \<rbrakk>\<close> sorry

subsubsection\<open>Boolean Literals\<close>

lemma \<open>undefined = \<lbrakk> \<epsilon>\<open>Bool_Type.true\<close> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> True \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> False \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>False\<rrangle> \<rbrakk>\<close> sorry

subsubsection\<open>Unit Literal\<close>

context
  fixes f :: \<open>unit \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>unit \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
lemma \<open>undefined = \<lbrakk> () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> (); () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> (); (); \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> return (); \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> return; \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> f(()) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> g((),True) \<rbrakk>\<close> sorry
end

subsubsection\<open>String Literals\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
lemma \<open>undefined = \<lbrakk> panic!("oh no!") \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> panic!( \<llangle>''oh no!''\<rrangle> ) \<rbrakk>\<close> sorry
end

subsubsection\<open>HOL Value Injection (Antiquotation)\<close>

lemma \<open>undefined = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined =
  \<lbrakk> \<llangle> \<lbrakk> \<llangle>1 :: nat\<rrangle> \<rbrakk> \<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined =
  \<lbrakk> \<epsilon>\<open> \<lbrakk> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<rbrakk> \<close> \<rbrakk>\<close> sorry

subsection\<open>Type Casts and Ascriptions\<close>

subsubsection\<open>Type Casting\<close>

context
  fixes a_value :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> a_value as u8\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a_value as u16\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a_value as u32\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a_value as u64\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a_value as u64; a_value as u64\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a_value as usize\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a_value as i32\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a_value as i64\<rbrakk>\<close> sorry
end

subsubsection\<open>Raw Pointer Casts\<close>

context
  fixes raw_buf :: \<open>('addr, 'gv) gref\<close>
begin
lemma \<open>undefined = \<lbrakk> raw_buf as *const u8 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> raw_buf as *const u16 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> raw_buf as *const u32 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> raw_buf as *const u64 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> raw_buf as *const usize \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> raw_buf as *mut u8 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> raw_buf as *mut u32 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> raw_buf as *mut u64 \<rbrakk>\<close> sorry
end

subsubsection\<open>Numeric Ascriptions\<close>

lemma \<open>undefined = \<lbrakk> 0_u8 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 1_u8 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0x4_u8 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0_u16 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 1_u16 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0x12_u16 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0_u32 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 1_u32 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0x2000_u32 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0_u64 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 1_u64 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0x2f0_u64 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0_usize \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 1_usize \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> 0xffffffff0_usize \<rbrakk>\<close> sorry

subsection\<open>Boolean Operators\<close>

subsubsection\<open>Boolean Negation\<close>

lemma \<open>undefined = \<lbrakk> !True \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> !False \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> !!True \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if !True { return; } \<rbrakk>\<close> sorry

subsubsection\<open>Boolean Conjunction\<close>

lemma \<open>undefined = \<lbrakk> True && True \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> True && False \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> False && True \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> False && False \<rbrakk>\<close> sorry

subsubsection\<open>Boolean Disjunction\<close>

lemma \<open>undefined = \<lbrakk> True || True \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> True || False \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> False || True \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> False || False \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<rbrakk>\<close> sorry

subsection\<open>Comparison Operators\<close>

subsubsection\<open>Equality and Nonequality\<close>

context
  fixes m n :: \<open>nat\<close>
  fixes h :: \<open>nat \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes x y :: \<open>64 word\<close>
begin
lemma \<open>undefined = \<lbrakk> m == n \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> !(m == n) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> m != n \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> m.h() \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if m.h() == n { m } else { n } \<rbrakk>\<close> sorry
end

subsubsection\<open>Ordering Comparisons\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> x < y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> x <= y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> x > y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> x >= y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> x > \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
end

subsection\<open>Arithmetic Operators\<close>

lemma \<open>undefined = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<rbrakk>\<close> sorry

context
  fixes x y :: \<open>64 word\<close>
begin
lemma \<open>undefined = \<lbrakk> let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>); a + b + c \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<rbrakk>\<close> sorry

subsection\<open>Bitwise Operators\<close>

lemma \<open>undefined = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<rbrakk>\<close> sorry

context
  fixes x y :: \<open>64 word\<close>
begin
lemma \<open>undefined = \<lbrakk> !x + y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> !(!x == x^y) \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<rbrakk>\<close> sorry

subsection\<open>Operator Precedence and Associativity\<close>

text\<open>
Goldens pin this precedence:
\<open>* / %\<close> (50) > \<open>+ -\<close> (49) > \<open><< >>\<close> (48) > \<open>&\<close> (47) >
\<open>^\<close> (46) > \<open>|\<close> (45) > comparisons (44) > \<open>&&\<close> (43) >
\<open>||\<close> (42); prefix \<open>!\<close> is tightest. Comparisons are non-associative
and covered by the negative tier.
\<close>

subsubsection\<open>Associativity (binary operators are left-associative)\<close>

lemma \<open>undefined = \<lbrakk> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<rbrakk>\<close> sorry

subsubsection\<open>Cross-tier precedence (the tighter operator groups first)\<close>

lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<rbrakk>\<close> sorry

subsection\<open>Assignment Operators\<close>

text\<open>
Simple assignment and its identifier, grouped, dereferenced, field, antiquotation,
precedence, associativity, and composition boundaries have runnable frontend-equivalence
coverage in \<open>Parser_Test_Conformance.thy\<close>.
\<close>

subsubsection\<open>Compound Assignment\<close>

text\<open>
The frontend-supported operators \<open>+= -= *= %= &= |= ^= <<= >>=\<close> and their
place, precedence, associativity, mutable-binding, and control-flow boundaries have
runnable frontend-equivalence coverage in
\<open>Parser_Test_Conformance.thy\<close>. The frontend does not provide \<open>/=\<close>;
its fidelity rejection is checked in
\<open>Parser_Test_Negative_Conformance.thy\<close>.
\<close>

subsection\<open>Control Flow - Conditionals\<close>

lemma \<open>undefined = \<lbrakk> if True { return True; } else { return True; } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if \<llangle>True\<rrangle> { let v = 16; return v; } else { 42 } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> ((if True { 0 } else { 1 }, True), if False { (2 as u32, 3 as u32) } else { (4, 5) }) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert!((if False { False } else if True { True } else { False })) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if True { () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some(p) = Some(g) { return; } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some(p) = Some(()) { if True { return; } else { return; } } else { return; } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> ((if True { 0 } else { 1 }, True), False) \<rbrakk>\<close> sorry

subsubsection\<open>Rust-Style Optional Semicolons for Block-Like Statements\<close>

lemma \<open>undefined = \<lbrakk> if True { () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if True { () } else { () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if False { () } else if True { () } else { () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some(_) = Some(()) { () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some(_) = Some(()) { () } else { () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match Some(()) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # []\<rrangle>; for (a, b) in lst { () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = (FunctionBody \<lbrakk> { () } () \<rbrakk>)\<close> sorry
lemma \<open>undefined = \<lbrakk> unsafe { () } () \<rbrakk>\<close> sorry

subsection\<open>Control Flow - If-Let and Let-Else\<close>

lemma \<open>undefined = \<lbrakk> if let Some(_) = Some(()) { () }; () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some(p) = Some(()) { return; } else { return; } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some((a, b)) = Some((\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>)) { assert!(a == \<llangle>1 :: 32 word\<rrangle>); assert!(b == \<llangle>2 :: 32 word\<rrangle>); () } else { () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some(Some(x)) = Some(Some(\<llangle>3 :: 32 word\<rrangle>)) { assert!(x == \<llangle>3 :: 32 word\<rrangle>); () } else { () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Some(p) = Some(g) { return 0; } else { return 2; } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let (a, b) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) { () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let (a, b) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) else { () }; () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let Some((a, b)) = Some((\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>)) else { () }; assert!(a == \<llangle>1 :: 32 word\<rrangle>); assert!(b == \<llangle>2 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = (FunctionBody \<lbrakk> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { assert!(False) }; return; \<rbrakk>)\<close> sorry

context
  fixes n :: \<open>nat option\<close>
begin
lemma \<open>undefined = \<lbrakk> let Some(x) = n else { return \<llangle>5\<rrangle>; }; return x; \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let Ok(k) = Ok(()) else { return; }; return k; \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let Err(e) = Ok(()) else { return True; }; return e; \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>7 :: 32 word\<rrangle>; let b = \<llangle>9 :: 32 word\<rrangle>; let Ok((x, y)) = Ok((a, b)) else { () }; assert!(x == a); assert!(y == b) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let (a,_) = (1,2); let (_,b) = (1,2); \<llangle>(a,b)\<rrangle> \<rbrakk>\<close> sorry

subsection\<open>Control Flow - Match Expressions\<close>

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> match Some(x) { Some(y) \<Rightarrow> { return; }, None \<Rightarrow> { return; } }; \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match Some(x) { None \<Rightarrow> { return; }, Some(y) \<Rightarrow> y }; \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let v = match Err(\<llangle>5 :: 32 word\<rrangle>) { Ok(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>, Err(x) \<Rightarrow> x }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry

subsubsection\<open>Wildcard Patterns\<close>

context
  fixes a :: \<open>nat\<close>
begin
lemma \<open>undefined = \<lbrakk>
  let _ = 3;
  let _ = (if True { False} else {True});
  const _ = { assert!(True); assert!(False); };
  let _ = assert!(let _ = False; if let Some(_) = None { False} else {True});
  match Some(a) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () };
  if let Some(_) = Some(()) { () };
  ()
\<rbrakk>\<close> sorry
end

subsubsection\<open>Variable Binding in Patterns\<close>

lemma \<open>undefined = \<lbrakk> let two = \<llangle>2 :: 32 word\<rrangle>; let res = match Some(Some(two)) { Some(Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == two) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let x = \<llangle>9 :: 32 word\<rrangle>; let y = match x { z \<Rightarrow> z }; assert!(y == x) \<rbrakk>\<close> sorry

subsubsection\<open>Grouped and Irrefutable Patterns\<close>

lemma \<open>undefined = \<lbrakk> let v = match Some(\<llangle>5 :: 32 word\<rrangle>) { (Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let foo = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); let (x, y) = foo; assert!(x == \<llangle>1 :: 32 word\<rrangle>); assert!(y == \<llangle>2 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let x = \<llangle>7 :: 32 word\<rrangle>; if let Some(y) = Some(x) { assert!(y == x); () } else { assert!(False); () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let foo = (\<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>); let (x, y) = foo else { () }; assert!(x == \<llangle>3 :: 32 word\<rrangle>); assert!(y == \<llangle>4 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry

subsubsection\<open>Slice Patterns\<close>

lemma \<open>undefined = \<lbrakk> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let res = match xs { [a, b, c] \<Rightarrow> a + b + c, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>6 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let tag = match xs { [_, _] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>0 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let ys = \<llangle>([] :: 32 word list)\<rrangle>; let tag = match ys { [] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let [a, b] = \<llangle>[7 :: 32 word, 8]\<rrangle> { assert!(a == \<llangle>7 :: 32 word\<rrangle>); assert!(b == \<llangle>8 :: 32 word\<rrangle>); () } else { assert!(False); () } \<rbrakk>\<close> sorry

subsubsection\<open>Extended Rust-Style Pattern Forms\<close>

lemma \<open>undefined = \<lbrakk> let y = match \<llangle>True\<rrangle> { true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, false \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match \<llangle>String.implode ''ok''\<rrangle> { "ok" \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match \<llangle>CHR ''a''\<rrangle> { \<llangle>CHR ''a''\<rrangle> \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { whole @ Some(v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry

text\<open>Rust-style pattern binders \<open>ref p\<close> / \<open>ref mut p\<close> are intentionally unsupported (they clash
with the reference syntax). Borrow patterns \<open>&v\<close> / \<open>& mut v\<close> are frontend-only sugar.\<close>

lemma \<open>undefined = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(&v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(& mut v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..=7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>1 :: nat\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>0 :: nat\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match \<llangle>[7 :: 32 word, 8, 9]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>0 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match Some(Some(True)) { Some(Some(True)) \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let y = match Some(Some(\<llangle>7 :: 32 word\<rrangle>)) { Some(whole @ Some(v)) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry

subsubsection\<open>Nested Patterns\<close>

lemma \<open>undefined = \<lbrakk> let one = \<llangle>1 :: 32 word\<rrangle>; let zero = \<llangle>0 :: 32 word\<rrangle>; assert!((match Some(Some(None)) { Some(None) \<Rightarrow> one, _ \<Rightarrow> zero }) == zero) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match ((a, b), c) { ((x, y), z) \<Rightarrow> (x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c) \<rbrakk>\<close> sorry

subsubsection\<open>Struct fixtures (from the tests theory)\<close>

datatype struct_pattern_fixture = Foo (foo: "32 word") (goo: "32 word") | Other

datatype_record struct_pattern_dr =
  dr_foo :: "32 word"
  dr_goo :: "32 word"

record struct_pattern_rec =
  rec_foo :: "32 word"
  rec_goo :: "32 word"

definition foo_struct_expr_lift where
  "foo_struct_expr_lift \<equiv> lift_fun2 Foo"
micro_rust_notation (call) foo_struct_expr_lift ("Foo")

definition struct_pattern_dr_struct_expr_lift where
  "struct_pattern_dr_struct_expr_lift \<equiv> lift_fun2 make_struct_pattern_dr"
micro_rust_notation (call) struct_pattern_dr_struct_expr_lift ("struct_pattern_dr")

subsubsection\<open>Tuple Patterns in Match\<close>

lemma \<open>undefined = \<lbrakk> match (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) { (a, b) \<Rightarrow> a } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match Some((a, b, c)) { Some((x, _, z)) \<Rightarrow> (x, z), _ \<Rightarrow> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>0 :: 32 word\<rrangle>) }; assert!(res.0 == a); assert!(res.1 == c) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>4 :: 32 word\<rrangle>; let b = \<llangle>8 :: 32 word\<rrangle>; if let Some((_, y)) = Some((a, b)) { assert!(y == b); () } else { () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let d = \<llangle>4 :: 32 word\<rrangle>; let res = match ((a, b), (c, d)) { ((w, x), (y, z)) \<Rightarrow> (w, x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c); assert!(res.3 == d) \<rbrakk>\<close> sorry

subsubsection\<open>Struct Patterns\<close>

lemma \<open>undefined = \<lbrakk> match \<llangle>Foo (1 :: 32 word) 2\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let res = match \<llangle>Foo (3 :: 32 word) 4\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let Foo { foo: p, goo: q } = \<llangle>Foo (5 :: 32 word) 6\<rrangle> { assert!(p == \<llangle>5 :: 32 word\<rrangle>); assert!(q == \<llangle>6 :: 32 word\<rrangle>); () } else { assert!(False); () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let Foo { foo: p, goo: q } = \<llangle>Foo (8 :: 32 word) 9\<rrangle> else { return; }; p + q \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let res = match \<llangle>make_struct_pattern_dr (10 :: 32 word) 11\<rrangle> { struct_pattern_dr { dr_goo: q, dr_foo: p } \<Rightarrow> p + q }; assert!(res == \<llangle>21 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, goo } \<Rightarrow> foo + goo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>46 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, .. } \<Rightarrow> foo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>12 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry

subsubsection\<open>Struct Expressions\<close>

lemma \<open>undefined = \<lbrakk> Foo { foo: \<llangle>1 :: 32 word\<rrangle>, goo: \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> Foo { goo: \<llangle>2 :: 32 word\<rrangle>, foo: \<llangle>1 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> struct_pattern_dr { dr_goo: \<llangle>11 :: 32 word\<rrangle>, dr_foo: \<llangle>10 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> Foo { foo: \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, goo: \<llangle>4 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry

subsubsection\<open>Pattern Guards\<close>

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> match Some(x) { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match Some(x) { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match Some(x) { Some(y) \<Rightarrow> { return; }, None \<Rightarrow> { return; } }; \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let zero = \<llangle>0 :: 32 word\<rrangle>; let one = \<llangle>1 :: 32 word\<rrangle>; let res = match Some(one) { Some(x) if x > zero \<Rightarrow> x, _ \<Rightarrow> zero }; assert!(res == one) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let zero = \<llangle>0 :: 32 word\<rrangle>; let res = match Some(zero) { Some(x) if x > zero \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(x) \<Rightarrow> x, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> }; assert!(res == zero) \<rbrakk>\<close> sorry

subsubsection\<open>Nested Match Expressions\<close>

text\<open>
These tests place nested \<open>match\<close> expressions in arm bodies, scrutinees, guards,
and \<open>let\<close> RHSs; nested patterns are covered separately.
\<close>

datatype nm_case = NmA "32 word" | NmB "32 word" | NmC

\<comment>\<open>Position of the inner match: arm body, scrutinee, let-RHS, guard, sequenced.\<close>
context
  fixes r :: \<open>(32 word option, unit) result\<close>
begin
lemma \<open>undefined = \<lbrakk> match r { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> match (match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }) { z \<Rightarrow> z } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { let t = match Ok(x) { Ok(v) \<Rightarrow> v, Err(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; t }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> match Some(x) { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { match Some(x) { Some(_) \<Rightarrow> (), None \<Rightarrow> () }; match Ok(x) { Ok(_) \<Rightarrow> (), Err(_) \<Rightarrow> () } }, None \<Rightarrow> () } \<rbrakk>\<close> sorry

\<comment>\<open>Nesting depth / breadth: depth-3, depth-4, and inner matches in multiple arms.\<close>
context
  fixes z :: \<open>32 word\<close>
  fixes a3 :: \<open>((32 word option, unit) result, unit) result\<close>
  fixes a4 :: \<open>(((32 word option, unit) result, unit) result, unit) result\<close>
  fixes r2 :: \<open>(32 word option, 32 word option) result\<close>
begin
lemma \<open>undefined = \<lbrakk> match a3 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match a4 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Ok(d) \<Rightarrow> match d { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match r2 { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(e) \<Rightarrow> match e { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } } \<rbrakk>\<close> sorry
end

\<comment>\<open>Interaction with other pattern features:
    nested/constructor, tuple, guard, or-patterns; local datatype; and match_switch both ways.\<close>
lemma \<open>undefined = \<lbrakk> match Some(Some(\<llangle>1 :: 32 word\<rrangle>)) { Some(Some(x)) \<Rightarrow> match Some(x) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry

context
  fixes p q :: \<open>32 word option\<close>
begin
lemma \<open>undefined = \<lbrakk> match (p, q) { (Some(x), qq) \<Rightarrow> match qq { Some(y) \<Rightarrow> x + y, None \<Rightarrow> x }, (None, _) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
end

context
  fixes ov :: \<open>32 word option\<close>
begin
lemma \<open>undefined = \<lbrakk> match ov { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> match Some(y) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> match \<llangle>NmA (1 :: 32 word)\<rrangle> { NmA(n) | NmB(n) \<Rightarrow> match Some(n) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, NmC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match Some(\<llangle>Foo (1 :: 32 word) 2\<rrangle>) { Some(s) \<Rightarrow> match s { Foo { foo: fp, goo: gq } \<Rightarrow> fp + gq, Other \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry

context
  fixes n :: \<open>32 word\<close>
  fixes ov :: \<open>32 word option\<close>
begin
lemma \<open>undefined = \<lbrakk> match ov { Some(x) \<Rightarrow> match_switch x { 0 \<Rightarrow> \<llangle>10 :: 32 word\<rrangle>, _ \<Rightarrow> x }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match_switch n { 0 \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>1 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
end

subsection\<open>Control Flow - Loops\<close>

lemma \<open>undefined = \<lbrakk> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # (3, 4, TNil) # []\<rrangle>; for (a, b) in lst { let _ = a; let _ = b; () }; () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>; for i in lst { if (i.2.0) && i.2.1 { *x = i.0; } else { *x = i.1; } }; x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>(1, 2, (True, False, nil), nil) # (1, 2, (True, False, nil), nil) # []\<rrangle>; for (a, b, (c, d)) in lst { if c && d { x += a; } else { x += b; } }; x \<rbrakk>\<close> sorry

context
  fixes x y :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> for i in x .. y { () } \<rbrakk>\<close> sorry
end

context
  fixes n :: nat
begin
lemma \<open>undefined = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] while (*x < 10_u32) { x += 1_u32; }; *x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] while (*x < 10_u32) { x += 1_u32; } *x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] loop { x += 1_u32; }; *x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] loop { x += 1_u32; } *x \<rbrakk>\<close> sorry
end

subsubsection\<open>While Let\<close>

context
  fixes n :: nat
  fixes g :: \<open>'s\<close>
begin
lemma \<open>undefined = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Some(v) = Some(g) { () }; () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> #[fuel(\<epsilon>\<open>n :: nat\<close>)] while let Some(v) = Some(g) { () } () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Ok(v) = Ok(g) { () }; () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let (a, b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { () }; () \<rbrakk>\<close> sorry
end

subsection\<open>Control Flow - Return\<close>

lemma \<open>undefined = \<lbrakk> return; \<rbrakk>\<close> sorry
lemma \<open>undefined = (FunctionBody \<lbrakk> {return;}; return; \<rbrakk>)\<close> sorry
lemma \<open>undefined = \<lbrakk> let v = \<llangle>42 :: 64 word\<rrangle>; return v; \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let (a,b) = (1,2); return; \<rbrakk>\<close> sorry

definition test :: \<open>(nat, unit, unit, unit, unit) function_body\<close> where
  \<open>test \<equiv> (FunctionBody \<lbrakk> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<rbrakk>)\<close>
hide_const test

lemma \<open>undefined = ((FunctionBody \<lbrakk> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<rbrakk>) :: (nat, unit, unit, unit, unit) function_body)\<close> sorry

context
  fixes x :: \<open>'s\<close>
  fixes g :: \<open>'s \<Rightarrow> ('a, nat option, unit, unit, unit) function_body\<close>
begin
lemma \<open>undefined = \<lbrakk> let blub = 0; if let Some(x) = g(x) { return 0; } else { return 42; }; return 12; \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let x = if True { 0 } else { 1 }; return x; \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let x = (if True { 0 } else { 1 }); return x; \<rbrakk>\<close> sorry

subsection\<open>Control Flow - Error Propagation\<close>

context
  fixes opt :: \<open>nat option\<close>
begin
lemma \<open>undefined = \<lbrakk> opt? \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let x = opt?; x \<rbrakk>\<close> sorry
end

context
  fixes res :: \<open>(nat, bool) result\<close>
begin
lemma \<open>undefined = \<lbrakk> res? \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let x = res?; x \<rbrakk>\<close> sorry
end

subsection\<open>Data Structures - Tuples\<close>

lemma \<open>undefined = \<lbrakk> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> ((False, True), False) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>); assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>); \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let tup = (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>, \<llangle>6 :: 32 word\<rrangle>, \<llangle>7 :: 32 word\<rrangle>, \<llangle>8 :: 32 word\<rrangle>, \<llangle>9 :: 32 word\<rrangle>, \<llangle>10 :: 32 word\<rrangle>, \<llangle>11 :: 32 word\<rrangle>, \<llangle>12 :: 32 word\<rrangle>, \<llangle>13 :: 32 word\<rrangle>, \<llangle>14 :: 32 word\<rrangle>, \<llangle>15 :: 32 word\<rrangle>); assert!(tup.6 == \<llangle>6 :: 32 word\<rrangle>); assert!(tup.10 == \<llangle>10 :: 32 word\<rrangle>); assert!(tup.15 == \<llangle>15 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let c = \<llangle>2 :: 32 word\<rrangle>; let tup = (a, b, c, (False, True)); assert!(tup.3.0 == False); assert!(tup.3.1 == True); \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let tup = (a, (b, a)); let (aaa, (bbb, ccc)) = tup; assert!(aaa == a); assert!(bbb == b); assert!(ccc == a); \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let a = \<llangle>10 :: 32 word\<rrangle>; let b = \<llangle>20 :: 32 word\<rrangle>; let c = \<llangle>30 :: 32 word\<rrangle>; let tup = (a, (b, c)); let (x, (y, z)) = tup; assert!(x == a); assert!(y == b); assert!(z == c) \<rbrakk>\<close> sorry

subsection\<open>Data Structures - Option and Result\<close>

lemma \<open>undefined = \<lbrakk> Some(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> None \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> Ok(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> Err(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close> sorry

subsection\<open>Data Structures - Ranges\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> x..y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> x..=y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let rng = x ..= x+y; rng.is_empty() \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let int_max = \<llangle>255 :: 8 word\<rrangle>; let inclusive = int_max ..= int_max; assert!(!(inclusive.is_empty())); assert!(inclusive.contains(int_max)); let exclusive = int_max .. int_max; assert!(exclusive.is_empty()); () \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let mut count = \<llangle>0 :: 8 word\<rrangle>; let int_max = \<llangle>255 :: 8 word\<rrangle>; for i in int_max ..= int_max { count += \<llangle>1 :: 8 word\<rrangle>; }; assert!(*count == \<llangle>1 :: 8 word\<rrangle>); () \<rbrakk>\<close> sorry

subsection\<open>Functions and Closures\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
  fixes h :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes i :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
begin
lemma \<open>undefined = \<lbrakk> h(a, b, c, a) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> i(a, b, c, a, b) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<epsilon>\<open>g\<close>(c); g(c); f(a,b); a.f(b); f(g(c),b); g(c).f(b) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> f(g(c),b) \<rbrakk>\<close> sorry
end

context
  fixes f14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin
lemma \<open>undefined = \<lbrakk> f14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<rbrakk>\<close> sorry
end

subsubsection\<open>Method-Style Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
begin
lemma \<open>undefined = \<lbrakk> g(c); c.g(); \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> a.f(b) \<rbrakk>\<close> sorry
end

subsubsection\<open>Turbofish Syntax\<close>

context
  fixes f :: \<open>nat \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
lemma \<open>undefined = \<lbrakk> f::<5>() \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> g::<10>(True) \<rbrakk>\<close> sorry
end

subsubsection\<open>Closures\<close>

context
  fixes f :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes h :: \<open>nat \<Rightarrow> (bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body) \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
  fixes n :: \<open>nat\<close>
  fixes x :: \<open>nat\<close>
begin
lemma \<open>undefined = \<lbrakk> || return x; \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> |x| x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> |x, y| { let z = f(x,y); return z; } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<rbrakk>\<close> sorry
end

subsection\<open>References and Mutation\<close>

text\<open>
Mutable allocation, borrow, read-dereference, simple assignment, and binary-operator
preservation have runnable frontend-equivalence coverage in
\<open>Parser_Test_Conformance.thy\<close>.
\<close>

subsection\<open>Field Access and Records\<close>

datatype_record testrec =
  field1 :: integer
  field2 :: bool
micro_rust_record testrec

datatype_record testrec2 =
  field3 :: testrec
  field4 :: \<open>bool option\<close>
micro_rust_record testrec2

context
  fixes x :: testrec
  fixes y :: testrec2
begin
lemma \<open>undefined = \<lbrakk> x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> x.field1 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> y.field4 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> y.field3.field1 \<rbrakk>\<close> sorry
end

subsubsection\<open>Declaring micro_rust_records in locales\<close>

locale micro_rust_record_locale_test =
  fixes answer :: \<open>64 word\<close>
  assumes \<open>answer = 42\<close>
begin
datatype_record foobar =
  field5 :: \<open>64 word\<close>
  field6 :: \<open>64 word\<close>
micro_rust_record foobar
lemma \<open>undefined = (\<lambda> x :: foobar. \<lbrakk> x.field5 + x.field6 \<rbrakk>)\<close> sorry
lemma \<open>undefined = (\<lambda> x :: ('addr, 'fv, foobar) ref. \<lbrakk> *x.field5 + *x.field6 \<rbrakk>)\<close> sorry
end

subsubsection\<open>Field Assignment Through Lenses\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
  fixes s :: \<open>('s, 'b, testrec2) Global_Store.ref\<close>
  fixes f :: \<open>('s, 'b, integer) Global_Store.ref \<Rightarrow> integer \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
begin
private definition dummy_dereference_field :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_field \<equiv> undefined\<close>
adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_field
lemma \<open>undefined = \<lbrakk> r.f(10) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> *(s. field3_lens) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> (*s). field3_lens \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> *r \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> *(s.field4_lens) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> (*s).field4_lens \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> s.field3_lens \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> s.field3_lens.field2_lens \<rbrakk>\<close> sorry
no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_field
end

subsubsection\<open>Custom uRust Field Names\<close>

datatype_record bounds_rec =
  bounds_rec_lo :: \<open>64 word\<close>
  bounds_rec_hi :: \<open>64 word\<close>
  bounds_rec_flag :: bool
micro_rust_record bounds_rec
  (bounds_rec_lo = "lo",
   bounds_rec_hi = "end",
   bounds_rec_flag = "flag")

context
  fixes m :: bounds_rec
begin
lemma \<open>undefined = \<lbrakk> m.lo \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> m.end \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> m.flag \<rbrakk>\<close> sorry
lemma \<open>\<lbrakk> m.lo \<rbrakk>   = \<lbrakk> m.bounds_rec_bounds_rec_lo_lens \<rbrakk>\<close>   by (rule refl)
lemma \<open>\<lbrakk> m.end \<rbrakk>  = \<lbrakk> m.bounds_rec_bounds_rec_hi_lens \<rbrakk>\<close>   by (rule refl)
lemma \<open>\<lbrakk> m.flag \<rbrakk> = \<lbrakk> m.bounds_rec_bounds_rec_flag_lens \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Partial uRust Field-Name Overrides\<close>

datatype_record partial_override_rec =
  por_renamed :: \<open>32 word\<close>
  por_kept    :: \<open>32 word\<close>
micro_rust_record partial_override_rec
  (por_renamed = "renamed")

context
  fixes p :: partial_override_rec
begin
lemma \<open>undefined = \<lbrakk> p.renamed \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> p.por_kept \<rbrakk>\<close> sorry
end

subsubsection\<open>Default Registration (no mapping)\<close>

datatype_record no_override_rec =
  nor_a :: \<open>32 word\<close>
  nor_b :: bool
micro_rust_record no_override_rec

context
  fixes n :: no_override_rec
begin
lemma \<open>undefined = \<lbrakk> n.nor_a \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> n.nor_b \<rbrakk>\<close> sorry
end

subsubsection\<open>Custom Names on Nested Records\<close>

datatype_record inner_named =
  inner_named_value :: \<open>32 word\<close>
micro_rust_record inner_named (inner_named_value = "value")

datatype_record outer_named =
  outer_named_inner :: inner_named
  outer_named_flag  :: bool
micro_rust_record outer_named
  (outer_named_inner = "inner",
   outer_named_flag  = "flag")

context
  fixes ob :: outer_named
begin
lemma \<open>undefined = \<lbrakk> ob.inner \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> ob.flag \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> ob.inner.value \<rbrakk>\<close> sorry
end

subsubsection\<open>Custom Names in a Locale\<close>

locale micro_rust_record_override_locale_test =
  fixes answer :: \<open>64 word\<close>
  assumes \<open>answer = 42\<close>
begin
datatype_record loc_named =
  loc_named_lo :: \<open>64 word\<close>
  loc_named_hi :: \<open>64 word\<close>
micro_rust_record loc_named
  (loc_named_lo = "lo",
   loc_named_hi = "hi")
lemma \<open>undefined = (\<lambda> x :: loc_named. \<lbrakk> x.lo + x.hi \<rbrakk>)\<close> sorry
lemma \<open>undefined = (\<lambda> x :: ('addr, 'fv, loc_named) ref. \<lbrakk> *x.lo + *x.hi \<rbrakk>)\<close> sorry
end

subsection\<open>Macros\<close>

text\<open>
All rows in this subsection whose only previously missing surface was a legacy
\<open>!\<close> macro are promoted to plain-\<open>refl\<close> checked rows in
\<open>Parser_Test_Conformance.thy\<close>. The two rows containing \<open>as\<close> remain
golden stubs because casts are still deferred; their surrounding assertion
syntax is covered independently. Legacy format operands after the first message
are intentionally parsed and discarded, exactly as in the frontend.
\<close>

context
  fixes b :: \<open>bool\<close>
  fixes o :: \<open>nat option\<close>
  fixes a_value :: \<open>32 word\<close>
  fixes x y :: \<open>nat\<close>
begin
lemma \<open>undefined = \<lbrakk> assert!( b ) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> debug_assert!( b ) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert!(!o.is_none()) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert!(b); a_value as u16\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert!(a_value as usize == a_value as usize); a_value as u16\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert_eq!(x, y) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert_ne!(x, y) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert!(b, "ignored assertion message") \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> debug_assert!(b, "ignored debug assertion message", x) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert_eq!(x, y, "ignored assert_eq message", x) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> assert_ne!(x, y, "ignored assert_ne message", y) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> debug_assert_eq!(x, y, "ignored debug_assert_eq message") \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> debug_assert_ne!(x, y, "ignored debug_assert_ne message") \<rbrakk>\<close> sorry
end

context
  fixes msg :: \<open>String.literal\<close>
  and idx :: \<open>32 word\<close>
  and r :: \<open>('a, 'b, 'v) ref\<close>
  and nm :: \<open>String.literal\<close>
begin
lemma \<open>undefined = \<lbrakk> panic!(msg) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> fatal!(msg) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unimplemented!("some_fun") \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unimplemented!(nm) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> todo!("oh no!") \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> fatal!("yikes!") \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> fatal!( \<llangle>''yikes!''\<rrangle> ) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> panic!() \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unimplemented!() \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> todo!() \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> fatal!() \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> panic!("first", msg) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unimplemented!("first", msg) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> todo!("first", msg) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> fatal!("first", msg) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unreachable!() \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unreachable!("should not reach here") \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unreachable!("bad state: {}", msg) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> panic!("Invalid index: {}", idx) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> unimplemented!("not done: {} {}", idx, idx) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> todo!("implement: {}", idx) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> addr_of!(r) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> addr_of_mut!(r) \<rbrakk>\<close> sorry
end

subsubsection\<open>Logging\<close>

text\<open>
Logging remains deferred: \<open>\<l>\<o>\<g>\<close> and log-data syntax are not legacy
bang macros and are not promoted by this increment.
\<close>

context
  fixes b :: \<open>bool\<close>
begin
lemma \<open>undefined = \<lbrakk> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<rbrakk>\<close> sorry
end

subsection\<open>Miscellaneous Features\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
lemma \<open>undefined = \<lbrakk> unsafe { panic!("msg") } \<rbrakk>\<close> sorry
end

subsubsection\<open>Array and Slice Expression Literals\<close>

lemma \<open>undefined = \<lbrakk> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> &[\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> & mut [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> & mut [] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> [\<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let xs = [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>]; assert!(xs[0] == \<llangle>1 :: 32 word\<rrangle>); assert!(xs[2] == \<llangle>3 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let xs = &[\<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>]; let s = match xs { [a, b] \<Rightarrow> a + b, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(s == \<llangle>9 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry

subsubsection\<open>Vec Macro\<close>

text\<open>
These rows are promoted in \<open>Parser_Test_Conformance.thy\<close>, including empty,
nested, indexed, parenthesized, and borrow-interaction variants.
\<close>

lemma \<open>undefined = \<lbrakk> vec![\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> vec![] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let xs = vec![\<llangle>10 :: 32 word\<rrangle>, \<llangle>20 :: 32 word\<rrangle>]; assert!(xs[0] == \<llangle>10 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry

subsubsection\<open>Matches Macro\<close>

text\<open>
These rows are promoted to checked parity tests together with constructor,
nested, alias, slice, struct, or-pattern, outer-capture, and single-evaluation
coverage. Frontend-rejected wildcard, binder, range, bracket, and malformed
forms are pinned in \<open>Parser_Test_Negative_Conformance.thy\<close>.
\<close>

context
  fixes x :: \<open>nat option\<close>
  and y :: \<open>bool option\<close>
begin
lemma \<open>undefined = \<lbrakk> matches!(x, Some(_)) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> matches!(x, None) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> matches!(y, Some(true) | None) \<rbrakk>\<close> sorry
end

subsubsection\<open>Indexing\<close>

context
  fixes xs :: \<open>nat list\<close>
  fixes xss :: \<open>nat list list\<close>
begin
lemma \<open>undefined = \<lbrakk> xs [0..100][42] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> xss[10] \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> xss[10][100] \<rbrakk>\<close> sorry
end

subsubsection\<open>Const Bindings\<close>

lemma \<open>undefined = \<lbrakk> const FOO = 5; () \<rbrakk>\<close> sorry

subsubsection\<open>Scoping and Block Expressions\<close>

context
  fixes x :: \<open>'s\<close>
begin
lemma \<open>undefined = (\<lbrakk> 1 \<rbrakk> :: ('s, nat, 'r, 'abort, 'i, 'o) expression)\<close> sorry
end

subsubsection\<open>Sequencing\<close>

lemma \<open>undefined = \<lbrakk> let a = 1; let b = 2; a \<rbrakk>\<close> sorry

subsection\<open>Rust Path Expressions\<close>

experiment
begin

definition number_42 :: nat where \<open>number_42 \<equiv> 42\<close>
micro_rust_notation (literal) number_42 ("foo::bar::test1")
micro_rust_notation (literal) number_42 ("foo::bar::test2")
micro_rust_notation (literal) True ("foo::bar::test3")

definition \<open>the_record \<equiv> make_testrec 1 False\<close>
micro_rust_notation (literal) the_record ("the::record")

lemma \<open>undefined = \<lbrakk>the::record\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk>(the::record).field1\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk>the::record.field1\<rbrakk>\<close> sorry

lemma \<open>undefined = \<lbrakk> foo::bar::test1 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> foo::bar:: test2 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> foo:: bar::test3 \<rbrakk>\<close> sorry

datatype pe_test =
    Test1
  | Test2

micro_rust_notation (literal) pe_test.Test1 ("test::Test_1")
micro_rust_notation (literal) pe_test.Test2 ("test::Test_2")

definition plus_two :: \<open>'l::len word \<Rightarrow> 'l word\<close> where \<open>plus_two n \<equiv> n + 2\<close>
definition \<open>plus_two_lift \<equiv> lift_fun1 plus_two\<close>

micro_rust_notation (call)    plus_two_lift ("plus2::lifted")
micro_rust_notation (literal) plus_two_lift ("plus2::lifted")

definition three :: \<open>64 word\<close> where \<open>three = 3\<close>
micro_rust_notation (literal) three ("number::three")

lemma \<open>undefined = \<lbrakk> test::Test_1 \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk>plus2::lifted(three)\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk>plus_two_lift(three)\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk>
  let arg = test::Test_1;
  let fun = plus2::lifted;
  match arg { test::Test_1 \<Rightarrow> fun(three), test::Test_2 \<Rightarrow> plus2::lifted(three) }
\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk>
  let x = 5;
  match x { 2 \<Rightarrow> False, number::three \<Rightarrow> False, 0 \<Rightarrow> False, 1 \<Rightarrow> False, _ \<Rightarrow> True }
\<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk>
  let x = 5;
  match_switch x { number::three \<Rightarrow> False, _ \<Rightarrow> True }
\<rbrakk>\<close> sorry

end

subsection\<open>Disjunctive Patterns\<close>

datatype three_case = CaseA nat | CaseB nat | CaseC

lemma \<open>undefined = \<lbrakk> match Some(\<llangle>42 :: nat\<rrangle>) { Some(x) | None \<Rightarrow> x } \<rbrakk>\<close> sorry

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open>undefined = \<lbrakk> match_switch x { 1 | 2 | 3 \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk>\<close> sorry
end

context
  fixes x :: \<open>32 word option\<close>
begin
lemma \<open>undefined = \<lbrakk> match x { Some(y) | None if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> if let CaseA(x) | CaseB(x) = \<llangle>CaseA 42\<rrangle> { () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> if let CaseA(x) | CaseB(x) = \<llangle>CaseA 5\<rrangle> { assert!(x == \<llangle>5 :: nat\<rrangle>); () } else { () } \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let CaseA(x) | CaseB(x) = \<llangle>CaseA 7\<rrangle> else { return; }; x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let CaseA(x) | CaseB(x) = \<llangle>CaseB 10\<rrangle> else { () }; assert!(x == \<llangle>10 :: nat\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match Some(Ok(\<llangle>1 :: nat\<rrangle>)) { Some(Ok(x) | Err(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<rbrakk>\<close> sorry

context
  fixes x :: \<open>64 word\<close>
begin
lemma \<open>undefined = \<lbrakk> match_switch x { 0 | 1 \<Rightarrow> False, _ \<Rightarrow> True } \<rbrakk>\<close> sorry
end

lemma \<open>undefined = \<lbrakk> let res = match Ok(\<llangle>10 :: 32 word\<rrangle>) { Ok(x) | Err(x) \<Rightarrow> x }; assert!(res == \<llangle>10 :: 32 word\<rrangle>) \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> match (Some(\<llangle>1 :: nat\<rrangle>), Some(\<llangle>2 :: nat\<rrangle>)) { (Some(x), Some(y)) | (None, Some(y)) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<rbrakk>\<close> sorry

subsection\<open>Mutable Pattern Destructuring\<close>

lemma \<open>undefined = \<lbrakk> let mut (x, y) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); x + y \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> let mut (a, b, c) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>); a \<rbrakk>\<close> sorry


section\<open> Definition goldens \<close>

subsection\<open>Function-definition tier — Rust fn \<rightarrow> Isabelle definition + FunctionBody\<close>

text\<open>
The HOL type and parameter binding encode the signature; only the body is embedded in
\<open>FunctionBody \<lbrakk>\<dots>\<rbrakk>\<close>. Future item parsing must reproduce each definition.
\<close>

\<comment>\<open>rust:  fn answer() -> u32 { 42 }\<close>
definition answer :: \<open>('s, 32 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>answer \<equiv> FunctionBody \<lbrakk> \<llangle>42 :: 32 word\<rrangle> \<rbrakk>\<close>

\<comment>\<open>rust:  fn inc(x: u32) -> u32 { x + 1 }\<close>
definition inc :: \<open>32 word \<Rightarrow> ('s, 32 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>inc x \<equiv> FunctionBody \<lbrakk> x + \<llangle>1 :: 32 word\<rrangle> \<rbrakk>\<close>

\<comment>\<open>rust:  fn add3(a: u32, b: u32, c: u32) -> u32 { a + b + c }\<close>
definition add3 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>add3 a b c \<equiv> FunctionBody \<lbrakk> a + b + c \<rbrakk>\<close>

\<comment>\<open>rust:  fn is_zero(x: u32) -> bool { x == 0 }\<close>
definition is_zero :: \<open>32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>is_zero x \<equiv> FunctionBody \<lbrakk> x == \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>

\<comment>\<open>rust:  fn safe_div(a: u32, b: u32) -> Result<u32,()> { if b == 0 { Err(()) } else { Ok(a / b) } }\<close>
definition safe_div :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, (32 word, unit) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>safe_div a b \<equiv> FunctionBody \<lbrakk> if b == \<llangle>0 :: 32 word\<rrangle> { Err(()) } else { Ok(a / b) } \<rbrakk>\<close>

subsection\<open>Record-definition tier — Rust struct \<rightarrow> datatype_record + micro_rust_record\<close>

text\<open>
A Rust \<open>struct\<close> maps to \<open>datatype_record\<close> plus \<open>micro_rust_record\<close>,
which generates lenses and registers bare Rust field names. Overrides map prefixed HOL
fields to those names; field-access stubs test resolution.
\<close>

\<comment>\<open>rust:  struct Point { x: u32, y: u32 }\<close>
datatype_record point =
  point_x :: \<open>32 word\<close>
  point_y :: \<open>32 word\<close>
micro_rust_record point (point_x = "x", point_y = "y")

\<comment>\<open>rust:  struct Flags { bits: u8, enabled: bool }\<close>
datatype_record flags =
  flags_bits :: \<open>8 word\<close>
  flags_enabled :: bool
micro_rust_record flags (flags_bits = "bits", flags_enabled = "enabled")

\<comment>\<open>rust:  struct Wrapper { value: Option<u32> }\<close>
datatype_record wrapper =
  wrapper_value :: \<open>32 word option\<close>
micro_rust_record wrapper (wrapper_value = "value")

\<comment>\<open>rust:  struct Line { from: Point, to: Point }\<close>
datatype_record line =
  line_from :: point
  line_to :: point
micro_rust_record line (line_from = "from", line_to = "to")

context fixes p :: point begin
lemma \<open>undefined = \<lbrakk> p.x \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> p.y \<rbrakk>\<close> sorry
end

context fixes fl :: flags begin
lemma \<open>undefined = \<lbrakk> fl.bits \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> fl.enabled \<rbrakk>\<close> sorry
end

context fixes w :: wrapper begin
lemma \<open>undefined = \<lbrakk> w.value \<rbrakk>\<close> sorry
end

context fixes ln :: line begin
lemma \<open>undefined = \<lbrakk> ln.from \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> ln.to \<rbrakk>\<close> sorry
lemma \<open>undefined = \<lbrakk> ln.from.x \<rbrakk>\<close> sorry
end

subsection\<open>Enum-definition tier — Rust enum \<rightarrow> datatype + micro_rust_notation\<close>

text\<open>
A Rust \<open>enum\<close> maps to a HOL \<open>datatype\<close> with one
\<open>micro_rust_notation\<close> registration per path-qualified variant. Stubs cover
construction and matching.
\<close>

\<comment>\<open>rust:  enum Color { Red, Green, Blue }\<close>
datatype color = Red | Green | Blue
micro_rust_notation (literal) color.Red   ("Color::Red")
micro_rust_notation (literal) color.Green ("Color::Green")
micro_rust_notation (literal) color.Blue  ("Color::Blue")

lemma \<open>undefined = \<lbrakk> Color::Red \<rbrakk>\<close> sorry

context fixes c :: color begin
lemma \<open>undefined = \<lbrakk>
  match c { Color::Red \<Rightarrow> \<llangle>0 :: nat\<rrangle>, Color::Green \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Color::Blue \<Rightarrow> \<llangle>2 :: nat\<rrangle> }
\<rbrakk>\<close> sorry
end

section\<open> Frontend rejections \<close>

ML\<open>
  \<comment>\<open>\<open>src\<close> must fail to elaborate through the current frontend.\<close>
  fun rejected src =
    (case Exn.capture (fn () => Syntax.read_term \<^context> src) () of
        Exn.Res _ => false
      | Exn.Exn _ => true);

  val _ = \<^assert> (rejected "\<lbrakk> 1 + \<rbrakk>");
  val _ = \<^assert> (rejected "\<lbrakk> if True \<rbrakk>");
  val _ = \<^assert> (rejected "\<lbrakk> let x = \<rbrakk>");
  val _ = \<^assert> (rejected "\<lbrakk> {} \<rbrakk>");
  \<comment>\<open>Comparisons are non-associative (infix 44): chaining them is a syntax error.\<close>
  val _ = \<^assert> (rejected "\<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<rbrakk>");
\<close>

end
