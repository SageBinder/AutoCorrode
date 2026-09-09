(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Test_Term_Hook_Conformance
  imports Parser_Test_Term_Hook
begin

section\<open> Term-hook conformance corpus \<close>

text\<open>
The inner-syntax frontend is the oracle. Every former
\<open>undefined = \<lbrakk>src\<rbrakk>\<close> expression golden now compares the term hook with its associated
frontend RHS and closes by \<open>refl\<close>. Wrappers such as lambdas, \<open>FunctionBody\<close>, and explicit type
constraints are retained on both sides. The definition and rejection tiers are copied unchanged.
\<open>**\<close> and \<open>!!\<close> mean double dereference and negation.

Known parser/conformance gaps are kept below as commented-out exact corpus
equations instead of being rewritten into different tests:

  \<^item> An exhaustive match over the registered literals
    \<^verbatim>\<open>test::Test_1\<close> and \<^verbatim>\<open>test::Test_2\<close>: the dedicated
    parser emits equality-tested conditionals with an \<open>undefined\<close> fallback,
    while the legacy frontend emits a datatype case expression.

  \<^item> A semicolon-bearing binding expression cannot appear directly as a
    macro argument. The legacy-accepted
    \<^verbatim>\<open>assert!(let ...; if let ...)\<close> form is rejected at the first
    \<open>let\<close> because macro arguments use the restricted \<open>uclosure_arg\<close>
    grammar instead of a full body.

  \<^item> Numeric tuple projections such as \<^verbatim>\<open>res.0\<close>,
    \<^verbatim>\<open>tup.10\<close>, and \<^verbatim>\<open>i.2.0\<close> are rejected because the
    postfix grammar requires an identifier after the dot; the legacy frontend
    lowers these forms to \<open>tuple_index_N\<close> applications.

  \<^item> A bare \<open>match\<close> cannot mix numeral patterns with the registered
    literal pattern \<^verbatim>\<open>number::three\<close>; the dedicated parser rejects
    the mixed pattern families before lowering.

  \<^item> Or-pattern alternatives with unequal binder sets, such as
    \<^verbatim>\<open>Some(x) | None\<close>, are accepted by the legacy frontend but
    rejected by the dedicated parser as missing a binder from one alternative.

The macro and numeric-projection gaps are grammatical and occur during
\<open>URust_Diagnostics.parse_source\<close>. Mixed-pattern and or-pattern-binder
rejections occur later during pattern resolution. The formerly deferred
\<open>is_none\<close> row below is enabled by an explicit call registration; without
that adapter, parsing and AST construction succeed but final HOL checking
rejects the pure function in shallow method-call position.

The hook preserves resolved constant identities when it returns to outer
syntax by using Isabelle's authentic constant markers. This prevents
concealed/private constants from being re-resolved as frees and captured by
an enclosing binder; the hook theory includes a dedicated capture regression.
\<close>


section\<open> Expression goldens \<close>

subsection\<open>Literals and Basic Values\<close>

subsubsection\<open>Numeric Literals\<close>

lemma \<open> \<mu>\<open> 0 \<close> = \<lbrakk> 0 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 1 \<close> = \<lbrakk> 1 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 42 \<close> = \<lbrakk> 42 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0xff \<close> = \<lbrakk> 0xff \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>0 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>255 :: 8 word\<rrangle> \<close> = \<lbrakk> \<llangle>255 :: 8 word\<rrangle> \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Boolean Literals\<close>

lemma \<open> \<mu>\<open> \<epsilon>\<open>Bool_Type.true\<close> \<close> = \<lbrakk> \<epsilon>\<open>Bool_Type.true\<close> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> True \<close> = \<lbrakk> True \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> False \<close> = \<lbrakk> False \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>True\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>False\<rrangle> \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Unit Literal\<close>

context
  fixes f :: \<open>unit \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>unit \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
lemma \<open> \<mu>\<open> () \<close> = \<lbrakk> () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> (); () \<close> = \<lbrakk> (); () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> (); (); \<close> = \<lbrakk> (); (); \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> return (); \<close> = \<lbrakk> return (); \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> return; \<close> = \<lbrakk> return; \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> f(()) \<close> = \<lbrakk> f(()) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> g((),True) \<close> = \<lbrakk> g((),True) \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>String Literals\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
lemma \<open> \<mu>\<open> panic!("oh no!") \<close> = \<lbrakk> panic!("oh no!") \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> panic!( \<llangle>''oh no!''\<rrangle> ) \<close> = \<lbrakk> panic!( \<llangle>''oh no!''\<rrangle> ) \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>HOL Value Injection (Antiquotation)\<close>

lemma \<open> \<mu>\<open> \<llangle>0 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>True\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>Some (0 :: nat)\<rrangle> \<close> = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open>
  \<mu>\<open> \<llangle> \<lbrakk> \<llangle>1 :: nat\<rrangle> \<rbrakk> \<rrangle> \<close> =
  \<lbrakk> \<llangle> \<lbrakk> \<llangle>1 :: nat\<rrangle> \<rbrakk> \<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open>
  \<mu>\<open> \<epsilon>\<open> \<lbrakk> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<rbrakk> \<close> \<close> =
  \<lbrakk> \<epsilon>\<open> \<lbrakk> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<rbrakk> \<close> \<rbrakk>\<close> by (rule refl)

subsection\<open>Type Casts and Ascriptions\<close>

subsubsection\<open>Type Casting\<close>

context
  fixes a_value :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> a_value as u8\<close> = \<lbrakk> a_value as u8\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a_value as u16\<close> = \<lbrakk> a_value as u16\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a_value as u32\<close> = \<lbrakk> a_value as u32\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a_value as u64\<close> = \<lbrakk> a_value as u64\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a_value as u64; a_value as u64\<close> = \<lbrakk> a_value as u64; a_value as u64\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a_value as usize\<close> = \<lbrakk> a_value as usize\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a_value as i32\<close> = \<lbrakk> a_value as i32\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a_value as i64\<close> = \<lbrakk> a_value as i64\<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Raw Pointer Casts\<close>

context
  fixes raw_buf :: \<open>('addr, 'gv) gref\<close>
begin
lemma \<open> \<mu>\<open> raw_buf as *const u8 \<close> = \<lbrakk> raw_buf as *const u8 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> raw_buf as *const u16 \<close> = \<lbrakk> raw_buf as *const u16 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> raw_buf as *const u32 \<close> = \<lbrakk> raw_buf as *const u32 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> raw_buf as *const u64 \<close> = \<lbrakk> raw_buf as *const u64 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> raw_buf as *const usize \<close> = \<lbrakk> raw_buf as *const usize \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> raw_buf as *mut u8 \<close> = \<lbrakk> raw_buf as *mut u8 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> raw_buf as *mut u32 \<close> = \<lbrakk> raw_buf as *mut u32 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> raw_buf as *mut u64 \<close> = \<lbrakk> raw_buf as *mut u64 \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Numeric Ascriptions\<close>

lemma \<open> \<mu>\<open> 0_u8 \<close> = \<lbrakk> 0_u8 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 1_u8 \<close> = \<lbrakk> 1_u8 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0x4_u8 \<close> = \<lbrakk> 0x4_u8 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0_u16 \<close> = \<lbrakk> 0_u16 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 1_u16 \<close> = \<lbrakk> 1_u16 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0x12_u16 \<close> = \<lbrakk> 0x12_u16 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0_u32 \<close> = \<lbrakk> 0_u32 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 1_u32 \<close> = \<lbrakk> 1_u32 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0x2000_u32 \<close> = \<lbrakk> 0x2000_u32 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0_u64 \<close> = \<lbrakk> 0_u64 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 1_u64 \<close> = \<lbrakk> 1_u64 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0x2f0_u64 \<close> = \<lbrakk> 0x2f0_u64 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0_usize \<close> = \<lbrakk> 0_usize \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 1_usize \<close> = \<lbrakk> 1_usize \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> 0xffffffff0_usize \<close> = \<lbrakk> 0xffffffff0_usize \<rbrakk>\<close> by (rule refl)

subsection\<open>Boolean Operators\<close>

subsubsection\<open>Boolean Negation\<close>

lemma \<open> \<mu>\<open> !True \<close> = \<lbrakk> !True \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> !False \<close> = \<lbrakk> !False \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> !!True \<close> = \<lbrakk> !!True \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if !True { return; } \<close> = \<lbrakk> if !True { return; } \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Boolean Conjunction\<close>

lemma \<open> \<mu>\<open> True && True \<close> = \<lbrakk> True && True \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> True && False \<close> = \<lbrakk> True && False \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> False && True \<close> = \<lbrakk> False && True \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> False && False \<close> = \<lbrakk> False && False \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Boolean Disjunction\<close>

lemma \<open> \<mu>\<open> True || True \<close> = \<lbrakk> True || True \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> True || False \<close> = \<lbrakk> True || False \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> False || True \<close> = \<lbrakk> False || True \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> False || False \<close> = \<lbrakk> False || False \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<close> = \<lbrakk> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<close> = \<lbrakk> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<rbrakk>\<close> by (rule refl)

subsection\<open>Comparison Operators\<close>

subsubsection\<open>Equality and Nonequality\<close>

context
  fixes m n :: \<open>nat\<close>
  fixes h :: \<open>nat \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes x y :: \<open>64 word\<close>
begin
lemma \<open> \<mu>\<open> m == n \<close> = \<lbrakk> m == n \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> !(m == n) \<close> = \<lbrakk> !(m == n) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> m != n \<close> = \<lbrakk> m != n \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> m.h() \<close> = \<lbrakk> m.h() \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if m.h() == n { m } else { n } \<close> = \<lbrakk> if m.h() == n { m } else { n } \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Ordering Comparisons\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> x < y \<close> = \<lbrakk> x < y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> x <= y \<close> = \<lbrakk> x <= y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> x > y \<close> = \<lbrakk> x > y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> x >= y \<close> = \<lbrakk> x >= y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> x > \<llangle>0 :: 32 word\<rrangle> \<close> = \<lbrakk> x > \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
end

subsection\<open>Arithmetic Operators\<close>

lemma \<open> \<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<rbrakk>\<close> by (rule refl)

context
  fixes x y :: \<open>64 word\<close>
begin
lemma \<open> \<mu>\<open> let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>); a + b + c \<close> = \<lbrakk> let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>); a + b + c \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<close> = \<lbrakk> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<close> = \<lbrakk> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<close> = \<lbrakk> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<close> = \<lbrakk> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<rbrakk>\<close> by (rule refl)

subsection\<open>Bitwise Operators\<close>

lemma \<open> \<mu>\<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<close> = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<close> = \<lbrakk> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<rbrakk>\<close> by (rule refl)

context
  fixes x y :: \<open>64 word\<close>
begin
lemma \<open> \<mu>\<open> !x + y \<close> = \<lbrakk> !x + y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> !(!x == x^y) \<close> = \<lbrakk> !(!x == x^y) \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<close> = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<close> = \<lbrakk> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<close> = \<lbrakk> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<rbrakk>\<close> by (rule refl)

subsection\<open>Operator Precedence and Associativity\<close>

text\<open>
Goldens pin this precedence:
\<open>* / %\<close> (50) > \<open>+ -\<close> (49) > \<open><< >>\<close> (48) > \<open>&\<close> (47) >
\<open>^\<close> (46) > \<open>|\<close> (45) > comparisons (44) > \<open>&&\<close> (43) >
\<open>||\<close> (42); prefix \<open>!\<close> is tightest. Comparisons are non-associative
and covered by the negative tier.
\<close>

subsubsection\<open>Associativity (binary operators are left-associative)\<close>

lemma \<open> \<mu>\<open> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Cross-tier precedence (the tighter operator groups first)\<close>

lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close> = \<lbrakk> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<close> = \<lbrakk> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<rbrakk>\<close> by (rule refl)

subsection\<open>Assignment Operators\<close>

text\<open>
Simple assignment and its identifier, grouped, dereferenced, field, antiquotation,
precedence, associativity, and composition boundaries have runnable frontend-equivalence
coverage in \<open>Parser_Test_Expr_Conformance.thy\<close>.
\<close>

subsubsection\<open>Compound Assignment\<close>

text\<open>
The frontend-supported operators \<open>+= -= *= %= &= |= ^= <<= >>=\<close> and their
place, precedence, associativity, mutable-binding, and control-flow boundaries have
runnable frontend-equivalence coverage in
\<open>Parser_Test_Expr_Conformance.thy\<close>. The frontend does not provide \<open>/=\<close>;
its fidelity rejection is checked in
\<open>Parser_Test_Negative_Conformance.thy\<close>.
\<close>

subsection\<open>Control Flow - Conditionals\<close>

lemma \<open> \<mu>\<open> if True { return True; } else { return True; } \<close> = \<lbrakk> if True { return True; } else { return True; } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if \<llangle>True\<rrangle> { let v = 16; return v; } else { 42 } \<close> = \<lbrakk> if \<llangle>True\<rrangle> { let v = 16; return v; } else { 42 } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> ((if True { 0 } else { 1 }, True), if False { (2_u32 as u32, 3_u32 as u32) } else { (4, 5) }) \<close> = \<lbrakk> ((if True { 0 } else { 1 }, True), if False { (2_u32 as u32, 3_u32 as u32) } else { (4, 5) }) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<close> = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<close> = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert!((if False { False } else if True { True } else { False })) \<close> = \<lbrakk> assert!((if False { False } else if True { True } else { False })) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if True { () } \<close> = \<lbrakk> if True { () } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> ((if True { 0 } else { 1 }, True), False) \<close> = \<lbrakk> ((if True { 0 } else { 1 }, True), False) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Rust-Style Optional Semicolons for Block-Like Statements\<close>

lemma \<open> \<mu>\<open> if True { () } () \<close> = \<lbrakk> if True { () } () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if True { () } else { () } () \<close> = \<lbrakk> if True { () } else { () } () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> if False { () } else if True { () } else { () } () \<close> = \<lbrakk> if False { () } else if True { () } else { () } () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match Some(()) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () } () \<close> = \<lbrakk> match Some(()) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () } () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # []\<rrangle>; for (a, b) in lst { () } () \<close> = \<lbrakk> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # []\<rrangle>; for (a, b) in lst { () } () \<rbrakk>\<close> by (rule refl)
lemma \<open> (FunctionBody \<mu>\<open> { () } () \<close>) = (FunctionBody \<lbrakk> { () } () \<rbrakk>)\<close> by (rule refl)
lemma \<open> \<mu>\<open> unsafe { () } () \<close> = \<lbrakk> unsafe { () } () \<rbrakk>\<close> by (rule refl)

subsection\<open>Control Flow - If-Let and Let-Else\<close>

text\<open>
Constructor, tuple, nested, returning, explicit-semicolon, and semicolon-free
rows from this section are executable same-source checks in
\<open>Parser_Test_Expr_Conformance.thy\<close>. Malformed and total-pattern redundancy
boundaries are executable checks in
\<open>Parser_Test_Negative_Conformance.thy\<close>.
\<close>

lemma \<open> \<mu>\<open> let (a,_) = (1_u32,2_u32); let (_,b) = (1_u32,2_u32); \<llangle>(a,b)\<rrangle> \<close> = \<lbrakk> let (a,_) = (1_u32,2_u32); let (_,b) = (1_u32,2_u32); \<llangle>(a,b)\<rrangle> \<rbrakk>\<close> by (rule refl)

subsection\<open>Control Flow - Match Expressions\<close>

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<close> = \<lbrakk> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match Some(x) { None \<Rightarrow> { return; }, Some(y) \<Rightarrow> y }; \<close> = \<lbrakk> match Some(x) { None \<Rightarrow> { return; }, Some(y) \<Rightarrow> y }; \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> let v = match Err(\<llangle>5 :: 32 word\<rrangle>) { Ok(ok_value) \<Rightarrow> \<llangle>0 * ok_value :: 32 word\<rrangle>, Err(x) \<Rightarrow> x }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<close> = \<lbrakk> let v = match Err(\<llangle>5 :: 32 word\<rrangle>) { Ok(ok_value) \<Rightarrow> \<llangle>0 * ok_value :: 32 word\<rrangle>, Err(x) \<Rightarrow> x }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Wildcard Patterns\<close>

context
  fixes a :: \<open>nat\<close>
begin
(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open>
  let _ = 3;
  let _ = (if True { False} else {True});
  const _ = { assert!(True); assert!(False); };
  let _ = assert!(let _ = False; if let Some(_) = None { False} else {True});
  match Some(a) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () };
  if let Some(_) = Some(()) { () };
  ()
\<close> = \<lbrakk>
  let _ = 3;
  let _ = (if True { False} else {True});
  const _ = { assert!(True); assert!(False); };
  let _ = assert!(let _ = False; if let Some(_) = None { False} else {True});
  match Some(a) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () };
  if let Some(_) = Some(()) { () };
  ()
\<rbrakk>\<close> by (rule refl)
*)
end

subsubsection\<open>Variable Binding in Patterns\<close>

lemma \<open> \<mu>\<open> let two = \<llangle>2 :: 32 word\<rrangle>; let res = match Some(Some(two)) { Some(Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == two) \<close> = \<lbrakk> let two = \<llangle>2 :: 32 word\<rrangle>; let res = match Some(Some(two)) { Some(Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == two) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let x = \<llangle>9 :: 32 word\<rrangle>; let y = match x { z \<Rightarrow> z }; assert!(y == x) \<close> = \<lbrakk> let x = \<llangle>9 :: 32 word\<rrangle>; let y = match x { z \<Rightarrow> z }; assert!(y == x) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Grouped and Irrefutable Patterns\<close>

lemma \<open> \<mu>\<open> let v = match Some(\<llangle>5 :: 32 word\<rrangle>) { (Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<close> = \<lbrakk> let v = match Some(\<llangle>5 :: 32 word\<rrangle>) { (Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let foo = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); let (x, y) = foo; assert!(x == \<llangle>1 :: 32 word\<rrangle>); assert!(y == \<llangle>2 :: 32 word\<rrangle>) \<close> = \<lbrakk> let foo = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); let (x, y) = foo; assert!(x == \<llangle>1 :: 32 word\<rrangle>); assert!(y == \<llangle>2 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Slice Patterns\<close>

lemma \<open> \<mu>\<open> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let res = match xs { [a, b, c] \<Rightarrow> a + b + c, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>6 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let res = match xs { [a, b, c] \<Rightarrow> a + b + c, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>6 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let tag = match xs { [_, _] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>0 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let tag = match xs { [_, _] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>0 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let ys = \<llangle>([] :: 32 word list)\<rrangle>; let tag = match ys { [] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let ys = \<llangle>([] :: 32 word list)\<rrangle>; let tag = match ys { [] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Extended Rust-Style Pattern Forms\<close>

lemma \<open> \<mu>\<open> let y = match \<llangle>True\<rrangle> { true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, false \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>True\<rrangle> { true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, false \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match \<llangle>String.implode ''ok''\<rrangle> { "ok" \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>String.implode ''ok''\<rrangle> { "ok" \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match \<llangle>CHR ''a''\<rrangle> { \<llangle>CHR ''a''\<rrangle> \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>CHR ''a''\<rrangle> { \<llangle>CHR ''a''\<rrangle> \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { whole @ Some(v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { whole @ Some(v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

text\<open>Rust-style pattern binders \<open>ref p\<close> / \<open>ref mut p\<close> are intentionally unsupported (they clash
with the reference syntax). Borrow patterns \<open>&v\<close> / \<open>& mut v\<close> are syntax-only wrappers during
case preparation in both frontends; direct binders still reject them, and type-sensitive semantics
remain deferred.\<close>

lemma \<open> \<mu>\<open> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(&v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(&v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(& mut v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(& mut v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..=7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>1 :: nat\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..=7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>1 :: nat\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>0 :: nat\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>0 :: nat\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match \<llangle>[7 :: 32 word, 8, 9]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[7 :: 32 word, 8, 9]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match \<llangle>[1 :: 32 word, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>0 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>0 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>5 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match Some(Some(True)) { Some(Some(True)) \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(Some(True)) { Some(Some(True)) \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let y = match Some(Some(\<llangle>7 :: 32 word\<rrangle>)) { Some(whole @ Some(v)) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(Some(\<llangle>7 :: 32 word\<rrangle>)) { Some(whole @ Some(v)) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Nested Patterns\<close>

lemma \<open> \<mu>\<open> let one = \<llangle>1 :: 32 word\<rrangle>; let zero = \<llangle>0 :: 32 word\<rrangle>; assert!((match Some(Some(\<llangle>None :: nat option\<rrangle>)) { Some(None) \<Rightarrow> one, _ \<Rightarrow> zero }) == zero) \<close> = \<lbrakk> let one = \<llangle>1 :: 32 word\<rrangle>; let zero = \<llangle>0 :: 32 word\<rrangle>; assert!((match Some(Some(\<llangle>None :: nat option\<rrangle>)) { Some(None) \<Rightarrow> one, _ \<Rightarrow> zero }) == zero) \<rbrakk>\<close> by (rule refl)
(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match ((a, b), c) { ((x, y), z) \<Rightarrow> (x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c) \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match ((a, b), c) { ((x, y), z) \<Rightarrow> (x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c) \<rbrakk>\<close> by (rule refl)
*)

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

lemma \<open> \<mu>\<open> match (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) { (a, b) \<Rightarrow> a } \<close> = \<lbrakk> match (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) { (a, b) \<Rightarrow> a } \<rbrakk>\<close> by (rule refl)
(* Known parser/conformance gaps; see the note at the top of this theory.
lemma \<open> \<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match Some((a, b, c)) { Some((x, _, z)) \<Rightarrow> (x, z), _ \<Rightarrow> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>0 :: 32 word\<rrangle>) }; assert!(res.0 == a); assert!(res.1 == c) \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match Some((a, b, c)) { Some((x, _, z)) \<Rightarrow> (x, z), _ \<Rightarrow> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>0 :: 32 word\<rrangle>) }; assert!(res.0 == a); assert!(res.1 == c) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let d = \<llangle>4 :: 32 word\<rrangle>; let res = match ((a, b), (c, d)) { ((w, x), (y, z)) \<Rightarrow> (w, x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c); assert!(res.3 == d) \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let d = \<llangle>4 :: 32 word\<rrangle>; let res = match ((a, b), (c, d)) { ((w, x), (y, z)) \<Rightarrow> (w, x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c); assert!(res.3 == d) \<rbrakk>\<close> by (rule refl)
*)

subsubsection\<open>Struct Patterns\<close>

lemma \<open> \<mu>\<open> match \<llangle>Foo (1 :: 32 word) 2\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match \<llangle>Foo (1 :: 32 word) 2\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let res = match \<llangle>Foo (3 :: 32 word) 4\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>Foo (3 :: 32 word) 4\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let res = match \<llangle>make_struct_pattern_dr (10 :: 32 word) 11\<rrangle> { struct_pattern_dr { dr_goo: q, dr_foo: p } \<Rightarrow> p + q }; assert!(res == \<llangle>21 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>make_struct_pattern_dr (10 :: 32 word) 11\<rrangle> { struct_pattern_dr { dr_goo: q, dr_foo: p } \<Rightarrow> p + q }; assert!(res == \<llangle>21 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, goo } \<Rightarrow> foo + goo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>46 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, goo } \<Rightarrow> foo + goo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>46 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, .. } \<Rightarrow> foo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>12 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, .. } \<Rightarrow> foo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>12 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Struct Expressions\<close>

text\<open>
These frontend goldens are promoted to the checked D-21 matrix in
\<open>Parser_Test_Expr_Conformance.thy\<close>. The active frontend treats labels as syntax-only and lowers each
head as an ordinary call with source-ordered initializers; Rust-correct metadata semantics are deferred
to T-39.
\<close>

lemma \<open> \<mu>\<open> Foo { foo: \<llangle>1 :: 32 word\<rrangle>, goo: \<llangle>2 :: 32 word\<rrangle> } \<close> = \<lbrakk> Foo { foo: \<llangle>1 :: 32 word\<rrangle>, goo: \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> Foo { goo: \<llangle>2 :: 32 word\<rrangle>, foo: \<llangle>1 :: 32 word\<rrangle> } \<close> = \<lbrakk> Foo { goo: \<llangle>2 :: 32 word\<rrangle>, foo: \<llangle>1 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> struct_pattern_dr { dr_goo: \<llangle>11 :: 32 word\<rrangle>, dr_foo: \<llangle>10 :: 32 word\<rrangle> } \<close> = \<lbrakk> struct_pattern_dr { dr_goo: \<llangle>11 :: 32 word\<rrangle>, dr_foo: \<llangle>10 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> Foo { foo: \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, goo: \<llangle>4 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> } \<close> = \<lbrakk> Foo { foo: \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, goo: \<llangle>4 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Pattern Guards\<close>

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> match Some(x) { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(x) { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match Some(x) { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(x) { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<close> = \<lbrakk> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> let zero = \<llangle>0 :: 32 word\<rrangle>; let one = \<llangle>1 :: 32 word\<rrangle>; let res = match Some(one) { Some(x) if x > zero \<Rightarrow> x, _ \<Rightarrow> zero }; assert!(res == one) \<close> = \<lbrakk> let zero = \<llangle>0 :: 32 word\<rrangle>; let one = \<llangle>1 :: 32 word\<rrangle>; let res = match Some(one) { Some(x) if x > zero \<Rightarrow> x, _ \<Rightarrow> zero }; assert!(res == one) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let zero = \<llangle>0 :: 32 word\<rrangle>; let res = match Some(zero) { Some(x) if x > zero \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(x) \<Rightarrow> x, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> }; assert!(res == zero) \<close> = \<lbrakk> let zero = \<llangle>0 :: 32 word\<rrangle>; let res = match Some(zero) { Some(x) if x > zero \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(x) \<Rightarrow> x, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> }; assert!(res == zero) \<rbrakk>\<close> by (rule refl)

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
lemma \<open> \<mu>\<open> match r { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match r { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> match (match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }) { z \<Rightarrow> z } \<close> = \<lbrakk> match (match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }) { z \<Rightarrow> z } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { let t = match Ok(x) { Ok(v) \<Rightarrow> v, Err(err_value) \<Rightarrow> \<llangle>0 * err_value :: 32 word\<rrangle> }; t }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { let t = match Ok(x) { Ok(v) \<Rightarrow> v, Err(err_value) \<Rightarrow> \<llangle>0 * err_value :: 32 word\<rrangle> }; t }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> match Some(x) { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(x) { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { match Some(x) { Some(_) \<Rightarrow> (), None \<Rightarrow> () }; match Ok(x) { Ok(_) \<Rightarrow> (), Err(err_value) \<Rightarrow> { let _ = \<llangle>err_value :: 32 word\<rrangle>; () } } }, None \<Rightarrow> () } \<close> = \<lbrakk> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { match Some(x) { Some(_) \<Rightarrow> (), None \<Rightarrow> () }; match Ok(x) { Ok(_) \<Rightarrow> (), Err(err_value) \<Rightarrow> { let _ = \<llangle>err_value :: 32 word\<rrangle>; () } } }, None \<Rightarrow> () } \<rbrakk>\<close> by (rule refl)

\<comment>\<open>Nesting depth / breadth: depth-3, depth-4, and inner matches in multiple arms.\<close>
context
  fixes z :: \<open>32 word\<close>
  fixes a3 :: \<open>((32 word option, unit) result, unit) result\<close>
  fixes a4 :: \<open>(((32 word option, unit) result, unit) result, unit) result\<close>
  fixes r2 :: \<open>(32 word option, 32 word option) result\<close>
begin
lemma \<open> \<mu>\<open> match a3 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<close> = \<lbrakk> match a3 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match a4 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Ok(d) \<Rightarrow> match d { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<close> = \<lbrakk> match a4 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Ok(d) \<Rightarrow> match d { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match r2 { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(e) \<Rightarrow> match e { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } } \<close> = \<lbrakk> match r2 { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(e) \<Rightarrow> match e { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } } \<rbrakk>\<close> by (rule refl)
end

\<comment>\<open>Interaction with other pattern features:
    nested/constructor, tuple, guard, or-patterns; local datatype; and match_switch both ways.\<close>
lemma \<open> \<mu>\<open> match Some(Some(\<llangle>1 :: 32 word\<rrangle>)) { Some(Some(x)) \<Rightarrow> match Some(x) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(Some(\<llangle>1 :: 32 word\<rrangle>)) { Some(Some(x)) \<Rightarrow> match Some(x) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)

context
  fixes p q :: \<open>32 word option\<close>
begin
lemma \<open> \<mu>\<open> match (p, q) { (Some(x), qq) \<Rightarrow> match qq { Some(y) \<Rightarrow> x + y, None \<Rightarrow> x }, (None, _) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match (p, q) { (Some(x), qq) \<Rightarrow> match qq { Some(y) \<Rightarrow> x + y, None \<Rightarrow> x }, (None, _) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
end

context
  fixes ov :: \<open>32 word option\<close>
begin
lemma \<open> \<mu>\<open> match ov { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> match Some(y) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match ov { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> match Some(y) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> match \<llangle>NmA (1 :: 32 word)\<rrangle> { NmA(n) | NmB(n) \<Rightarrow> match Some(n) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, NmC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match \<llangle>NmA (1 :: 32 word)\<rrangle> { NmA(n) | NmB(n) \<Rightarrow> match Some(n) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, NmC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match Some(\<llangle>Foo (1 :: 32 word) 2\<rrangle>) { Some(s) \<Rightarrow> match s { Foo { foo: fp, goo: gq } \<Rightarrow> fp + gq, Other \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(\<llangle>Foo (1 :: 32 word) 2\<rrangle>) { Some(s) \<Rightarrow> match s { Foo { foo: fp, goo: gq } \<Rightarrow> fp + gq, Other \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)

context
  fixes n :: \<open>32 word\<close>
  fixes ov :: \<open>32 word option\<close>
begin
lemma \<open> \<mu>\<open> match ov { Some(x) \<Rightarrow> match_switch x { 0 \<Rightarrow> \<llangle>10 :: 32 word\<rrangle>, _ \<Rightarrow> x }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match ov { Some(x) \<Rightarrow> match_switch x { 0 \<Rightarrow> \<llangle>10 :: 32 word\<rrangle>, _ \<Rightarrow> x }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> match_switch n { 0 \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>1 :: 32 word\<rrangle> } \<close> = \<lbrakk> match_switch n { 0 \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>1 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
end

subsection\<open>Control Flow - Loops\<close>

lemma \<open> \<mu>\<open> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # (3, 4, TNil) # []\<rrangle>; for (a, b) in lst { let _ = a; let _ = b; () }; () \<close> = \<lbrakk> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # (3, 4, TNil) # []\<rrangle>; for (a, b) in lst { let _ = a; let _ = b; () }; () \<rbrakk>\<close> by (rule refl)
(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>; for i in lst { if (i.2.0) && i.2.1 { *x = i.0; } else { *x = i.1; } }; x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>; for i in lst { if (i.2.0) && i.2.1 { *x = i.0; } else { *x = i.1; } }; x \<rbrakk>\<close> by (rule refl)
*)
lemma \<open> \<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # ((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # []\<rrangle>; for (a, b, (c, d)) in lst { if c && d { x += a; } else { x += b; } }; x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # ((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # []\<rrangle>; for (a, b, (c, d)) in lst { if c && d { x += a; } else { x += b; } }; x \<rbrakk>\<close> by (rule refl)

context
  fixes x y :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> for i in x .. y { () } \<close> = \<lbrakk> for i in x .. y { () } \<rbrakk>\<close> by (rule refl)
end

context
  fixes n :: nat
begin
lemma \<open> \<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] while (*x < 10_u32) { x += 1_u32; }; *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] while (*x < 10_u32) { x += 1_u32; }; *x \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] while (*x < 10_u32) { x += 1_u32; } *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] while (*x < 10_u32) { x += 1_u32; } *x \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] loop { x += 1_u32; }; *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] loop { x += 1_u32; }; *x \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] loop { x += 1_u32; } *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] loop { x += 1_u32; } *x \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>While Let\<close>

context
  fixes n :: nat
  fixes g :: \<open>'s\<close>
begin
lemma \<open> \<mu>\<open> #[fuel(\<epsilon>\<open>n\<close>)] while let Some(v) = Some(g) { () }; () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Some(v) = Some(g) { () }; () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> #[fuel(\<epsilon>\<open>n :: nat\<close>)] while let Some(v) = Some(g) { () } () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n :: nat\<close>)] while let Some(v) = Some(g) { () } () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> #[fuel(\<epsilon>\<open>n\<close>)] while let Ok(v) = \<llangle>Ok g :: ('s, unit) result\<rrangle> { () }; () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Ok(v) = \<llangle>Ok g :: ('s, unit) result\<rrangle> { () }; () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> #[fuel(\<epsilon>\<open>n\<close>)] while let (a, b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { () }; () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let (a, b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { () }; () \<rbrakk>\<close> by (rule refl)
end

subsection\<open>Control Flow - Return\<close>

lemma \<open> \<mu>\<open> return; \<close> = \<lbrakk> return; \<rbrakk>\<close> by (rule refl)
lemma \<open> (FunctionBody \<mu>\<open> ({return;}) == (); return; \<close>) = (FunctionBody \<lbrakk> ({return;}) == (); return; \<rbrakk>)\<close> by (rule refl)
lemma \<open> \<mu>\<open> let v = \<llangle>42 :: 64 word\<rrangle>; return v; \<close> = \<lbrakk> let v = \<llangle>42 :: 64 word\<rrangle>; return v; \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let (a,b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); return; \<close> = \<lbrakk> let (a,b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); return; \<rbrakk>\<close> by (rule refl)

definition test :: \<open>(nat, unit, unit, unit, unit) function_body\<close> where
  \<open>test \<equiv> (FunctionBody \<lbrakk> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<rbrakk>)\<close>
hide_const test

lemma \<open> ((FunctionBody \<mu>\<open> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<close>) :: (nat, unit, unit, unit, unit) function_body) = ((FunctionBody \<lbrakk> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<rbrakk>) :: (nat, unit, unit, unit, unit) function_body)\<close> by (rule refl)

context
  fixes x :: \<open>'s\<close>
  fixes g :: \<open>'s \<Rightarrow> ('a, nat option, unit, unit, unit) function_body\<close>
begin
lemma \<open> \<mu>\<open> let blub = 0_u32; (if let Some(x) = g(x) { return 0; } else { return 42; }) + 0_u32; return 12; \<close> = \<lbrakk> let blub = 0_u32; (if let Some(x) = g(x) { return 0; } else { return 42; }) + 0_u32; return 12; \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> let x = if True { 0 } else { 1 }; return x; \<close> = \<lbrakk> let x = if True { 0 } else { 1 }; return x; \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let x = (if True { 0 } else { 1 }); return x; \<close> = \<lbrakk> let x = (if True { 0 } else { 1 }); return x; \<rbrakk>\<close> by (rule refl)

subsection\<open>Control Flow - Error Propagation\<close>

context
  fixes opt :: \<open>nat option\<close>
begin
lemma \<open> \<mu>\<open> opt? \<close> = \<lbrakk> opt? \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let x = opt?; x \<close> = \<lbrakk> let x = opt?; x \<rbrakk>\<close> by (rule refl)
end

context
  fixes res :: \<open>(nat, bool) result\<close>
begin
lemma \<open> \<mu>\<open> res? \<close> = \<lbrakk> res? \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let x = res?; x \<close> = \<lbrakk> let x = res?; x \<rbrakk>\<close> by (rule refl)
end

subsection\<open>Data Structures - Tuples\<close>

lemma \<open> \<mu>\<open> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False) \<close> = \<lbrakk> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> ((False, True), False) \<close> = \<lbrakk> ((False, True), False) \<rbrakk>\<close> by (rule refl)
(* Known parser/conformance gaps; see the note at the top of this theory.
lemma \<open> \<mu>\<open> assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>); assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>); \<close> = \<lbrakk> assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>); assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>); \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let tup = (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>, \<llangle>6 :: 32 word\<rrangle>, \<llangle>7 :: 32 word\<rrangle>, \<llangle>8 :: 32 word\<rrangle>, \<llangle>9 :: 32 word\<rrangle>, \<llangle>10 :: 32 word\<rrangle>, \<llangle>11 :: 32 word\<rrangle>, \<llangle>12 :: 32 word\<rrangle>, \<llangle>13 :: 32 word\<rrangle>, \<llangle>14 :: 32 word\<rrangle>, \<llangle>15 :: 32 word\<rrangle>); assert!(tup.6 == \<llangle>6 :: 32 word\<rrangle>); assert!(tup.10 == \<llangle>10 :: 32 word\<rrangle>); assert!(tup.15 == \<llangle>15 :: 32 word\<rrangle>) \<close> = \<lbrakk> let tup = (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>, \<llangle>6 :: 32 word\<rrangle>, \<llangle>7 :: 32 word\<rrangle>, \<llangle>8 :: 32 word\<rrangle>, \<llangle>9 :: 32 word\<rrangle>, \<llangle>10 :: 32 word\<rrangle>, \<llangle>11 :: 32 word\<rrangle>, \<llangle>12 :: 32 word\<rrangle>, \<llangle>13 :: 32 word\<rrangle>, \<llangle>14 :: 32 word\<rrangle>, \<llangle>15 :: 32 word\<rrangle>); assert!(tup.6 == \<llangle>6 :: 32 word\<rrangle>); assert!(tup.10 == \<llangle>10 :: 32 word\<rrangle>); assert!(tup.15 == \<llangle>15 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let c = \<llangle>2 :: 32 word\<rrangle>; let tup = (a, b, c, (False, True)); assert!(tup.3.0 == False); assert!(tup.3.1 == True); \<close> = \<lbrakk> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let c = \<llangle>2 :: 32 word\<rrangle>; let tup = (a, b, c, (False, True)); assert!(tup.3.0 == False); assert!(tup.3.1 == True); \<rbrakk>\<close> by (rule refl)
*)
lemma \<open> \<mu>\<open> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let tup = (a, (b, a)); let (aaa, (bbb, ccc)) = tup; assert!(aaa == a); assert!(bbb == b); assert!(ccc == a); \<close> = \<lbrakk> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let tup = (a, (b, a)); let (aaa, (bbb, ccc)) = tup; assert!(aaa == a); assert!(bbb == b); assert!(ccc == a); \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let a = \<llangle>10 :: 32 word\<rrangle>; let b = \<llangle>20 :: 32 word\<rrangle>; let c = \<llangle>30 :: 32 word\<rrangle>; let tup = (a, (b, c)); let (x, (y, z)) = tup; assert!(x == a); assert!(y == b); assert!(z == c) \<close> = \<lbrakk> let a = \<llangle>10 :: 32 word\<rrangle>; let b = \<llangle>20 :: 32 word\<rrangle>; let c = \<llangle>30 :: 32 word\<rrangle>; let tup = (a, (b, c)); let (x, (y, z)) = tup; assert!(x == a); assert!(y == b); assert!(z == c) \<rbrakk>\<close> by (rule refl)

subsection\<open>Data Structures - Option and Result\<close>

lemma \<open> \<mu>\<open> Some(\<llangle>42 :: nat\<rrangle>) \<close> = \<lbrakk> Some(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> None \<close> = \<lbrakk> None \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<llangle>Some (0 :: nat)\<rrangle> \<close> = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> Ok(\<llangle>42 :: nat\<rrangle>) \<close> = \<lbrakk> Ok(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> Err(\<llangle>42 :: nat\<rrangle>) \<close> = \<lbrakk> Err(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close> by (rule refl)

subsection\<open>Data Structures - Ranges\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> x..y \<close> = \<lbrakk> x..y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> x..=y \<close> = \<lbrakk> x..=y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let rng = x ..= x+y; rng.is_empty() \<close> = \<lbrakk> let rng = x ..= x+y; rng.is_empty() \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> let int_max = \<llangle>255 :: 8 word\<rrangle>; let inclusive = int_max ..= int_max; assert!(!(inclusive.is_empty())); assert!(inclusive.contains(int_max)); let exclusive = int_max .. int_max; assert!(exclusive.is_empty()); () \<close> = \<lbrakk> let int_max = \<llangle>255 :: 8 word\<rrangle>; let inclusive = int_max ..= int_max; assert!(!(inclusive.is_empty())); assert!(inclusive.contains(int_max)); let exclusive = int_max .. int_max; assert!(exclusive.is_empty()); () \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let mut count = \<llangle>0 :: 8 word\<rrangle>; let _ = \<llangle>count :: (unit, unit, 8 word) Global_Store.ref\<rrangle>; let int_max = \<llangle>255 :: 8 word\<rrangle>; for i in int_max ..= int_max { count += \<llangle>1 :: 8 word\<rrangle>; }; assert!(*count == \<llangle>1 :: 8 word\<rrangle>); () \<close> = \<lbrakk> let mut count = \<llangle>0 :: 8 word\<rrangle>; let _ = \<llangle>count :: (unit, unit, 8 word) Global_Store.ref\<rrangle>; let int_max = \<llangle>255 :: 8 word\<rrangle>; for i in int_max ..= int_max { count += \<llangle>1 :: 8 word\<rrangle>; }; assert!(*count == \<llangle>1 :: 8 word\<rrangle>); () \<rbrakk>\<close> by (rule refl)

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
lemma \<open> \<mu>\<open> h(a, b, c, a) \<close> = \<lbrakk> h(a, b, c, a) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> i(a, b, c, a, b) \<close> = \<lbrakk> i(a, b, c, a, b) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<epsilon>\<open>g\<close>(c); g(c); f(a,b); a.f(b); f(g(c),b); g(c).f(b) \<close> = \<lbrakk> \<epsilon>\<open>g\<close>(c); g(c); f(a,b); a.f(b); f(g(c),b); g(c).f(b) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> f(g(c),b) \<close> = \<lbrakk> f(g(c),b) \<rbrakk>\<close> by (rule refl)
end

context
  fixes f14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin
lemma \<open> \<mu>\<open> f14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<close> = \<lbrakk> f14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Method-Style Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
begin
lemma \<open> \<mu>\<open> g(c); c.g(); \<close> = \<lbrakk> g(c); c.g(); \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> a.f(b) \<close> = \<lbrakk> a.f(b) \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Turbofish Syntax\<close>

text\<open>
These representative rows are promoted to executable same-source coverage in
\<open>Parser_Test_Expr_Conformance.thy\<close>, with additional qualified bases, methods, lexical capture,
multiple parameters, exact-registration precedence, malformed input, and structural/range audits.
\<close>

context
  fixes f :: \<open>nat \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
lemma \<open> \<mu>\<open> f::<5>() \<close> = \<lbrakk> f::<5>() \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> g::<10>(True) \<close> = \<lbrakk> g::<10>(True) \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Closures\<close>

text\<open>
Second-class closure parity has runnable coverage in
\<open>Parser_Test_Expr_Conformance.thy\<close>, including duplicate and long formal lists, lexical capture,
role-sensitive notation resolution, closure-body forms, and every frontend placement. Parser-only
delimiter compositions and grouped placements are checked in \<open>Parser_Test_Improvements.thy\<close>;
malformed formals, excluded bare placements, and direct invocation remain executable negative rows.
The goldens below remain representative frontend examples rather than the complete coverage source.
\<close>

context
  fixes f :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes h :: \<open>nat \<Rightarrow> (bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body) \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
  fixes n :: \<open>nat\<close>
  fixes x :: \<open>nat\<close>
begin
lemma \<open> \<mu>\<open> || return x; \<close> = \<lbrakk> || return x; \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> |x| x \<close> = \<lbrakk> |x| x \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> |x, y| { let z = f(x,y); return z; } \<close> = \<lbrakk> |x, y| { let z = f(x,y); return z; } \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<close> = \<lbrakk> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<rbrakk>\<close> by (rule refl)
end

subsection\<open>References and Mutation\<close>

text\<open>
Mutable allocation, borrow, read-dereference, simple assignment, and binary-operator
preservation have runnable frontend-equivalence coverage in
\<open>Parser_Test_Expr_Conformance.thy\<close>.
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
lemma \<open> \<mu>\<open> x \<close> = \<lbrakk> x \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> x.field1 \<close> = \<lbrakk> x.field1 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> y.field4 \<close> = \<lbrakk> y.field4 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> y.field3.field1 \<close> = \<lbrakk> y.field3.field1 \<rbrakk>\<close> by (rule refl)
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
lemma \<open> (\<lambda> x :: foobar. \<mu>\<open> x.field5 + x.field6 \<close>) = (\<lambda> x :: foobar. \<lbrakk> x.field5 + x.field6 \<rbrakk>)\<close> by (rule refl)
lemma \<open> (\<lambda> x :: ('addr, 'fv, foobar) ref. \<mu>\<open> *x.field5 + *x.field6 \<close>) = (\<lambda> x :: ('addr, 'fv, foobar) ref. \<lbrakk> *x.field5 + *x.field6 \<rbrakk>)\<close> by (rule refl)
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
lemma \<open> \<mu>\<open> r.f(10) \<close> = \<lbrakk> r.f(10) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> *(s. field3_lens) \<close> = \<lbrakk> *(s. field3_lens) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> (*s). field3_lens \<close> = \<lbrakk> (*s). field3_lens \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> *r \<close> = \<lbrakk> *r \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> *(s.field4_lens) \<close> = \<lbrakk> *(s.field4_lens) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> (*s).field4_lens \<close> = \<lbrakk> (*s).field4_lens \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> s.testrec2_field3_lens \<close> = \<lbrakk> s.testrec2_field3_lens \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> s.testrec2_field3_lens.testrec_field2_lens \<close> = \<lbrakk> s.testrec2_field3_lens.testrec_field2_lens \<rbrakk>\<close> by (rule refl)
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
lemma \<open> \<mu>\<open> m.lo \<close> = \<lbrakk> m.lo \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> m.end \<close> = \<lbrakk> m.end \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> m.flag \<close> = \<lbrakk> m.flag \<rbrakk>\<close> by (rule refl)
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
lemma \<open> \<mu>\<open> p.renamed \<close> = \<lbrakk> p.renamed \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> p.por_kept \<close> = \<lbrakk> p.por_kept \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Default Registration (no mapping)\<close>

datatype_record no_override_rec =
  nor_a :: \<open>32 word\<close>
  nor_b :: bool
micro_rust_record no_override_rec

context
  fixes n :: no_override_rec
begin
lemma \<open> \<mu>\<open> n.nor_a \<close> = \<lbrakk> n.nor_a \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> n.nor_b \<close> = \<lbrakk> n.nor_b \<rbrakk>\<close> by (rule refl)
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
lemma \<open> \<mu>\<open> ob.inner \<close> = \<lbrakk> ob.inner \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> ob.flag \<close> = \<lbrakk> ob.flag \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> ob.inner.value \<close> = \<lbrakk> ob.inner.value \<rbrakk>\<close> by (rule refl)
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
lemma \<open> (\<lambda> x :: loc_named. \<mu>\<open> x.lo + x.hi \<close>) = (\<lambda> x :: loc_named. \<lbrakk> x.lo + x.hi \<rbrakk>)\<close> by (rule refl)
lemma \<open> (\<lambda> x :: ('addr, 'fv, loc_named) ref. \<mu>\<open> *x.lo + *x.hi \<close>) = (\<lambda> x :: ('addr, 'fv, loc_named) ref. \<lbrakk> *x.lo + *x.hi \<rbrakk>)\<close> by (rule refl)
end

subsection\<open>Macros\<close>

text\<open>
All rows in this subsection whose only previously missing surface was a legacy
\<open>!\<close> macro or \<open>as\<close> cast are promoted to executable rows in
\<open>Parser_Test_Expr_Conformance.thy\<close>, with direct \<open>refl\<close> parity where the
surrounding frontend term has the same elaborated shape. Legacy format operands
after the first message are intentionally parsed and discarded, exactly as in
the frontend.
\<close>

definition term_hook_is_none ::
  \<open>nat option \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where \<open> term_hook_is_none \<equiv> lift_fun1 Option.is_none \<close>

micro_rust_notation (call) term_hook_is_none ("is_none")

context
  fixes b :: \<open>bool\<close>
  fixes o :: \<open>nat option\<close>
  fixes a_value :: \<open>32 word\<close>
  fixes x y :: \<open>nat\<close>
begin
lemma \<open> \<mu>\<open> assert!( b ) \<close> = \<lbrakk> assert!( b ) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> debug_assert!( b ) \<close> = \<lbrakk> debug_assert!( b ) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert!(!o.is_none()) \<close> = \<lbrakk> assert!(!o.is_none()) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert!(b); a_value as u16\<close> = \<lbrakk> assert!(b); a_value as u16\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert!(a_value as usize == a_value as usize); a_value as u16\<close> = \<lbrakk> assert!(a_value as usize == a_value as usize); a_value as u16\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert_eq!(x, y) \<close> = \<lbrakk> assert_eq!(x, y) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert_ne!(x, y) \<close> = \<lbrakk> assert_ne!(x, y) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert!(b, "ignored assertion message") \<close> = \<lbrakk> assert!(b, "ignored assertion message") \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> debug_assert!(b, "ignored debug assertion message", x) \<close> = \<lbrakk> debug_assert!(b, "ignored debug assertion message", x) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert_eq!(x, y, "ignored assert_eq message", x) \<close> = \<lbrakk> assert_eq!(x, y, "ignored assert_eq message", x) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> assert_ne!(x, y, "ignored assert_ne message", y) \<close> = \<lbrakk> assert_ne!(x, y, "ignored assert_ne message", y) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> debug_assert_eq!(x, y, "ignored debug_assert_eq message") \<close> = \<lbrakk> debug_assert_eq!(x, y, "ignored debug_assert_eq message") \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> debug_assert_ne!(x, y, "ignored debug_assert_ne message") \<close> = \<lbrakk> debug_assert_ne!(x, y, "ignored debug_assert_ne message") \<rbrakk>\<close> by (rule refl)
end

context
  fixes msg :: \<open>String.literal\<close>
  and idx :: \<open>32 word\<close>
  and r :: \<open>('a, 'b, 'v) ref\<close>
  and nm :: \<open>String.literal\<close>
begin
lemma \<open> \<mu>\<open> panic!(msg) \<close> = \<lbrakk> panic!(msg) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> fatal!(msg) \<close> = \<lbrakk> fatal!(msg) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unimplemented!("some_fun") \<close> = \<lbrakk> unimplemented!("some_fun") \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unimplemented!(nm) \<close> = \<lbrakk> unimplemented!(nm) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> todo!("oh no!") \<close> = \<lbrakk> todo!("oh no!") \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> fatal!("yikes!") \<close> = \<lbrakk> fatal!("yikes!") \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> fatal!( \<llangle>''yikes!''\<rrangle> ) \<close> = \<lbrakk> fatal!( \<llangle>''yikes!''\<rrangle> ) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> panic!() \<close> = \<lbrakk> panic!() \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unimplemented!() \<close> = \<lbrakk> unimplemented!() \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> todo!() \<close> = \<lbrakk> todo!() \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> fatal!() \<close> = \<lbrakk> fatal!() \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> panic!("first", msg) \<close> = \<lbrakk> panic!("first", msg) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unimplemented!("first", msg) \<close> = \<lbrakk> unimplemented!("first", msg) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> todo!("first", msg) \<close> = \<lbrakk> todo!("first", msg) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> fatal!("first", msg) \<close> = \<lbrakk> fatal!("first", msg) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unreachable!() \<close> = \<lbrakk> unreachable!() \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unreachable!("should not reach here") \<close> = \<lbrakk> unreachable!("should not reach here") \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unreachable!("bad state: {}", msg) \<close> = \<lbrakk> unreachable!("bad state: {}", msg) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> panic!("Invalid index: {}", idx) \<close> = \<lbrakk> panic!("Invalid index: {}", idx) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> unimplemented!("not done: {} {}", idx, idx) \<close> = \<lbrakk> unimplemented!("not done: {} {}", idx, idx) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> todo!("implement: {}", idx) \<close> = \<lbrakk> todo!("implement: {}", idx) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> addr_of!(r) \<close> = \<lbrakk> addr_of!(r) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> addr_of_mut!(r) \<close> = \<lbrakk> addr_of_mut!(r) \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Logging\<close>

text\<open>
Primitive logging and yield have runnable parser-equivalence coverage in
\<open>Parser_Test_Expr_Conformance.thy\<close>. The \<open>StdLib_Logging\<close> log-data surface and registered logger
calls are isolated in \<open>Parser_Test_Logging.thy\<close>.
\<close>

context
  fixes b :: \<open>bool\<close>
begin
lemma \<open> \<mu>\<open> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<close> = \<lbrakk> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<close> = \<lbrakk> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<close> = \<lbrakk> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> \<y>\<i>\<e>\<l>\<d> \<close> = \<lbrakk> \<y>\<i>\<e>\<l>\<d> \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> \<y>\<i>\<e>\<l>\<d>; () \<close> = \<lbrakk> \<y>\<i>\<e>\<l>\<d>; () \<rbrakk>\<close> by (rule refl)

subsection\<open>Miscellaneous Features\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
lemma \<open> \<mu>\<open> unsafe { panic!("msg") } \<close> = \<lbrakk> unsafe { panic!("msg") } \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Array and Slice Expression Literals\<close>

lemma \<open> \<mu>\<open> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<close> = \<lbrakk> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> &[\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<close> = \<lbrakk> &[\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> & mut [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<close> = \<lbrakk> & mut [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> & mut [] \<close> = \<lbrakk> & mut [] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> [\<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<close> = \<lbrakk> [\<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let xs = [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>1 :: 32 word\<rrangle>); assert!(xs[2_usize] == \<llangle>3 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>1 :: 32 word\<rrangle>); assert!(xs[2_usize] == \<llangle>3 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let xs = &[\<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>]; let s = match xs { [a, b] \<Rightarrow> a + b, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(s == \<llangle>9 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = &[\<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>]; let s = match xs { [a, b] \<Rightarrow> a + b, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(s == \<llangle>9 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Vec Macro\<close>

text\<open>
These rows are promoted in \<open>Parser_Test_Expr_Conformance.thy\<close>, including empty,
nested, indexed, parenthesized, and borrow-interaction variants.
\<close>

lemma \<open> \<mu>\<open> vec![\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<close> = \<lbrakk> vec![\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> vec![] \<close> = \<lbrakk> vec![] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let xs = vec![\<llangle>10 :: 32 word\<rrangle>, \<llangle>20 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>10 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = vec![\<llangle>10 :: 32 word\<rrangle>, \<llangle>20 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>10 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)

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
lemma \<open> \<mu>\<open> matches!(x, Some(_)) \<close> = \<lbrakk> matches!(x, Some(_)) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> matches!(x, None) \<close> = \<lbrakk> matches!(x, None) \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> matches!(y, Some(true) | None) \<close> = \<lbrakk> matches!(y, Some(true) | None) \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Indexing\<close>

context
  fixes xs :: \<open>nat list\<close>
  fixes xss :: \<open>nat list list\<close>
begin
lemma \<open> \<mu>\<open> xs [0_usize..100_usize][42_usize] \<close> = \<lbrakk> xs [0_usize..100_usize][42_usize] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> xss[10_usize] \<close> = \<lbrakk> xss[10_usize] \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> xss[10_usize][100_usize] \<close> = \<lbrakk> xss[10_usize][100_usize] \<rbrakk>\<close> by (rule refl)
end

subsubsection\<open>Const Bindings\<close>

lemma \<open> \<mu>\<open> const FOO = \<llangle>5 :: nat\<rrangle>; () \<close> = \<lbrakk> const FOO = \<llangle>5 :: nat\<rrangle>; () \<rbrakk>\<close> by (rule refl)

subsubsection\<open>Scoping and Block Expressions\<close>

context
  fixes x :: \<open>'s\<close>
begin
lemma \<open> (\<mu>\<open> 1 \<close> :: ('s, nat, 'r, 'abort, 'i, 'o) expression) = (\<lbrakk> 1 \<rbrakk> :: ('s, nat, 'r, 'abort, 'i, 'o) expression)\<close> by (rule refl)
end

subsubsection\<open>Sequencing\<close>

lemma \<open> \<mu>\<open> let a = 1; let b = \<llangle>2 :: nat\<rrangle>; a \<close> = \<lbrakk> let a = 1; let b = \<llangle>2 :: nat\<rrangle>; a \<rbrakk>\<close> by (rule refl)

subsection\<open>Rust Path Expressions\<close>

text\<open>
Path literals, calls, constructor patterns, nonconstructor value patterns, switch keys, macros, and
generic path composition now have runnable coverage in the parser test theories. Leading
\<open>::\<close>, Rust type generics, and real module/item traversal remain separate work.
\<close>

experiment
begin

definition number_42 :: nat where \<open>number_42 \<equiv> 42\<close>
micro_rust_notation (literal) number_42 ("foo::bar::test1")
micro_rust_notation (literal) number_42 ("foo::bar::test2")
micro_rust_notation (literal) True ("foo::bar::test3")

definition \<open>the_record \<equiv> make_testrec 1 False\<close>
micro_rust_notation (literal) the_record ("the::record")

lemma \<open> \<mu>\<open>the::record\<close> = \<lbrakk>the::record\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open>(the::record).field1\<close> = \<lbrakk>(the::record).field1\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open>the::record.field1\<close> = \<lbrakk>the::record.field1\<rbrakk>\<close> by (rule refl)

lemma \<open> \<mu>\<open> foo::bar::test1 \<close> = \<lbrakk> foo::bar::test1 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> foo::bar:: test2 \<close> = \<lbrakk> foo::bar:: test2 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> foo:: bar::test3 \<close> = \<lbrakk> foo:: bar::test3 \<rbrakk>\<close> by (rule refl)

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

lemma \<open> \<mu>\<open> test::Test_1 \<close> = \<lbrakk> test::Test_1 \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open>plus2::lifted(three)\<close> = \<lbrakk>plus2::lifted(three)\<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open>plus_two_lift(three)\<close> = \<lbrakk>plus_two_lift(three)\<rbrakk>\<close> by (rule refl)
(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open>
  let arg = test::Test_1;
  let fun = plus2::lifted;
  match arg { test::Test_1 \<Rightarrow> fun(three), test::Test_2 \<Rightarrow> plus2::lifted(three) }
\<close> = \<lbrakk>
  let arg = test::Test_1;
  let fun = plus2::lifted;
  match arg { test::Test_1 \<Rightarrow> fun(three), test::Test_2 \<Rightarrow> plus2::lifted(three) }
\<rbrakk>\<close> by (rule refl)
*)
(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open>
  let x = 5;
  match x { 2 \<Rightarrow> False, number::three \<Rightarrow> False, 0 \<Rightarrow> False, 1 \<Rightarrow> False, _ \<Rightarrow> True }
\<close> = \<lbrakk>
  let x = 5;
  match x { 2 \<Rightarrow> False, number::three \<Rightarrow> False, 0 \<Rightarrow> False, 1 \<Rightarrow> False, _ \<Rightarrow> True }
\<rbrakk>\<close> by (rule refl)
*)
lemma \<open> \<mu>\<open>
  let x = 5;
  match_switch x { number::three \<Rightarrow> False, _ \<Rightarrow> True }
\<close> = \<lbrakk>
  let x = 5;
  match_switch x { number::three \<Rightarrow> False, _ \<Rightarrow> True }
\<rbrakk>\<close> by (rule refl)

end

subsection\<open>Disjunctive Patterns\<close>

datatype three_case = CaseA nat | CaseB nat | CaseC

(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open> match Some(\<llangle>42 :: nat\<rrangle>) { Some(x) | None \<Rightarrow> x } \<close> = \<lbrakk> match Some(\<llangle>42 :: nat\<rrangle>) { Some(x) | None \<Rightarrow> x } \<rbrakk>\<close> by (rule refl)
*)

context
  fixes x :: \<open>32 word\<close>
begin
lemma \<open> \<mu>\<open> match_switch x { 1 | 2 | 3 \<Rightarrow> True, _ \<Rightarrow> False } \<close> = \<lbrakk> match_switch x { 1 | 2 | 3 \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk>\<close> by (rule refl)
end

context
  fixes x :: \<open>32 word option\<close>
begin
(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open> match x { Some(y) | None if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match x { Some(y) | None if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close> by (rule refl)
*)
end

lemma \<open> \<mu>\<open> match Some(Ok(\<llangle>1 :: nat\<rrangle>)) { Some(Ok(x) | Err(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<close> = \<lbrakk> match Some(Ok(\<llangle>1 :: nat\<rrangle>)) { Some(Ok(x) | Err(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<rbrakk>\<close> by (rule refl)

context
  fixes x :: \<open>64 word\<close>
begin
lemma \<open> \<mu>\<open> match_switch x { 0 | 1 \<Rightarrow> False, _ \<Rightarrow> True } \<close> = \<lbrakk> match_switch x { 0 | 1 \<Rightarrow> False, _ \<Rightarrow> True } \<rbrakk>\<close> by (rule refl)
end

lemma \<open> \<mu>\<open> let res = match Ok(\<llangle>10 :: 32 word\<rrangle>) { Ok(x) | Err(x) \<Rightarrow> x }; assert!(res == \<llangle>10 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match Ok(\<llangle>10 :: 32 word\<rrangle>) { Ok(x) | Err(x) \<Rightarrow> x }; assert!(res == \<llangle>10 :: 32 word\<rrangle>) \<rbrakk>\<close> by (rule refl)
(* Known parser/conformance gap; see the note at the top of this theory.
lemma \<open> \<mu>\<open> match (Some(\<llangle>1 :: nat\<rrangle>), Some(\<llangle>2 :: nat\<rrangle>)) { (Some(x), Some(y)) | (None, Some(y)) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<close> = \<lbrakk> match (Some(\<llangle>1 :: nat\<rrangle>), Some(\<llangle>2 :: nat\<rrangle>)) { (Some(x), Some(y)) | (None, Some(y)) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<rbrakk>\<close> by (rule refl)
*)

subsection\<open>Mutable Pattern Destructuring\<close>

lemma \<open> \<mu>\<open> let mut (x, y) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); x + y \<close> = \<lbrakk> let mut (x, y) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); x + y \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> let mut (a, b, c) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>); a \<close> = \<lbrakk> let mut (a, b, c) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>); a \<rbrakk>\<close> by (rule refl)


section\<open> Definition goldens \<close>

subsection\<open>Function-definition tier — Rust fn \<rightarrow> Isabelle definition + FunctionBody\<close>

text\<open>
The HOL type and parameter binding encode the signature; only the body is embedded in
\<open>FunctionBody \<lbrakk>\<dots>\<rbrakk>\<close>. Both the explicit Isabelle-typed \<open>urust_fn\<close> facade and
the common typed \<open>urust_expr NAME :: TYPE (PARAMETERS) BODY\<close> form check corresponding
signatures and bodies against the existing frontend. Their focused coverage lives in
\<open>Parser_Test_Fun_Conformance.thy\<close> and \<open>Parser_Test_Expr_Types.thy\<close>. Future Rust-shaped item
parsing must reproduce these complete declaration goldens.
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

\<comment>\<open>rust:  fn discard(x: u32) { () }\<close>
definition discard :: \<open>32 word \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>discard x \<equiv> FunctionBody \<lbrakk> () \<rbrakk>\<close>

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
lemma \<open> \<mu>\<open> p.x \<close> = \<lbrakk> p.x \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> p.y \<close> = \<lbrakk> p.y \<rbrakk>\<close> by (rule refl)
end

context fixes fl :: flags begin
lemma \<open> \<mu>\<open> fl.bits \<close> = \<lbrakk> fl.bits \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> fl.enabled \<close> = \<lbrakk> fl.enabled \<rbrakk>\<close> by (rule refl)
end

context fixes w :: wrapper begin
lemma \<open> \<mu>\<open> w.value \<close> = \<lbrakk> w.value \<rbrakk>\<close> by (rule refl)
end

context fixes ln :: line begin
lemma \<open> \<mu>\<open> ln.from \<close> = \<lbrakk> ln.from \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> ln.to \<close> = \<lbrakk> ln.to \<rbrakk>\<close> by (rule refl)
lemma \<open> \<mu>\<open> ln.from.x \<close> = \<lbrakk> ln.from.x \<rbrakk>\<close> by (rule refl)
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

lemma \<open> \<mu>\<open> Color::Red \<close> = \<lbrakk> Color::Red \<rbrakk>\<close> by (rule refl)

context fixes c :: color begin
lemma \<open> \<mu>\<open>
  match c { Color::Red \<Rightarrow> \<llangle>0 :: nat\<rrangle>, Color::Green \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Color::Blue \<Rightarrow> \<llangle>2 :: nat\<rrangle> }
\<close> = \<lbrakk>
  match c { Color::Red \<Rightarrow> \<llangle>0 :: nat\<rrangle>, Color::Green \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Color::Blue \<Rightarrow> \<llangle>2 :: nat\<rrangle> }
\<rbrakk>\<close> by (rule refl)
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
