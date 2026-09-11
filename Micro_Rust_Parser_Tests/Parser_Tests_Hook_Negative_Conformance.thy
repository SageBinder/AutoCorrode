(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Tests_Hook_Negative_Conformance
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Term_Hook
  keywords "hook_rejects" :: thy_decl
begin
ML\<open>
local
  fun reject (index, source) lthy =
    (case Exn.result (Syntax.read_prop lthy) (Input.string_of source) of
       Exn.Res proposition =>
           error
             ("hook negative conformance row " ^
               Value.print_int index ^ " unexpectedly elaborated:\n" ^
               Syntax.string_of_term lthy proposition)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else lthy)

  val arguments =
    Parse.int --
      (Parse.token Parse.cartouche >>
        Parser_Lex_Util.cartouche_source)
in
  val _ =
    Outer_Syntax.local_theory
      \<^command_keyword>\<open>hook_rejects\<close>
      "Require an exact hook-corpus replacement to be rejected"
      (arguments >> reject)
end
\<close>

declare [[urust_term_hook_conformance_check = true]]

section\<open> Hook conformance corpus \<close>

text\<open>
This theory contains the rows from \<open>Conformance_Corpus.thy\<close> whose exact mechanical
replacement of every legacy \<open>\<lbrakk>src\<rbrakk>\<close> embedding by
\<open>\<mu>\<open>src\<close>\<close> is intentionally rejected. Each command checks the complete
original equality in its original declaration or locale context and fails if that direct
replacement ever elaborates.

These are negative conformance cases, not disabled tests. Typical reasons include syntax excluded
from the closed quotation and references that require explicit captures or dependencies.
Accepted direct replacements are tested in \<open>Parser_Tests_Hook_Conformance.thy\<close>.
\<close>

section\<open> Expression goldens \<close>

subsection\<open>Literals and Basic Values\<close>

subsubsection\<open>Numeric Literals\<close>

hook_rejects 5 \<open>\<mu>\<open> \<llangle>0 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 6 \<open>\<mu>\<open> \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close>
hook_rejects 7 \<open>\<mu>\<open> \<llangle>255 :: 8 word\<rrangle> \<close> = \<lbrakk> \<llangle>255 :: 8 word\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Boolean Literals\<close>

hook_rejects 8 \<open>\<mu>\<open> \<epsilon>\<open>Bool_Type.true\<close> \<close> = \<lbrakk> \<epsilon>\<open>Bool_Type.true\<close> \<rbrakk>\<close>
hook_rejects 9 \<open>\<mu>\<open> True \<close> = \<lbrakk> True \<rbrakk>\<close>
hook_rejects 10 \<open>\<mu>\<open> False \<close> = \<lbrakk> False \<rbrakk>\<close>
hook_rejects 11 \<open>\<mu>\<open> \<llangle>True\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close>
hook_rejects 12 \<open>\<mu>\<open> \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>False\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Unit Literal\<close>

context
  fixes f :: \<open>unit \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>unit \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin

hook_rejects 18 \<open>\<mu>\<open> f(()) \<close> = \<lbrakk> f(()) \<rbrakk>\<close>
hook_rejects 19 \<open>\<mu>\<open> g((),True) \<close> = \<lbrakk> g((),True) \<rbrakk>\<close>
end

subsubsection\<open>String Literals\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
hook_rejects 20 \<open>\<mu>\<open> panic!("oh no!") \<close> = \<lbrakk> panic!("oh no!") \<rbrakk>\<close>
hook_rejects 21 \<open>\<mu>\<open> panic!( \<llangle>''oh no!''\<rrangle> ) \<close> = \<lbrakk> panic!( \<llangle>''oh no!''\<rrangle> ) \<rbrakk>\<close>
end

subsubsection\<open>HOL Value Injection (Antiquotation)\<close>

hook_rejects 22 \<open>\<mu>\<open> \<llangle>0 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 23 \<open>\<mu>\<open> \<llangle>True\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close>
hook_rejects 24 \<open>\<mu>\<open> \<llangle>Some (0 :: nat)\<rrangle> \<close> = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close>
hook_rejects 25 \<open>\<mu>\<open> \<llangle> \<mu>\<open> \<llangle>1 :: nat\<rrangle> \<close> \<rrangle> \<close> = \<lbrakk> \<llangle> \<lbrakk> \<llangle>1 :: nat\<rrangle> \<rbrakk> \<rrangle> \<rbrakk>\<close>
hook_rejects 26 \<open>\<mu>\<open> \<epsilon>\<open> \<mu>\<open> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<close> \<close> \<close> = \<lbrakk> \<epsilon>\<open> \<lbrakk> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<rbrakk> \<close> \<rbrakk>\<close>

subsection\<open>Type Casts and Ascriptions\<close>

subsubsection\<open>Type Casting\<close>

context
  fixes a_value :: \<open>32 word\<close>
begin
hook_rejects 27 \<open>\<mu>\<open> a_value as u8\<close> = \<lbrakk> a_value as u8\<rbrakk>\<close>
hook_rejects 28 \<open>\<mu>\<open> a_value as u16\<close> = \<lbrakk> a_value as u16\<rbrakk>\<close>
hook_rejects 29 \<open>\<mu>\<open> a_value as u32\<close> = \<lbrakk> a_value as u32\<rbrakk>\<close>
hook_rejects 30 \<open>\<mu>\<open> a_value as u64\<close> = \<lbrakk> a_value as u64\<rbrakk>\<close>
hook_rejects 31 \<open>\<mu>\<open> a_value as u64; a_value as u64\<close> = \<lbrakk> a_value as u64; a_value as u64\<rbrakk>\<close>
hook_rejects 32 \<open>\<mu>\<open> a_value as usize\<close> = \<lbrakk> a_value as usize\<rbrakk>\<close>
hook_rejects 33 \<open>\<mu>\<open> a_value as i32\<close> = \<lbrakk> a_value as i32\<rbrakk>\<close>
hook_rejects 34 \<open>\<mu>\<open> a_value as i64\<close> = \<lbrakk> a_value as i64\<rbrakk>\<close>
end

subsubsection\<open>Raw Pointer Casts\<close>

context
  fixes raw_buf :: \<open>('addr, 'gv) gref\<close>
begin
hook_rejects 35 \<open>\<mu>\<open> raw_buf as *const u8 \<close> = \<lbrakk> raw_buf as *const u8 \<rbrakk>\<close>
hook_rejects 36 \<open>\<mu>\<open> raw_buf as *const u16 \<close> = \<lbrakk> raw_buf as *const u16 \<rbrakk>\<close>
hook_rejects 37 \<open>\<mu>\<open> raw_buf as *const u32 \<close> = \<lbrakk> raw_buf as *const u32 \<rbrakk>\<close>
hook_rejects 38 \<open>\<mu>\<open> raw_buf as *const u64 \<close> = \<lbrakk> raw_buf as *const u64 \<rbrakk>\<close>
hook_rejects 39 \<open>\<mu>\<open> raw_buf as *const usize \<close> = \<lbrakk> raw_buf as *const usize \<rbrakk>\<close>
hook_rejects 40 \<open>\<mu>\<open> raw_buf as *mut u8 \<close> = \<lbrakk> raw_buf as *mut u8 \<rbrakk>\<close>
hook_rejects 41 \<open>\<mu>\<open> raw_buf as *mut u32 \<close> = \<lbrakk> raw_buf as *mut u32 \<rbrakk>\<close>
hook_rejects 42 \<open>\<mu>\<open> raw_buf as *mut u64 \<close> = \<lbrakk> raw_buf as *mut u64 \<rbrakk>\<close>
end

subsection\<open>Boolean Operators\<close>

subsubsection\<open>Boolean Negation\<close>

hook_rejects 58 \<open>\<mu>\<open> !True \<close> = \<lbrakk> !True \<rbrakk>\<close>
hook_rejects 59 \<open>\<mu>\<open> !False \<close> = \<lbrakk> !False \<rbrakk>\<close>
hook_rejects 60 \<open>\<mu>\<open> !!True \<close> = \<lbrakk> !!True \<rbrakk>\<close>
hook_rejects 61 \<open>\<mu>\<open> if !True { return; } \<close> = \<lbrakk> if !True { return; } \<rbrakk>\<close>

subsubsection\<open>Boolean Conjunction\<close>

hook_rejects 62 \<open>\<mu>\<open> True && True \<close> = \<lbrakk> True && True \<rbrakk>\<close>
hook_rejects 63 \<open>\<mu>\<open> True && False \<close> = \<lbrakk> True && False \<rbrakk>\<close>
hook_rejects 64 \<open>\<mu>\<open> False && True \<close> = \<lbrakk> False && True \<rbrakk>\<close>
hook_rejects 65 \<open>\<mu>\<open> False && False \<close> = \<lbrakk> False && False \<rbrakk>\<close>

subsubsection\<open>Boolean Disjunction\<close>

hook_rejects 66 \<open>\<mu>\<open> True || True \<close> = \<lbrakk> True || True \<rbrakk>\<close>
hook_rejects 67 \<open>\<mu>\<open> True || False \<close> = \<lbrakk> True || False \<rbrakk>\<close>
hook_rejects 68 \<open>\<mu>\<open> False || True \<close> = \<lbrakk> False || True \<rbrakk>\<close>
hook_rejects 69 \<open>\<mu>\<open> False || False \<close> = \<lbrakk> False || False \<rbrakk>\<close>
hook_rejects 70 \<open>\<mu>\<open> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<close> = \<lbrakk> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<rbrakk>\<close>
hook_rejects 71 \<open>\<mu>\<open> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<close> = \<lbrakk> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<rbrakk>\<close>

subsection\<open>Comparison Operators\<close>

subsubsection\<open>Equality and Nonequality\<close>

context
  fixes m n :: \<open>nat\<close>
  fixes h :: \<open>nat \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes x y :: \<open>64 word\<close>
begin
hook_rejects 72 \<open>\<mu>\<open> m == n \<close> = \<lbrakk> m == n \<rbrakk>\<close>
hook_rejects 73 \<open>\<mu>\<open> !(m == n) \<close> = \<lbrakk> !(m == n) \<rbrakk>\<close>
hook_rejects 74 \<open>\<mu>\<open> m != n \<close> = \<lbrakk> m != n \<rbrakk>\<close>
hook_rejects 75 \<open>\<mu>\<open> m.h() \<close> = \<lbrakk> m.h() \<rbrakk>\<close>
hook_rejects 76 \<open>\<mu>\<open> if m.h() == n { m } else { n } \<close> = \<lbrakk> if m.h() == n { m } else { n } \<rbrakk>\<close>
end

subsubsection\<open>Ordering Comparisons\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
hook_rejects 77 \<open>\<mu>\<open> x < y \<close> = \<lbrakk> x < y \<rbrakk>\<close>
hook_rejects 78 \<open>\<mu>\<open> x <= y \<close> = \<lbrakk> x <= y \<rbrakk>\<close>
hook_rejects 79 \<open>\<mu>\<open> x > y \<close> = \<lbrakk> x > y \<rbrakk>\<close>
hook_rejects 80 \<open>\<mu>\<open> x >= y \<close> = \<lbrakk> x >= y \<rbrakk>\<close>
hook_rejects 81 \<open>\<mu>\<open> x > \<llangle>0 :: 32 word\<rrangle> \<close> = \<lbrakk> x > \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
end

subsection\<open>Arithmetic Operators\<close>

hook_rejects 82 \<open>\<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<rbrakk>\<close>

context
  fixes x y :: \<open>64 word\<close>
begin
hook_rejects 83 \<open>\<mu>\<open> let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>); a + b + c \<close> = \<lbrakk> let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>); a + b + c \<rbrakk>\<close>
end

hook_rejects 84 \<open>\<mu>\<open> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<close> = \<lbrakk> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<rbrakk>\<close>
hook_rejects 85 \<open>\<mu>\<open> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<close> = \<lbrakk> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<rbrakk>\<close>
hook_rejects 86 \<open>\<mu>\<open> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<close> = \<lbrakk> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<rbrakk>\<close>
hook_rejects 87 \<open>\<mu>\<open> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<close> = \<lbrakk> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<rbrakk>\<close>

subsection\<open>Bitwise Operators\<close>

hook_rejects 88 \<open>\<mu>\<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<close> = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<rbrakk>\<close>
hook_rejects 89 \<open>\<mu>\<open> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<close> = \<lbrakk> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<rbrakk>\<close>

context
  fixes x y :: \<open>64 word\<close>
begin
hook_rejects 90 \<open>\<mu>\<open> !x + y \<close> = \<lbrakk> !x + y \<rbrakk>\<close>
hook_rejects 91 \<open>\<mu>\<open> !(!x == x^y) \<close> = \<lbrakk> !(!x == x^y) \<rbrakk>\<close>
end

hook_rejects 92 \<open>\<mu>\<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<close> = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<rbrakk>\<close>
hook_rejects 93 \<open>\<mu>\<open> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<close> = \<lbrakk> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<rbrakk>\<close>
hook_rejects 94 \<open>\<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<rbrakk>\<close>
hook_rejects 95 \<open>\<mu>\<open> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<close> = \<lbrakk> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<rbrakk>\<close>

subsection\<open>Operator Precedence and Associativity\<close>

text\<open>
Goldens pin this precedence:
\<open>* / %\<close> (50) > \<open>+ -\<close> (49) > \<open><< >>\<close> (48) > \<open>&\<close> (47) >
\<open>^\<close> (46) > \<open>|\<close> (45) > comparisons (44) > \<open>&&\<close> (43) >
\<open>||\<close> (42); prefix \<open>!\<close> is tightest. Comparisons are non-associative
and covered by the negative tier.
\<close>

subsubsection\<open>Associativity (binary operators are left-associative)\<close>

hook_rejects 96 \<open>\<mu>\<open> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 97 \<open>\<mu>\<open> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 98 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close>
hook_rejects 99 \<open>\<mu>\<open> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close>
hook_rejects 100 \<open>\<mu>\<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Cross-tier precedence (the tighter operator groups first)\<close>

hook_rejects 101 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 102 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close>
hook_rejects 103 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close>
hook_rejects 104 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 105 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 106 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<rbrakk>\<close>
hook_rejects 107 \<open>\<mu>\<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<close> = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<rbrakk>\<close>
hook_rejects 108 \<open>\<mu>\<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close> = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close>
hook_rejects 109 \<open>\<mu>\<open> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close> = \<lbrakk> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk>\<close>
hook_rejects 110 \<open>\<mu>\<open> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<close> = \<lbrakk> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<rbrakk>\<close>

subsection\<open>Control Flow - Conditionals\<close>

hook_rejects 111 \<open>\<mu>\<open> if True { return True; } else { return True; } \<close> = \<lbrakk> if True { return True; } else { return True; } \<rbrakk>\<close>
hook_rejects 112 \<open>\<mu>\<open> if \<llangle>True\<rrangle> { let v = 16; return v; } else { 42 } \<close> = \<lbrakk> if \<llangle>True\<rrangle> { let v = 16; return v; } else { 42 } \<rbrakk>\<close>
hook_rejects 113 \<open>\<mu>\<open> ((if True { 0 } else { 1 }, True), if False { (2_u32 as u32, 3_u32 as u32) } else { (4, 5) }) \<close> = \<lbrakk> ((if True { 0 } else { 1 }, True), if False { (2_u32 as u32, 3_u32 as u32) } else { (4, 5) }) \<rbrakk>\<close>
hook_rejects 114 \<open>\<mu>\<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<close> = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 115 \<open>\<mu>\<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<close> = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 116 \<open>\<mu>\<open> assert!((if False { False } else if True { True } else { False })) \<close> = \<lbrakk> assert!((if False { False } else if True { True } else { False })) \<rbrakk>\<close>
hook_rejects 117 \<open>\<mu>\<open> if True { () } \<close> = \<lbrakk> if True { () } \<rbrakk>\<close>
hook_rejects 118 \<open>\<mu>\<open> ((if True { 0 } else { 1 }, True), False) \<close> = \<lbrakk> ((if True { 0 } else { 1 }, True), False) \<rbrakk>\<close>

subsubsection\<open>Rust-Style Optional Semicolons for Block-Like Statements\<close>

hook_rejects 119 \<open>\<mu>\<open> if True { () } () \<close> = \<lbrakk> if True { () } () \<rbrakk>\<close>
hook_rejects 120 \<open>\<mu>\<open> if True { () } else { () } () \<close> = \<lbrakk> if True { () } else { () } () \<rbrakk>\<close>
hook_rejects 121 \<open>\<mu>\<open> if False { () } else if True { () } else { () } () \<close> = \<lbrakk> if False { () } else if True { () } else { () } () \<rbrakk>\<close>
hook_rejects 122 \<open>\<mu>\<open> match Some(()) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () } () \<close> = \<lbrakk> match Some(()) { Some(_) \<Rightarrow> (), _ \<Rightarrow> () } () \<rbrakk>\<close>
hook_rejects 123 \<open>\<mu>\<open> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # []\<rrangle>; for (a, b) in lst { () } () \<close> = \<lbrakk> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # []\<rrangle>; for (a, b) in lst { () } () \<rbrakk>\<close>

subsection\<open>Control Flow - If-Let and Let-Else\<close>

text\<open>
Constructor, tuple, nested, returning, explicit-semicolon, and semicolon-free
rows from this section are executable same-source checks in
\<open>Parser_Test_Expr_Conformance.thy\<close>. Malformed and total-pattern redundancy
boundaries are executable checks in
\<open>Parser_Tests_Negative_Conformance.thy\<close>.
\<close>

hook_rejects 126 \<open>\<mu>\<open> let (a,_) = (1_u32,2_u32); let (_,b) = (1_u32,2_u32); \<llangle>(a,b)\<rrangle> \<close> = \<lbrakk> let (a,_) = (1_u32,2_u32); let (_,b) = (1_u32,2_u32); \<llangle>(a,b)\<rrangle> \<rbrakk>\<close>

subsection\<open>Control Flow - Match Expressions\<close>

context
  fixes x :: \<open>32 word\<close>
begin
hook_rejects 127 \<open>\<mu>\<open> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<close> = \<lbrakk> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<rbrakk>\<close>
hook_rejects 128 \<open>\<mu>\<open> match Some(x) { None \<Rightarrow> { return; }, Some(y) \<Rightarrow> y }; \<close> = \<lbrakk> match Some(x) { None \<Rightarrow> { return; }, Some(y) \<Rightarrow> y }; \<rbrakk>\<close>
end

hook_rejects 129 \<open>\<mu>\<open> let v = match Err(\<llangle>5 :: 32 word\<rrangle>) { Ok(ok_value) \<Rightarrow> \<llangle>0 * ok_value :: 32 word\<rrangle>, Err(x) \<Rightarrow> x }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<close> = \<lbrakk> let v = match Err(\<llangle>5 :: 32 word\<rrangle>) { Ok(ok_value) \<Rightarrow> \<llangle>0 * ok_value :: 32 word\<rrangle>, Err(x) \<Rightarrow> x }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Wildcard Patterns\<close>

context
  fixes a :: \<open>nat\<close>
begin
hook_rejects 130 \<open>\<mu>\<open>
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
\<rbrakk>\<close>
end

subsubsection\<open>Variable Binding in Patterns\<close>

hook_rejects 131 \<open>\<mu>\<open> let two = \<llangle>2 :: 32 word\<rrangle>; let res = match Some(Some(two)) { Some(Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == two) \<close> = \<lbrakk> let two = \<llangle>2 :: 32 word\<rrangle>; let res = match Some(Some(two)) { Some(Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == two) \<rbrakk>\<close>
hook_rejects 132 \<open>\<mu>\<open> let x = \<llangle>9 :: 32 word\<rrangle>; let y = match x { z \<Rightarrow> z }; assert!(y == x) \<close> = \<lbrakk> let x = \<llangle>9 :: 32 word\<rrangle>; let y = match x { z \<Rightarrow> z }; assert!(y == x) \<rbrakk>\<close>

subsubsection\<open>Grouped and Irrefutable Patterns\<close>

hook_rejects 133 \<open>\<mu>\<open> let v = match Some(\<llangle>5 :: 32 word\<rrangle>) { (Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<close> = \<lbrakk> let v = match Some(\<llangle>5 :: 32 word\<rrangle>) { (Some(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(v == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 134 \<open>\<mu>\<open> let foo = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); let (x, y) = foo; assert!(x == \<llangle>1 :: 32 word\<rrangle>); assert!(y == \<llangle>2 :: 32 word\<rrangle>) \<close> = \<lbrakk> let foo = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); let (x, y) = foo; assert!(x == \<llangle>1 :: 32 word\<rrangle>); assert!(y == \<llangle>2 :: 32 word\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Slice Patterns\<close>

hook_rejects 135 \<open>\<mu>\<open> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let res = match xs { [a, b, c] \<Rightarrow> a + b + c, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>6 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let res = match xs { [a, b, c] \<Rightarrow> a + b + c, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>6 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 136 \<open>\<mu>\<open> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let tag = match xs { [_, _] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>0 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>; let tag = match xs { [_, _] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>0 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 137 \<open>\<mu>\<open> let ys = \<llangle>([] :: 32 word list)\<rrangle>; let tag = match ys { [] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let ys = \<llangle>([] :: 32 word list)\<rrangle>; let tag = match ys { [] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(tag == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Extended Rust-Style Pattern Forms\<close>

hook_rejects 138 \<open>\<mu>\<open> let y = match \<llangle>True\<rrangle> { true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, false \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>True\<rrangle> { true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, false \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 139 \<open>\<mu>\<open> let y = match \<llangle>String.implode ''ok''\<rrangle> { "ok" \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>String.implode ''ok''\<rrangle> { "ok" \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 140 \<open>\<mu>\<open> let y = match \<llangle>CHR ''a''\<rrangle> { \<llangle>CHR ''a''\<rrangle> \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>CHR ''a''\<rrangle> { \<llangle>CHR ''a''\<rrangle> \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 141 \<open>\<mu>\<open> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { whole @ Some(v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { whole @ Some(v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close>

text\<open>Rust-style pattern binders \<open>ref p\<close> / \<open>ref mut p\<close> are intentionally unsupported (they clash
with the reference syntax). Borrow patterns \<open>&v\<close> / \<open>& mut v\<close> are syntax-only wrappers during
case preparation in both frontends; direct binders still reject them, and type-sensitive semantics
remain deferred.\<close>

hook_rejects 142 \<open>\<mu>\<open> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(&v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(&v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 143 \<open>\<mu>\<open> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(& mut v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: 32 word\<rrangle>) { Some(& mut v) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 144 \<open>\<mu>\<open> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..=7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>1 :: nat\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..=7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>1 :: nat\<rrangle>) \<rbrakk>\<close>
hook_rejects 145 \<open>\<mu>\<open> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>0 :: nat\<rrangle>) \<close> = \<lbrakk> let y = match Some(\<llangle>7 :: nat\<rrangle>) { Some(5..7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> }; assert!(y == \<llangle>0 :: nat\<rrangle>) \<rbrakk>\<close>
hook_rejects 146 \<open>\<mu>\<open> let y = match \<llangle>[7 :: 32 word, 8, 9]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[7 :: 32 word, 8, 9]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 147 \<open>\<mu>\<open> let y = match \<llangle>[1 :: 32 word, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 148 \<open>\<mu>\<open> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>0 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>0 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 149 \<open>\<mu>\<open> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>5 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y + z, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>5 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 150 \<open>\<mu>\<open> let y = match Some(Some(True)) { Some(Some(True)) \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(Some(True)) { Some(Some(True)) \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 151 \<open>\<mu>\<open> let y = match Some(Some(\<llangle>7 :: 32 word\<rrangle>)) { Some(whole @ Some(v)) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let y = match Some(Some(\<llangle>7 :: 32 word\<rrangle>)) { Some(whole @ Some(v)) \<Rightarrow> v, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(y == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Nested Patterns\<close>

hook_rejects 152 \<open>\<mu>\<open> let one = \<llangle>1 :: 32 word\<rrangle>; let zero = \<llangle>0 :: 32 word\<rrangle>; assert!((match Some(Some(\<llangle>None :: nat option\<rrangle>)) { Some(None) \<Rightarrow> one, _ \<Rightarrow> zero }) == zero) \<close> = \<lbrakk> let one = \<llangle>1 :: 32 word\<rrangle>; let zero = \<llangle>0 :: 32 word\<rrangle>; assert!((match Some(Some(\<llangle>None :: nat option\<rrangle>)) { Some(None) \<Rightarrow> one, _ \<Rightarrow> zero }) == zero) \<rbrakk>\<close>
hook_rejects 153 \<open>\<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match ((a, b), c) { ((x, y), z) \<Rightarrow> (x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c) \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match ((a, b), c) { ((x, y), z) \<Rightarrow> (x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c) \<rbrakk>\<close>

subsubsection\<open>Struct fixtures (from the tests theory)\<close>

datatype struct_pattern_fixture = Foo (foo: "32 word") (goo: "32 word") | Other

datatype_record struct_pattern_dr =
  dr_foo :: "32 word"
  dr_goo :: "32 word"

definition foo_struct_expr_lift where
  "foo_struct_expr_lift \<equiv> lift_fun2 Foo"
micro_rust_notation (call) foo_struct_expr_lift ("Foo")

definition struct_pattern_dr_struct_expr_lift where
  "struct_pattern_dr_struct_expr_lift \<equiv> lift_fun2 make_struct_pattern_dr"
micro_rust_notation (call) struct_pattern_dr_struct_expr_lift ("struct_pattern_dr")

subsubsection\<open>Tuple Patterns in Match\<close>

hook_rejects 154 \<open>\<mu>\<open> match (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) { (a, b) \<Rightarrow> a } \<close> = \<lbrakk> match (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) { (a, b) \<Rightarrow> a } \<rbrakk>\<close>
hook_rejects 155 \<open>\<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match Some((a, b, c)) { Some((x, _, z)) \<Rightarrow> (x, z), _ \<Rightarrow> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>0 :: 32 word\<rrangle>) }; assert!(res.0 == a); assert!(res.1 == c) \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let res = match Some((a, b, c)) { Some((x, _, z)) \<Rightarrow> (x, z), _ \<Rightarrow> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>0 :: 32 word\<rrangle>) }; assert!(res.0 == a); assert!(res.1 == c) \<rbrakk>\<close>
hook_rejects 156 \<open>\<mu>\<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let d = \<llangle>4 :: 32 word\<rrangle>; let res = match ((a, b), (c, d)) { ((w, x), (y, z)) \<Rightarrow> (w, x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c); assert!(res.3 == d) \<close> = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; let c = \<llangle>3 :: 32 word\<rrangle>; let d = \<llangle>4 :: 32 word\<rrangle>; let res = match ((a, b), (c, d)) { ((w, x), (y, z)) \<Rightarrow> (w, x, y, z) }; assert!(res.0 == a); assert!(res.1 == b); assert!(res.2 == c); assert!(res.3 == d) \<rbrakk>\<close>

subsubsection\<open>Struct Patterns\<close>

hook_rejects 157 \<open>\<mu>\<open> match \<llangle>Foo (1 :: 32 word) 2\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match \<llangle>Foo (1 :: 32 word) 2\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 158 \<open>\<mu>\<open> let res = match \<llangle>Foo (3 :: 32 word) 4\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>7 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>Foo (3 :: 32 word) 4\<rrangle> { Foo { foo: p, goo: q } \<Rightarrow> p + q, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>7 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 159 \<open>\<mu>\<open> let res = match \<llangle>make_struct_pattern_dr (10 :: 32 word) 11\<rrangle> { struct_pattern_dr { dr_goo: q, dr_foo: p } \<Rightarrow> p + q }; assert!(res == \<llangle>21 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>make_struct_pattern_dr (10 :: 32 word) 11\<rrangle> { struct_pattern_dr { dr_goo: q, dr_foo: p } \<Rightarrow> p + q }; assert!(res == \<llangle>21 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 160 \<open>\<mu>\<open> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, goo } \<Rightarrow> foo + goo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>46 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, goo } \<Rightarrow> foo + goo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>46 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 161 \<open>\<mu>\<open> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, .. } \<Rightarrow> foo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>12 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> { Foo { foo, .. } \<Rightarrow> foo, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(res == \<llangle>12 :: 32 word\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Struct Expressions\<close>

text\<open>
These frontend goldens are promoted to the checked D-21 matrix in
\<open>Parser_Test_Expr_Conformance.thy\<close>. The active frontend treats labels as syntax-only and lowers each
head as an ordinary call with source-ordered initializers; Rust-correct metadata semantics are deferred
to T-39.
\<close>

hook_rejects 162 \<open>\<mu>\<open> Foo { foo: \<llangle>1 :: 32 word\<rrangle>, goo: \<llangle>2 :: 32 word\<rrangle> } \<close> = \<lbrakk> Foo { foo: \<llangle>1 :: 32 word\<rrangle>, goo: \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 163 \<open>\<mu>\<open> Foo { goo: \<llangle>2 :: 32 word\<rrangle>, foo: \<llangle>1 :: 32 word\<rrangle> } \<close> = \<lbrakk> Foo { goo: \<llangle>2 :: 32 word\<rrangle>, foo: \<llangle>1 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 164 \<open>\<mu>\<open> struct_pattern_dr { dr_goo: \<llangle>11 :: 32 word\<rrangle>, dr_foo: \<llangle>10 :: 32 word\<rrangle> } \<close> = \<lbrakk> struct_pattern_dr { dr_goo: \<llangle>11 :: 32 word\<rrangle>, dr_foo: \<llangle>10 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 165 \<open>\<mu>\<open> Foo { foo: \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, goo: \<llangle>4 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> } \<close> = \<lbrakk> Foo { foo: \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, goo: \<llangle>4 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> } \<rbrakk>\<close>

subsubsection\<open>Pattern Guards\<close>

context
  fixes x :: \<open>32 word\<close>
begin
hook_rejects 166 \<open>\<mu>\<open> match Some(x) { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(x) { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 167 \<open>\<mu>\<open> match Some(x) { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(x) { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 168 \<open>\<mu>\<open> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<close> = \<lbrakk> match Some(x) { Some(y) \<Rightarrow> { if True { return; } else { () } }, None \<Rightarrow> { if True { return; } else { () } } }; \<rbrakk>\<close>
end

hook_rejects 169 \<open>\<mu>\<open> let zero = \<llangle>0 :: 32 word\<rrangle>; let one = \<llangle>1 :: 32 word\<rrangle>; let res = match Some(one) { Some(x) if x > zero \<Rightarrow> x, _ \<Rightarrow> zero }; assert!(res == one) \<close> = \<lbrakk> let zero = \<llangle>0 :: 32 word\<rrangle>; let one = \<llangle>1 :: 32 word\<rrangle>; let res = match Some(one) { Some(x) if x > zero \<Rightarrow> x, _ \<Rightarrow> zero }; assert!(res == one) \<rbrakk>\<close>
hook_rejects 170 \<open>\<mu>\<open> let zero = \<llangle>0 :: 32 word\<rrangle>; let res = match Some(zero) { Some(x) if x > zero \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(x) \<Rightarrow> x, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> }; assert!(res == zero) \<close> = \<lbrakk> let zero = \<llangle>0 :: 32 word\<rrangle>; let res = match Some(zero) { Some(x) if x > zero \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(x) \<Rightarrow> x, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> }; assert!(res == zero) \<rbrakk>\<close>

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
hook_rejects 171 \<open>\<mu>\<open> match r { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match r { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
end

hook_rejects 172 \<open>\<mu>\<open> match (match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }) { z \<Rightarrow> z } \<close> = \<lbrakk> match (match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }) { z \<Rightarrow> z } \<rbrakk>\<close>
hook_rejects 173 \<open>\<mu>\<open> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { let t = match Ok(x) { Ok(v) \<Rightarrow> v, Err(err_value) \<Rightarrow> \<llangle>0 * err_value :: 32 word\<rrangle> }; t }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { let t = match Ok(x) { Ok(v) \<Rightarrow> v, Err(err_value) \<Rightarrow> \<llangle>0 * err_value :: 32 word\<rrangle> }; t }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>

context
  fixes x :: \<open>32 word\<close>
begin
hook_rejects 174 \<open>\<mu>\<open> match Some(x) { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(x) { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
end

hook_rejects 175 \<open>\<mu>\<open> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { match Some(x) { Some(_) \<Rightarrow> (), None \<Rightarrow> () }; match Ok(x) { Ok(_) \<Rightarrow> (), Err(err_value) \<Rightarrow> { let _ = \<llangle>err_value :: 32 word\<rrangle>; () } } }, None \<Rightarrow> () } \<close> = \<lbrakk> match Some(\<llangle>1 :: 32 word\<rrangle>) { Some(x) \<Rightarrow> { match Some(x) { Some(_) \<Rightarrow> (), None \<Rightarrow> () }; match Ok(x) { Ok(_) \<Rightarrow> (), Err(err_value) \<Rightarrow> { let _ = \<llangle>err_value :: 32 word\<rrangle>; () } } }, None \<Rightarrow> () } \<rbrakk>\<close>

\<comment>\<open>Nesting depth / breadth: depth-3, depth-4, and inner matches in multiple arms.\<close>
context
  fixes z :: \<open>32 word\<close>
  fixes a3 :: \<open>((32 word option, unit) result, unit) result\<close>
  fixes a4 :: \<open>(((32 word option, unit) result, unit) result, unit) result\<close>
  fixes r2 :: \<open>(32 word option, 32 word option) result\<close>
begin
hook_rejects 176 \<open>\<mu>\<open> match a3 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<close> = \<lbrakk> match a3 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<rbrakk>\<close>
hook_rejects 177 \<open>\<mu>\<open> match a4 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Ok(d) \<Rightarrow> match d { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<close> = \<lbrakk> match a4 { Ok(b) \<Rightarrow> match b { Ok(c) \<Rightarrow> match c { Ok(d) \<Rightarrow> match d { Some(v) \<Rightarrow> v, None \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z }, Err(_) \<Rightarrow> z } \<rbrakk>\<close>
hook_rejects 178 \<open>\<mu>\<open> match r2 { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(e) \<Rightarrow> match e { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } } \<close> = \<lbrakk> match r2 { Ok(ov) \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, Err(e) \<Rightarrow> match e { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } } \<rbrakk>\<close>
end

\<comment>\<open>Interaction with other pattern features:
    nested/constructor, tuple, guard, or-patterns; local datatype; and match_switch both ways.\<close>
hook_rejects 179 \<open>\<mu>\<open> match Some(Some(\<llangle>1 :: 32 word\<rrangle>)) { Some(Some(x)) \<Rightarrow> match Some(x) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(Some(\<llangle>1 :: 32 word\<rrangle>)) { Some(Some(x)) \<Rightarrow> match Some(x) { Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>

context
  fixes p q :: \<open>32 word option\<close>
begin
hook_rejects 180 \<open>\<mu>\<open> match (p, q) { (Some(x), qq) \<Rightarrow> match qq { Some(y) \<Rightarrow> x + y, None \<Rightarrow> x }, (None, _) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match (p, q) { (Some(x), qq) \<Rightarrow> match qq { Some(y) \<Rightarrow> x + y, None \<Rightarrow> x }, (None, _) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
end

context
  fixes ov :: \<open>32 word option\<close>
begin
hook_rejects 181 \<open>\<mu>\<open> match ov { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> match Some(y) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match ov { Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> match Some(y) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
end

hook_rejects 182 \<open>\<mu>\<open> match \<llangle>NmA (1 :: 32 word)\<rrangle> { NmA(n) | NmB(n) \<Rightarrow> match Some(n) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, NmC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match \<llangle>NmA (1 :: 32 word)\<rrangle> { NmA(n) | NmB(n) \<Rightarrow> match Some(n) { Some(v) \<Rightarrow> v, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, NmC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 183 \<open>\<mu>\<open> match Some(\<llangle>Foo (1 :: 32 word) 2\<rrangle>) { Some(s) \<Rightarrow> match s { Foo { foo: fp, goo: gq } \<Rightarrow> fp + gq, Other \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match Some(\<llangle>Foo (1 :: 32 word) 2\<rrangle>) { Some(s) \<Rightarrow> match s { Foo { foo: fp, goo: gq } \<Rightarrow> fp + gq, Other \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>

context
  fixes n :: \<open>32 word\<close>
  fixes ov :: \<open>32 word option\<close>
begin
hook_rejects 184 \<open>\<mu>\<open> match ov { Some(x) \<Rightarrow> match_switch x { 0 \<Rightarrow> \<llangle>10 :: 32 word\<rrangle>, _ \<Rightarrow> x }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match ov { Some(x) \<Rightarrow> match_switch x { 0 \<Rightarrow> \<llangle>10 :: 32 word\<rrangle>, _ \<Rightarrow> x }, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
hook_rejects 185 \<open>\<mu>\<open> match_switch n { 0 \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>1 :: 32 word\<rrangle> } \<close> = \<lbrakk> match_switch n { 0 \<Rightarrow> match ov { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }, _ \<Rightarrow> \<llangle>1 :: 32 word\<rrangle> } \<rbrakk>\<close>
end

subsection\<open>Control Flow - Loops\<close>

hook_rejects 186 \<open>\<mu>\<open> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # (3, 4, TNil) # []\<rrangle>; for (a, b) in lst { let _ = a; let _ = b; () }; () \<close> = \<lbrakk> let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # (3, 4, TNil) # []\<rrangle>; for (a, b) in lst { let _ = a; let _ = b; () }; () \<rbrakk>\<close>
hook_rejects 187 \<open>\<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>; for i in lst { if (i.2.0) && i.2.1 { *x = i.0; } else { *x = i.1; } }; x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>; for i in lst { if (i.2.0) && i.2.1 { *x = i.0; } else { *x = i.1; } }; x \<rbrakk>\<close>
hook_rejects 188 \<open>\<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # ((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # []\<rrangle>; for (a, b, (c, d)) in lst { if c && d { x += a; } else { x += b; } }; x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let lst = \<llangle>((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # ((1 :: 32 word), (2 :: 32 word), (True, False, nil), nil) # []\<rrangle>; for (a, b, (c, d)) in lst { if c && d { x += a; } else { x += b; } }; x \<rbrakk>\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
hook_rejects 189 \<open>\<mu>\<open> for i in x .. y { () } \<close> = \<lbrakk> for i in x .. y { () } \<rbrakk>\<close>
end

context
  fixes n :: nat
begin
hook_rejects 190 \<open>\<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] while (*x < 10_u32) { x += 1_u32; }; *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] while (*x < 10_u32) { x += 1_u32; }; *x \<rbrakk>\<close>
hook_rejects 191 \<open>\<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] while (*x < 10_u32) { x += 1_u32; } *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] while (*x < 10_u32) { x += 1_u32; } *x \<rbrakk>\<close>
hook_rejects 192 \<open>\<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] loop { x += 1_u32; }; *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n\<close>) ] loop { x += 1_u32; }; *x \<rbrakk>\<close>
hook_rejects 193 \<open>\<mu>\<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] loop { x += 1_u32; } *x \<close> = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; let _ = \<llangle>x :: (unit, unit, 32 word) Global_Store.ref\<rrangle>; #[fuel(\<epsilon>\<open>n :: nat\<close>) ] loop { x += 1_u32; } *x \<rbrakk>\<close>
end

subsubsection\<open>While Let\<close>

context
  fixes n :: nat
  fixes g :: \<open>'s\<close>
begin
hook_rejects 194 \<open>\<mu>\<open> #[fuel(\<epsilon>\<open>n\<close>)] while let Some(v) = Some(g) { () }; () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Some(v) = Some(g) { () }; () \<rbrakk>\<close>
hook_rejects 195 \<open>\<mu>\<open> #[fuel(\<epsilon>\<open>n :: nat\<close>)] while let Some(v) = Some(g) { () } () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n :: nat\<close>)] while let Some(v) = Some(g) { () } () \<rbrakk>\<close>
hook_rejects 196 \<open>\<mu>\<open> #[fuel(\<epsilon>\<open>n\<close>)] while let Ok(v) = \<llangle>Ok g :: ('s, unit) result\<rrangle> { () }; () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Ok(v) = \<llangle>Ok g :: ('s, unit) result\<rrangle> { () }; () \<rbrakk>\<close>
hook_rejects 197 \<open>\<mu>\<open> #[fuel(\<epsilon>\<open>n\<close>)] while let (a, b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { () }; () \<close> = \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let (a, b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { () }; () \<rbrakk>\<close>
end

subsection\<open>Control Flow - Return\<close>

hook_rejects 200 \<open>\<mu>\<open> let v = \<llangle>42 :: 64 word\<rrangle>; return v; \<close> = \<lbrakk> let v = \<llangle>42 :: 64 word\<rrangle>; return v; \<rbrakk>\<close>
hook_rejects 201 \<open>\<mu>\<open> let (a,b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); return; \<close> = \<lbrakk> let (a,b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); return; \<rbrakk>\<close>

hook_rejects 202 \<open>((FunctionBody \<mu>\<open> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<close>) :: (nat, unit, unit, unit, unit) function_body) = ((FunctionBody \<lbrakk> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<rbrakk>) :: (nat, unit, unit, unit, unit) function_body)\<close>

context
  fixes x :: \<open>'s\<close>
  fixes g :: \<open>'s \<Rightarrow> ('a, nat option, unit, unit, unit) function_body\<close>
begin
hook_rejects 203 \<open>\<mu>\<open> let blub = 0_u32; (if let Some(x) = g(x) { return 0; } else { return 42; }) + 0_u32; return 12; \<close> = \<lbrakk> let blub = 0_u32; (if let Some(x) = g(x) { return 0; } else { return 42; }) + 0_u32; return 12; \<rbrakk>\<close>
end

hook_rejects 204 \<open>\<mu>\<open> let x = if True { 0 } else { 1 }; return x; \<close> = \<lbrakk> let x = if True { 0 } else { 1 }; return x; \<rbrakk>\<close>
hook_rejects 205 \<open>\<mu>\<open> let x = (if True { 0 } else { 1 }); return x; \<close> = \<lbrakk> let x = (if True { 0 } else { 1 }); return x; \<rbrakk>\<close>

subsection\<open>Control Flow - Error Propagation\<close>

context
  fixes opt :: \<open>nat option\<close>
begin
hook_rejects 206 \<open>\<mu>\<open> opt? \<close> = \<lbrakk> opt? \<rbrakk>\<close>
hook_rejects 207 \<open>\<mu>\<open> let x = opt?; x \<close> = \<lbrakk> let x = opt?; x \<rbrakk>\<close>
end

context
  fixes res :: \<open>(nat, bool) result\<close>
begin
hook_rejects 208 \<open>\<mu>\<open> res? \<close> = \<lbrakk> res? \<rbrakk>\<close>
hook_rejects 209 \<open>\<mu>\<open> let x = res?; x \<close> = \<lbrakk> let x = res?; x \<rbrakk>\<close>
end

subsection\<open>Data Structures - Tuples\<close>

hook_rejects 210 \<open>\<mu>\<open> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>) \<close> = \<lbrakk> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 211 \<open>\<mu>\<open> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False) \<close> = \<lbrakk> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False) \<rbrakk>\<close>
hook_rejects 212 \<open>\<mu>\<open> ((False, True), False) \<close> = \<lbrakk> ((False, True), False) \<rbrakk>\<close>
hook_rejects 213 \<open>\<mu>\<open> assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>); assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>); \<close> = \<lbrakk> assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>); assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>); \<rbrakk>\<close>
hook_rejects 214 \<open>\<mu>\<open> let tup = (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>, \<llangle>6 :: 32 word\<rrangle>, \<llangle>7 :: 32 word\<rrangle>, \<llangle>8 :: 32 word\<rrangle>, \<llangle>9 :: 32 word\<rrangle>, \<llangle>10 :: 32 word\<rrangle>, \<llangle>11 :: 32 word\<rrangle>, \<llangle>12 :: 32 word\<rrangle>, \<llangle>13 :: 32 word\<rrangle>, \<llangle>14 :: 32 word\<rrangle>, \<llangle>15 :: 32 word\<rrangle>); assert!(tup.6 == \<llangle>6 :: 32 word\<rrangle>); assert!(tup.10 == \<llangle>10 :: 32 word\<rrangle>); assert!(tup.15 == \<llangle>15 :: 32 word\<rrangle>) \<close> = \<lbrakk> let tup = (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>, \<llangle>6 :: 32 word\<rrangle>, \<llangle>7 :: 32 word\<rrangle>, \<llangle>8 :: 32 word\<rrangle>, \<llangle>9 :: 32 word\<rrangle>, \<llangle>10 :: 32 word\<rrangle>, \<llangle>11 :: 32 word\<rrangle>, \<llangle>12 :: 32 word\<rrangle>, \<llangle>13 :: 32 word\<rrangle>, \<llangle>14 :: 32 word\<rrangle>, \<llangle>15 :: 32 word\<rrangle>); assert!(tup.6 == \<llangle>6 :: 32 word\<rrangle>); assert!(tup.10 == \<llangle>10 :: 32 word\<rrangle>); assert!(tup.15 == \<llangle>15 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 215 \<open>\<mu>\<open> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let c = \<llangle>2 :: 32 word\<rrangle>; let tup = (a, b, c, (False, True)); assert!(tup.3.0 == False); assert!(tup.3.1 == True); \<close> = \<lbrakk> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let c = \<llangle>2 :: 32 word\<rrangle>; let tup = (a, b, c, (False, True)); assert!(tup.3.0 == False); assert!(tup.3.1 == True); \<rbrakk>\<close>
hook_rejects 216 \<open>\<mu>\<open> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let tup = (a, (b, a)); let (aaa, (bbb, ccc)) = tup; assert!(aaa == a); assert!(bbb == b); assert!(ccc == a); \<close> = \<lbrakk> let a = \<llangle>0 :: 32 word\<rrangle>; let b = \<llangle>1 :: 32 word\<rrangle>; let tup = (a, (b, a)); let (aaa, (bbb, ccc)) = tup; assert!(aaa == a); assert!(bbb == b); assert!(ccc == a); \<rbrakk>\<close>
hook_rejects 217 \<open>\<mu>\<open> let a = \<llangle>10 :: 32 word\<rrangle>; let b = \<llangle>20 :: 32 word\<rrangle>; let c = \<llangle>30 :: 32 word\<rrangle>; let tup = (a, (b, c)); let (x, (y, z)) = tup; assert!(x == a); assert!(y == b); assert!(z == c) \<close> = \<lbrakk> let a = \<llangle>10 :: 32 word\<rrangle>; let b = \<llangle>20 :: 32 word\<rrangle>; let c = \<llangle>30 :: 32 word\<rrangle>; let tup = (a, (b, c)); let (x, (y, z)) = tup; assert!(x == a); assert!(y == b); assert!(z == c) \<rbrakk>\<close>

subsection\<open>Data Structures - Option and Result\<close>

hook_rejects 218 \<open>\<mu>\<open> Some(\<llangle>42 :: nat\<rrangle>) \<close> = \<lbrakk> Some(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>
hook_rejects 219 \<open>\<mu>\<open> None \<close> = \<lbrakk> None \<rbrakk>\<close>
hook_rejects 220 \<open>\<mu>\<open> \<llangle>Some (0 :: nat)\<rrangle> \<close> = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close>
hook_rejects 221 \<open>\<mu>\<open> Ok(\<llangle>42 :: nat\<rrangle>) \<close> = \<lbrakk> Ok(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>
hook_rejects 222 \<open>\<mu>\<open> Err(\<llangle>42 :: nat\<rrangle>) \<close> = \<lbrakk> Err(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>

subsection\<open>Data Structures - Ranges\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
hook_rejects 223 \<open>\<mu>\<open> x..y \<close> = \<lbrakk> x..y \<rbrakk>\<close>
hook_rejects 224 \<open>\<mu>\<open> x..=y \<close> = \<lbrakk> x..=y \<rbrakk>\<close>
hook_rejects 225 \<open>\<mu>\<open> let rng = x ..= x+y; rng.is_empty() \<close> = \<lbrakk> let rng = x ..= x+y; rng.is_empty() \<rbrakk>\<close>
end

hook_rejects 226 \<open>\<mu>\<open> let int_max = \<llangle>255 :: 8 word\<rrangle>; let inclusive = int_max ..= int_max; assert!(!(inclusive.is_empty())); assert!(inclusive.contains(int_max)); let exclusive = int_max .. int_max; assert!(exclusive.is_empty()); () \<close> = \<lbrakk> let int_max = \<llangle>255 :: 8 word\<rrangle>; let inclusive = int_max ..= int_max; assert!(!(inclusive.is_empty())); assert!(inclusive.contains(int_max)); let exclusive = int_max .. int_max; assert!(exclusive.is_empty()); () \<rbrakk>\<close>
hook_rejects 227 \<open>\<mu>\<open> let mut count = \<llangle>0 :: 8 word\<rrangle>; let _ = \<llangle>count :: (unit, unit, 8 word) Global_Store.ref\<rrangle>; let int_max = \<llangle>255 :: 8 word\<rrangle>; for i in int_max ..= int_max { count += \<llangle>1 :: 8 word\<rrangle>; }; assert!(*count == \<llangle>1 :: 8 word\<rrangle>); () \<close> = \<lbrakk> let mut count = \<llangle>0 :: 8 word\<rrangle>; let _ = \<llangle>count :: (unit, unit, 8 word) Global_Store.ref\<rrangle>; let int_max = \<llangle>255 :: 8 word\<rrangle>; for i in int_max ..= int_max { count += \<llangle>1 :: 8 word\<rrangle>; }; assert!(*count == \<llangle>1 :: 8 word\<rrangle>); () \<rbrakk>\<close>

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
hook_rejects 228 \<open>\<mu>\<open> h(a, b, c, a) \<close> = \<lbrakk> h(a, b, c, a) \<rbrakk>\<close>
hook_rejects 229 \<open>\<mu>\<open> i(a, b, c, a, b) \<close> = \<lbrakk> i(a, b, c, a, b) \<rbrakk>\<close>
hook_rejects 230 \<open>\<mu>\<open> \<epsilon>\<open>g\<close>(c); g(c); f(a,b); a.f(b); f(g(c),b); g(c).f(b) \<close> = \<lbrakk> \<epsilon>\<open>g\<close>(c); g(c); f(a,b); a.f(b); f(g(c),b); g(c).f(b) \<rbrakk>\<close>
hook_rejects 231 \<open>\<mu>\<open> f(g(c),b) \<close> = \<lbrakk> f(g(c),b) \<rbrakk>\<close>
end

context
  fixes f14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin
hook_rejects 232 \<open>\<mu>\<open> f14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<close> = \<lbrakk> f14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<rbrakk>\<close>
end

subsubsection\<open>Method-Style Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
begin
hook_rejects 233 \<open>\<mu>\<open> g(c); c.g(); \<close> = \<lbrakk> g(c); c.g(); \<rbrakk>\<close>
hook_rejects 234 \<open>\<mu>\<open> a.f(b) \<close> = \<lbrakk> a.f(b) \<rbrakk>\<close>
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
hook_rejects 235 \<open>\<mu>\<open> f::<5>() \<close> = \<lbrakk> f::<5>() \<rbrakk>\<close>
hook_rejects 236 \<open>\<mu>\<open> g::<10>(True) \<close> = \<lbrakk> g::<10>(True) \<rbrakk>\<close>
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
hook_rejects 237 \<open>\<mu>\<open> || return x; \<close> = \<lbrakk> || return x; \<rbrakk>\<close>

hook_rejects 239 \<open>\<mu>\<open> |x, y| { let z = f(x,y); return z; } \<close> = \<lbrakk> |x, y| { let z = f(x,y); return z; } \<rbrakk>\<close>
hook_rejects 240 \<open>\<mu>\<open> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<close> = \<lbrakk> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<rbrakk>\<close>
end

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
hook_rejects 241 \<open>\<mu>\<open> x \<close> = \<lbrakk> x \<rbrakk>\<close>
hook_rejects 242 \<open>\<mu>\<open> x.field1 \<close> = \<lbrakk> x.field1 \<rbrakk>\<close>
hook_rejects 243 \<open>\<mu>\<open> y.field4 \<close> = \<lbrakk> y.field4 \<rbrakk>\<close>
hook_rejects 244 \<open>\<mu>\<open> y.field3.field1 \<close> = \<lbrakk> y.field3.field1 \<rbrakk>\<close>
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
hook_rejects 245 \<open>(\<lambda> x :: foobar. \<mu>\<open> x.field5 + x.field6 \<close>) = (\<lambda> x :: foobar. \<lbrakk> x.field5 + x.field6 \<rbrakk>)\<close>
hook_rejects 246 \<open>(\<lambda> x :: ('addr, 'fv, foobar) ref. \<mu>\<open> *x.field5 + *x.field6 \<close>) = (\<lambda> x :: ('addr, 'fv, foobar) ref. \<lbrakk> *x.field5 + *x.field6 \<rbrakk>)\<close>
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
hook_rejects 247 \<open>\<mu>\<open> r.f(10) \<close> = \<lbrakk> r.f(10) \<rbrakk>\<close>
hook_rejects 248 \<open>\<mu>\<open> *(s. field3_lens) \<close> = \<lbrakk> *(s. field3_lens) \<rbrakk>\<close>
hook_rejects 249 \<open>\<mu>\<open> (*s). field3_lens \<close> = \<lbrakk> (*s). field3_lens \<rbrakk>\<close>
hook_rejects 250 \<open>\<mu>\<open> *r \<close> = \<lbrakk> *r \<rbrakk>\<close>
hook_rejects 251 \<open>\<mu>\<open> *(s.field4_lens) \<close> = \<lbrakk> *(s.field4_lens) \<rbrakk>\<close>
hook_rejects 252 \<open>\<mu>\<open> (*s).field4_lens \<close> = \<lbrakk> (*s).field4_lens \<rbrakk>\<close>
hook_rejects 253 \<open>\<mu>\<open> s.testrec2_field3_lens \<close> = \<lbrakk> s.testrec2_field3_lens \<rbrakk>\<close>
hook_rejects 254 \<open>\<mu>\<open> s.testrec2_field3_lens.testrec_field2_lens \<close> = \<lbrakk> s.testrec2_field3_lens.testrec_field2_lens \<rbrakk>\<close>
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
hook_rejects 255 \<open>\<mu>\<open> m.lo \<close> = \<lbrakk> m.lo \<rbrakk>\<close>
hook_rejects 256 \<open>\<mu>\<open> m.end \<close> = \<lbrakk> m.end \<rbrakk>\<close>
hook_rejects 257 \<open>\<mu>\<open> m.flag \<close> = \<lbrakk> m.flag \<rbrakk>\<close>
hook_rejects 258 \<open>\<mu>\<open> m.bounds_rec_bounds_rec_lo_lens \<close> = \<lbrakk> m.bounds_rec_bounds_rec_lo_lens \<rbrakk>\<close>
hook_rejects 259 \<open>\<mu>\<open> m.bounds_rec_bounds_rec_hi_lens \<close> = \<lbrakk> m.bounds_rec_bounds_rec_hi_lens \<rbrakk>\<close>
hook_rejects 260 \<open>\<mu>\<open> m.bounds_rec_bounds_rec_flag_lens \<close> = \<lbrakk> m.bounds_rec_bounds_rec_flag_lens \<rbrakk>\<close>
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
hook_rejects 261 \<open>\<mu>\<open> p.renamed \<close> = \<lbrakk> p.renamed \<rbrakk>\<close>
hook_rejects 262 \<open>\<mu>\<open> p.por_kept \<close> = \<lbrakk> p.por_kept \<rbrakk>\<close>
end

subsubsection\<open>Default Registration (no mapping)\<close>

datatype_record no_override_rec =
  nor_a :: \<open>32 word\<close>
  nor_b :: bool
micro_rust_record no_override_rec

context
  fixes n :: no_override_rec
begin
hook_rejects 263 \<open>\<mu>\<open> n.nor_a \<close> = \<lbrakk> n.nor_a \<rbrakk>\<close>
hook_rejects 264 \<open>\<mu>\<open> n.nor_b \<close> = \<lbrakk> n.nor_b \<rbrakk>\<close>
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
hook_rejects 265 \<open>\<mu>\<open> ob.inner \<close> = \<lbrakk> ob.inner \<rbrakk>\<close>
hook_rejects 266 \<open>\<mu>\<open> ob.flag \<close> = \<lbrakk> ob.flag \<rbrakk>\<close>
hook_rejects 267 \<open>\<mu>\<open> ob.inner.value \<close> = \<lbrakk> ob.inner.value \<rbrakk>\<close>
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
hook_rejects 268 \<open>(\<lambda> x :: loc_named. \<mu>\<open> x.lo + x.hi \<close>) = (\<lambda> x :: loc_named. \<lbrakk> x.lo + x.hi \<rbrakk>)\<close>
hook_rejects 269 \<open>(\<lambda> x :: ('addr, 'fv, loc_named) ref. \<mu>\<open> *x.lo + *x.hi \<close>) = (\<lambda> x :: ('addr, 'fv, loc_named) ref. \<lbrakk> *x.lo + *x.hi \<rbrakk>)\<close>
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

context
  fixes b :: \<open>bool\<close>
  fixes o :: \<open>nat option\<close>
  fixes a_value :: \<open>32 word\<close>
  fixes x y :: \<open>nat\<close>
begin
hook_rejects 270 \<open>\<mu>\<open> assert!( b ) \<close> = \<lbrakk> assert!( b ) \<rbrakk>\<close>
hook_rejects 271 \<open>\<mu>\<open> debug_assert!( b ) \<close> = \<lbrakk> debug_assert!( b ) \<rbrakk>\<close>
hook_rejects 272 \<open>\<mu>\<open> assert!(!o.is_none()) \<close> = \<lbrakk> assert!(!o.is_none()) \<rbrakk>\<close>
hook_rejects 273 \<open>\<mu>\<open> assert!(b); a_value as u16\<close> = \<lbrakk> assert!(b); a_value as u16\<rbrakk>\<close>
hook_rejects 274 \<open>\<mu>\<open> assert!(a_value as usize == a_value as usize); a_value as u16\<close> = \<lbrakk> assert!(a_value as usize == a_value as usize); a_value as u16\<rbrakk>\<close>
hook_rejects 275 \<open>\<mu>\<open> assert_eq!(x, y) \<close> = \<lbrakk> assert_eq!(x, y) \<rbrakk>\<close>
hook_rejects 276 \<open>\<mu>\<open> assert_ne!(x, y) \<close> = \<lbrakk> assert_ne!(x, y) \<rbrakk>\<close>
hook_rejects 277 \<open>\<mu>\<open> assert!(b, "ignored assertion message") \<close> = \<lbrakk> assert!(b, "ignored assertion message") \<rbrakk>\<close>
hook_rejects 278 \<open>\<mu>\<open> debug_assert!(b, "ignored debug assertion message", x) \<close> = \<lbrakk> debug_assert!(b, "ignored debug assertion message", x) \<rbrakk>\<close>
hook_rejects 279 \<open>\<mu>\<open> assert_eq!(x, y, "ignored assert_eq message", x) \<close> = \<lbrakk> assert_eq!(x, y, "ignored assert_eq message", x) \<rbrakk>\<close>
hook_rejects 280 \<open>\<mu>\<open> assert_ne!(x, y, "ignored assert_ne message", y) \<close> = \<lbrakk> assert_ne!(x, y, "ignored assert_ne message", y) \<rbrakk>\<close>
hook_rejects 281 \<open>\<mu>\<open> debug_assert_eq!(x, y, "ignored debug_assert_eq message") \<close> = \<lbrakk> debug_assert_eq!(x, y, "ignored debug_assert_eq message") \<rbrakk>\<close>
hook_rejects 282 \<open>\<mu>\<open> debug_assert_ne!(x, y, "ignored debug_assert_ne message") \<close> = \<lbrakk> debug_assert_ne!(x, y, "ignored debug_assert_ne message") \<rbrakk>\<close>
end

context
  fixes msg :: \<open>String.literal\<close>
  and idx :: \<open>32 word\<close>
  and r :: \<open>('a, 'b, 'v) ref\<close>
  and nm :: \<open>String.literal\<close>
begin
hook_rejects 283 \<open>\<mu>\<open> panic!(msg) \<close> = \<lbrakk> panic!(msg) \<rbrakk>\<close>
hook_rejects 284 \<open>\<mu>\<open> fatal!(msg) \<close> = \<lbrakk> fatal!(msg) \<rbrakk>\<close>
hook_rejects 285 \<open>\<mu>\<open> unimplemented!("some_fun") \<close> = \<lbrakk> unimplemented!("some_fun") \<rbrakk>\<close>
hook_rejects 286 \<open>\<mu>\<open> unimplemented!(nm) \<close> = \<lbrakk> unimplemented!(nm) \<rbrakk>\<close>
hook_rejects 287 \<open>\<mu>\<open> todo!("oh no!") \<close> = \<lbrakk> todo!("oh no!") \<rbrakk>\<close>
hook_rejects 288 \<open>\<mu>\<open> fatal!("yikes!") \<close> = \<lbrakk> fatal!("yikes!") \<rbrakk>\<close>
hook_rejects 289 \<open>\<mu>\<open> fatal!( \<llangle>''yikes!''\<rrangle> ) \<close> = \<lbrakk> fatal!( \<llangle>''yikes!''\<rrangle> ) \<rbrakk>\<close>
hook_rejects 290 \<open>\<mu>\<open> panic!() \<close> = \<lbrakk> panic!() \<rbrakk>\<close>
hook_rejects 291 \<open>\<mu>\<open> unimplemented!() \<close> = \<lbrakk> unimplemented!() \<rbrakk>\<close>
hook_rejects 292 \<open>\<mu>\<open> todo!() \<close> = \<lbrakk> todo!() \<rbrakk>\<close>
hook_rejects 293 \<open>\<mu>\<open> fatal!() \<close> = \<lbrakk> fatal!() \<rbrakk>\<close>
hook_rejects 294 \<open>\<mu>\<open> panic!("first", msg) \<close> = \<lbrakk> panic!("first", msg) \<rbrakk>\<close>
hook_rejects 295 \<open>\<mu>\<open> unimplemented!("first", msg) \<close> = \<lbrakk> unimplemented!("first", msg) \<rbrakk>\<close>
hook_rejects 296 \<open>\<mu>\<open> todo!("first", msg) \<close> = \<lbrakk> todo!("first", msg) \<rbrakk>\<close>
hook_rejects 297 \<open>\<mu>\<open> fatal!("first", msg) \<close> = \<lbrakk> fatal!("first", msg) \<rbrakk>\<close>
hook_rejects 298 \<open>\<mu>\<open> unreachable!() \<close> = \<lbrakk> unreachable!() \<rbrakk>\<close>
hook_rejects 299 \<open>\<mu>\<open> unreachable!("should not reach here") \<close> = \<lbrakk> unreachable!("should not reach here") \<rbrakk>\<close>
hook_rejects 300 \<open>\<mu>\<open> unreachable!("bad state: {}", msg) \<close> = \<lbrakk> unreachable!("bad state: {}", msg) \<rbrakk>\<close>
hook_rejects 301 \<open>\<mu>\<open> panic!("Invalid index: {}", idx) \<close> = \<lbrakk> panic!("Invalid index: {}", idx) \<rbrakk>\<close>
hook_rejects 302 \<open>\<mu>\<open> unimplemented!("not done: {} {}", idx, idx) \<close> = \<lbrakk> unimplemented!("not done: {} {}", idx, idx) \<rbrakk>\<close>
hook_rejects 303 \<open>\<mu>\<open> todo!("implement: {}", idx) \<close> = \<lbrakk> todo!("implement: {}", idx) \<rbrakk>\<close>
hook_rejects 304 \<open>\<mu>\<open> addr_of!(r) \<close> = \<lbrakk> addr_of!(r) \<rbrakk>\<close>
hook_rejects 305 \<open>\<mu>\<open> addr_of_mut!(r) \<close> = \<lbrakk> addr_of_mut!(r) \<rbrakk>\<close>
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
hook_rejects 306 \<open>\<mu>\<open> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<close> = \<lbrakk> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<rbrakk>\<close>
hook_rejects 307 \<open>\<mu>\<open> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<close> = \<lbrakk> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<rbrakk>\<close>
hook_rejects 308 \<open>\<mu>\<open> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<close> = \<lbrakk> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<rbrakk>\<close>
end

subsection\<open>Miscellaneous Features\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
hook_rejects 311 \<open>\<mu>\<open> unsafe { panic!("msg") } \<close> = \<lbrakk> unsafe { panic!("msg") } \<rbrakk>\<close>
end

subsubsection\<open>Array and Slice Expression Literals\<close>

hook_rejects 312 \<open>\<mu>\<open> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<close> = \<lbrakk> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>
hook_rejects 313 \<open>\<mu>\<open> &[\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<close> = \<lbrakk> &[\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close>
hook_rejects 314 \<open>\<mu>\<open> & mut [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<close> = \<lbrakk> & mut [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close>

hook_rejects 316 \<open>\<mu>\<open> [\<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<close> = \<lbrakk> [\<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>
hook_rejects 317 \<open>\<mu>\<open> let xs = [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>1 :: 32 word\<rrangle>); assert!(xs[2_usize] == \<llangle>3 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>1 :: 32 word\<rrangle>); assert!(xs[2_usize] == \<llangle>3 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 318 \<open>\<mu>\<open> let xs = &[\<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>]; let s = match xs { [a, b] \<Rightarrow> a + b, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(s == \<llangle>9 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = &[\<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>]; let s = match xs { [a, b] \<Rightarrow> a + b, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> }; assert!(s == \<llangle>9 :: 32 word\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Vec Macro\<close>

text\<open>
These rows are promoted in \<open>Parser_Test_Expr_Conformance.thy\<close>, including empty,
nested, indexed, parenthesized, and borrow-interaction variants.
\<close>

hook_rejects 319 \<open>\<mu>\<open> vec![\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<close> = \<lbrakk> vec![\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>
hook_rejects 320 \<open>\<mu>\<open> vec![] \<close> = \<lbrakk> vec![] \<rbrakk>\<close>
hook_rejects 321 \<open>\<mu>\<open> let xs = vec![\<llangle>10 :: 32 word\<rrangle>, \<llangle>20 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>10 :: 32 word\<rrangle>) \<close> = \<lbrakk> let xs = vec![\<llangle>10 :: 32 word\<rrangle>, \<llangle>20 :: 32 word\<rrangle>]; assert!(xs[0_usize] == \<llangle>10 :: 32 word\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Matches Macro\<close>

text\<open>
These rows are promoted to checked parity tests together with constructor,
nested, alias, slice, struct, or-pattern, outer-capture, and single-evaluation
coverage. Frontend-rejected wildcard, binder, range, bracket, and malformed
forms are pinned in \<open>Parser_Tests_Negative_Conformance.thy\<close>.
\<close>

context
  fixes x :: \<open>nat option\<close>
  and y :: \<open>bool option\<close>
begin
hook_rejects 322 \<open>\<mu>\<open> matches!(x, Some(_)) \<close> = \<lbrakk> matches!(x, Some(_)) \<rbrakk>\<close>
hook_rejects 323 \<open>\<mu>\<open> matches!(x, None) \<close> = \<lbrakk> matches!(x, None) \<rbrakk>\<close>
hook_rejects 324 \<open>\<mu>\<open> matches!(y, Some(true) | None) \<close> = \<lbrakk> matches!(y, Some(true) | None) \<rbrakk>\<close>
end

subsubsection\<open>Indexing\<close>

context
  fixes xs :: \<open>nat list\<close>
  fixes xss :: \<open>nat list list\<close>
begin
hook_rejects 325 \<open>\<mu>\<open> xs [0_usize..100_usize][42_usize] \<close> = \<lbrakk> xs [0_usize..100_usize][42_usize] \<rbrakk>\<close>
hook_rejects 326 \<open>\<mu>\<open> xss[10_usize] \<close> = \<lbrakk> xss[10_usize] \<rbrakk>\<close>
hook_rejects 327 \<open>\<mu>\<open> xss[10_usize][100_usize] \<close> = \<lbrakk> xss[10_usize][100_usize] \<rbrakk>\<close>
end

subsubsection\<open>Const Bindings\<close>

hook_rejects 328 \<open>\<mu>\<open> const FOO = \<llangle>5 :: nat\<rrangle>; () \<close> = \<lbrakk> const FOO = \<llangle>5 :: nat\<rrangle>; () \<rbrakk>\<close>

subsubsection\<open>Sequencing\<close>

hook_rejects 330 \<open>\<mu>\<open> let a = 1; let b = \<llangle>2 :: nat\<rrangle>; a \<close> = \<lbrakk> let a = 1; let b = \<llangle>2 :: nat\<rrangle>; a \<rbrakk>\<close>

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

hook_rejects 331 \<open>\<mu>\<open>the::record\<close> = \<lbrakk>the::record\<rbrakk>\<close>
hook_rejects 332 \<open>\<mu>\<open>(the::record).field1\<close> = \<lbrakk>(the::record).field1\<rbrakk>\<close>
hook_rejects 333 \<open>\<mu>\<open>the::record.field1\<close> = \<lbrakk>the::record.field1\<rbrakk>\<close>

hook_rejects 334 \<open>\<mu>\<open> foo::bar::test1 \<close> = \<lbrakk> foo::bar::test1 \<rbrakk>\<close>
hook_rejects 335 \<open>\<mu>\<open> foo::bar:: test2 \<close> = \<lbrakk> foo::bar:: test2 \<rbrakk>\<close>
hook_rejects 336 \<open>\<mu>\<open> foo:: bar::test3 \<close> = \<lbrakk> foo:: bar::test3 \<rbrakk>\<close>

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

hook_rejects 337 \<open>\<mu>\<open> test::Test_1 \<close> = \<lbrakk> test::Test_1 \<rbrakk>\<close>
hook_rejects 338 \<open>\<mu>\<open>plus2::lifted(three)\<close> = \<lbrakk>plus2::lifted(three)\<rbrakk>\<close>
hook_rejects 339 \<open>\<mu>\<open>plus_two_lift(three)\<close> = \<lbrakk>plus_two_lift(three)\<rbrakk>\<close>
hook_rejects 340 \<open>\<mu>\<open>
  let arg = test::Test_1;
  let fun = plus2::lifted;
  match arg { test::Test_1 \<Rightarrow> fun(three), test::Test_2 \<Rightarrow> plus2::lifted(three) }
\<close> = \<lbrakk>
  let arg = test::Test_1;
  let fun = plus2::lifted;
  match arg { test::Test_1 \<Rightarrow> fun(three), test::Test_2 \<Rightarrow> plus2::lifted(three) }
\<rbrakk>\<close>
hook_rejects 341 \<open>\<mu>\<open>
  let x = 5;
  match x { 2 \<Rightarrow> False, number::three \<Rightarrow> False, 0 \<Rightarrow> False, 1 \<Rightarrow> False, _ \<Rightarrow> True }
\<close> = \<lbrakk>
  let x = 5;
  match x { 2 \<Rightarrow> False, number::three \<Rightarrow> False, 0 \<Rightarrow> False, 1 \<Rightarrow> False, _ \<Rightarrow> True }
\<rbrakk>\<close>
hook_rejects 342 \<open>\<mu>\<open>
  let x = 5;
  match_switch x { number::three \<Rightarrow> False, _ \<Rightarrow> True }
\<close> = \<lbrakk>
  let x = 5;
  match_switch x { number::three \<Rightarrow> False, _ \<Rightarrow> True }
\<rbrakk>\<close>

end

subsection\<open>Disjunctive Patterns\<close>

hook_rejects 343 \<open>\<mu>\<open> match Some(\<llangle>42 :: nat\<rrangle>) { Some(x) | None \<Rightarrow> x } \<close> = \<lbrakk> match Some(\<llangle>42 :: nat\<rrangle>) { Some(x) | None \<Rightarrow> x } \<rbrakk>\<close>

context
  fixes x :: \<open>32 word\<close>
begin
hook_rejects 344 \<open>\<mu>\<open> match_switch x { 1 | 2 | 3 \<Rightarrow> True, _ \<Rightarrow> False } \<close> = \<lbrakk> match_switch x { 1 | 2 | 3 \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk>\<close>
end

context
  fixes x :: \<open>32 word option\<close>
begin
hook_rejects 345 \<open>\<mu>\<open> match x { Some(y) | None if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close> = \<lbrakk> match x { Some(y) | None if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk>\<close>
end

hook_rejects 346 \<open>\<mu>\<open> match Some(Ok(\<llangle>1 :: nat\<rrangle>)) { Some(Ok(x) | Err(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<close> = \<lbrakk> match Some(Ok(\<llangle>1 :: nat\<rrangle>)) { Some(Ok(x) | Err(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<rbrakk>\<close>

context
  fixes x :: \<open>64 word\<close>
begin
hook_rejects 347 \<open>\<mu>\<open> match_switch x { 0 | 1 \<Rightarrow> False, _ \<Rightarrow> True } \<close> = \<lbrakk> match_switch x { 0 | 1 \<Rightarrow> False, _ \<Rightarrow> True } \<rbrakk>\<close>
end

hook_rejects 348 \<open>\<mu>\<open> let res = match Ok(\<llangle>10 :: 32 word\<rrangle>) { Ok(x) | Err(x) \<Rightarrow> x }; assert!(res == \<llangle>10 :: 32 word\<rrangle>) \<close> = \<lbrakk> let res = match Ok(\<llangle>10 :: 32 word\<rrangle>) { Ok(x) | Err(x) \<Rightarrow> x }; assert!(res == \<llangle>10 :: 32 word\<rrangle>) \<rbrakk>\<close>
hook_rejects 349 \<open>\<mu>\<open> match (Some(\<llangle>1 :: nat\<rrangle>), Some(\<llangle>2 :: nat\<rrangle>)) { (Some(x), Some(y)) | (None, Some(y)) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<close> = \<lbrakk> match (Some(\<llangle>1 :: nat\<rrangle>), Some(\<llangle>2 :: nat\<rrangle>)) { (Some(x), Some(y)) | (None, Some(y)) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<rbrakk>\<close>

subsection\<open>Mutable Pattern Destructuring\<close>

hook_rejects 350 \<open>\<mu>\<open> let mut (x, y) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); x + y \<close> = \<lbrakk> let mut (x, y) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>); x + y \<rbrakk>\<close>
hook_rejects 351 \<open>\<mu>\<open> let mut (a, b, c) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>); a \<close> = \<lbrakk> let mut (a, b, c) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>); a \<rbrakk>\<close>

section\<open> Definition goldens \<close>

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
hook_rejects 352 \<open>\<mu>\<open> p.x \<close> = \<lbrakk> p.x \<rbrakk>\<close>
hook_rejects 353 \<open>\<mu>\<open> p.y \<close> = \<lbrakk> p.y \<rbrakk>\<close>
end

context fixes fl :: flags begin
hook_rejects 354 \<open>\<mu>\<open> fl.bits \<close> = \<lbrakk> fl.bits \<rbrakk>\<close>
hook_rejects 355 \<open>\<mu>\<open> fl.enabled \<close> = \<lbrakk> fl.enabled \<rbrakk>\<close>
end

context fixes w :: wrapper begin
hook_rejects 356 \<open>\<mu>\<open> w.value \<close> = \<lbrakk> w.value \<rbrakk>\<close>
end

context fixes ln :: line begin
hook_rejects 357 \<open>\<mu>\<open> ln.from \<close> = \<lbrakk> ln.from \<rbrakk>\<close>
hook_rejects 358 \<open>\<mu>\<open> ln.to \<close> = \<lbrakk> ln.to \<rbrakk>\<close>
hook_rejects 359 \<open>\<mu>\<open> ln.from.x \<close> = \<lbrakk> ln.from.x \<rbrakk>\<close>
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

hook_rejects 360 \<open>\<mu>\<open> Color::Red \<close> = \<lbrakk> Color::Red \<rbrakk>\<close>

context fixes c :: color begin
hook_rejects 361 \<open>\<mu>\<open>
  match c { Color::Red \<Rightarrow> \<llangle>0 :: nat\<rrangle>, Color::Green \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Color::Blue \<Rightarrow> \<llangle>2 :: nat\<rrangle> }
\<close> = \<lbrakk>
  match c { Color::Red \<Rightarrow> \<llangle>0 :: nat\<rrangle>, Color::Green \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Color::Blue \<Rightarrow> \<llangle>2 :: nat\<rrangle> }
\<rbrakk>\<close>
end

end
