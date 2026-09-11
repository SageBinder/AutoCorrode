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
This theory is generated structurally from \<open>Conformance_Corpus.thy\<close>. Each retained
lemma keeps the legacy-frontend RHS and replaces its LHS with a copy of that RHS in which every
\<open>\<lbrakk>src\<rbrakk>\<close> embedding is written with \<open>\<mu>\<open>src\<close>\<close>. These are
the direct replacements accepted by the closed quotation, and every equality must close by
\<open>refl\<close>.

Rows whose exact replacement is intentionally rejected are tested in
\<open>Parser_Tests_Hook_Negative_Conformance.thy\<close>. The focused semantic and diagnostic
properties remain in \<open>Parser_Tests_Hook_Properties.thy\<close>. \<open>**\<close> and
\<open>!!\<close> mean double dereference and negation.
\<close>


section\<open> Expression goldens \<close>

subsection\<open>Literals and Basic Values\<close>

subsubsection\<open>Numeric Literals\<close>

lemma \<open>\<mu>\<open> 0 \<close> = \<lbrakk> 0 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 1 \<close> = \<lbrakk> 1 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 42 \<close> = \<lbrakk> 42 \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> 0xff \<close> = \<lbrakk> 0xff \<rbrakk>\<close> by (rule refl)




subsubsection\<open>Boolean Literals\<close>







subsubsection\<open>Unit Literal\<close>

context
  fixes f :: \<open>unit \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>unit \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
lemma \<open>\<mu>\<open> () \<close> = \<lbrakk> () \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> (); () \<close> = \<lbrakk> (); () \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> (); (); \<close> = \<lbrakk> (); (); \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> return (); \<close> = \<lbrakk> return (); \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> return; \<close> = \<lbrakk> return; \<rbrakk>\<close> by (rule refl)


end

subsubsection\<open>String Literals\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin


end

subsubsection\<open>HOL Value Injection (Antiquotation)\<close>







subsection\<open>Type Casts and Ascriptions\<close>

subsubsection\<open>Type Casting\<close>

context
  fixes a_value :: \<open>32 word\<close>
begin








end

subsubsection\<open>Raw Pointer Casts\<close>

context
  fixes raw_buf :: \<open>('addr, 'gv) gref\<close>
begin








end

subsubsection\<open>Numeric Ascriptions\<close>

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

subsection\<open>Boolean Operators\<close>

subsubsection\<open>Boolean Negation\<close>






subsubsection\<open>Boolean Conjunction\<close>






subsubsection\<open>Boolean Disjunction\<close>








subsection\<open>Comparison Operators\<close>

subsubsection\<open>Equality and Nonequality\<close>

context
  fixes m n :: \<open>nat\<close>
  fixes h :: \<open>nat \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes x y :: \<open>64 word\<close>
begin





end

subsubsection\<open>Ordering Comparisons\<close>

context
  fixes x y :: \<open>32 word\<close>
begin





end

subsection\<open>Arithmetic Operators\<close>



context
  fixes x y :: \<open>64 word\<close>
begin

end






subsection\<open>Bitwise Operators\<close>




context
  fixes x y :: \<open>64 word\<close>
begin


end






subsection\<open>Operator Precedence and Associativity\<close>

text\<open>
Goldens pin this precedence:
\<open>* / %\<close> (50) > \<open>+ -\<close> (49) > \<open><< >>\<close> (48) > \<open>&\<close> (47) >
\<open>^\<close> (46) > \<open>|\<close> (45) > comparisons (44) > \<open>&&\<close> (43) >
\<open>||\<close> (42); prefix \<open>!\<close> is tightest. Comparisons are non-associative
and covered by the negative tier.
\<close>

subsubsection\<open>Associativity (binary operators are left-associative)\<close>







subsubsection\<open>Cross-tier precedence (the tighter operator groups first)\<close>












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
\<open>Parser_Tests_Negative_Conformance.thy\<close>.
\<close>

subsection\<open>Control Flow - Conditionals\<close>










subsubsection\<open>Rust-Style Optional Semicolons for Block-Like Statements\<close>






lemma \<open>(FunctionBody \<mu>\<open> { () } () \<close>) = (FunctionBody \<lbrakk> { () } () \<rbrakk>)\<close> by (rule refl)
lemma \<open>\<mu>\<open> unsafe { () } () \<close> = \<lbrakk> unsafe { () } () \<rbrakk>\<close> by (rule refl)

subsection\<open>Control Flow - If-Let and Let-Else\<close>

text\<open>
Constructor, tuple, nested, returning, explicit-semicolon, and semicolon-free
rows from this section are executable same-source checks in
\<open>Parser_Test_Expr_Conformance.thy\<close>. Malformed and total-pattern redundancy
boundaries are executable checks in
\<open>Parser_Tests_Negative_Conformance.thy\<close>.
\<close>



subsection\<open>Control Flow - Match Expressions\<close>

context
  fixes x :: \<open>32 word\<close>
begin


end



subsubsection\<open>Wildcard Patterns\<close>

context
  fixes a :: \<open>nat\<close>
begin

end

subsubsection\<open>Variable Binding in Patterns\<close>




subsubsection\<open>Grouped and Irrefutable Patterns\<close>




subsubsection\<open>Slice Patterns\<close>





subsubsection\<open>Extended Rust-Style Pattern Forms\<close>






text\<open>Rust-style pattern binders \<open>ref p\<close> / \<open>ref mut p\<close> are intentionally unsupported (they clash
with the reference syntax). Borrow patterns \<open>&v\<close> / \<open>& mut v\<close> are syntax-only wrappers during
case preparation in both frontends; direct binders still reject them, and type-sensitive semantics
remain deferred.\<close>












subsubsection\<open>Nested Patterns\<close>




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





subsubsection\<open>Struct Patterns\<close>







subsubsection\<open>Struct Expressions\<close>

text\<open>
These frontend goldens are promoted to the checked D-21 matrix in
\<open>Parser_Test_Expr_Conformance.thy\<close>. The active frontend treats labels as syntax-only and lowers each
head as an ordinary call with source-ordered initializers; Rust-correct metadata semantics are deferred
to T-39.
\<close>






subsubsection\<open>Pattern Guards\<close>

context
  fixes x :: \<open>32 word\<close>
begin



end




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

end




context
  fixes x :: \<open>32 word\<close>
begin

end



\<comment>\<open>Nesting depth / breadth: depth-3, depth-4, and inner matches in multiple arms.\<close>
context
  fixes z :: \<open>32 word\<close>
  fixes a3 :: \<open>((32 word option, unit) result, unit) result\<close>
  fixes a4 :: \<open>(((32 word option, unit) result, unit) result, unit) result\<close>
  fixes r2 :: \<open>(32 word option, 32 word option) result\<close>
begin



end

\<comment>\<open>Interaction with other pattern features:
    nested/constructor, tuple, guard, or-patterns; local datatype; and match_switch both ways.\<close>


context
  fixes p q :: \<open>32 word option\<close>
begin

end

context
  fixes ov :: \<open>32 word option\<close>
begin

end




context
  fixes n :: \<open>32 word\<close>
  fixes ov :: \<open>32 word option\<close>
begin


end

subsection\<open>Control Flow - Loops\<close>





context
  fixes x y :: \<open>32 word\<close>
begin

end

context
  fixes n :: nat
begin




end

subsubsection\<open>While Let\<close>

context
  fixes n :: nat
  fixes g :: \<open>'s\<close>
begin




end

subsection\<open>Control Flow - Return\<close>

lemma \<open>\<mu>\<open> return; \<close> = \<lbrakk> return; \<rbrakk>\<close> by (rule refl)
lemma \<open>(FunctionBody \<mu>\<open> ({return;}) == (); return; \<close>) = (FunctionBody \<lbrakk> ({return;}) == (); return; \<rbrakk>)\<close> by (rule refl)



definition test :: \<open>(nat, unit, unit, unit, unit) function_body\<close> where
  \<open>test \<equiv> (FunctionBody \<lbrakk> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<rbrakk>)\<close>
hide_const test



context
  fixes x :: \<open>'s\<close>
  fixes g :: \<open>'s \<Rightarrow> ('a, nat option, unit, unit, unit) function_body\<close>
begin

end




subsection\<open>Control Flow - Error Propagation\<close>

context
  fixes opt :: \<open>nat option\<close>
begin


end

context
  fixes res :: \<open>(nat, bool) result\<close>
begin


end

subsection\<open>Data Structures - Tuples\<close>










subsection\<open>Data Structures - Option and Result\<close>







subsection\<open>Data Structures - Ranges\<close>

context
  fixes x y :: \<open>32 word\<close>
begin



end




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




end

context
  fixes f14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin

end

subsubsection\<open>Method-Style Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
begin


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

lemma \<open>\<mu>\<open> |x| x \<close> = \<lbrakk> |x| x \<rbrakk>\<close> by (rule refl)


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


end

subsubsection\<open>Default Registration (no mapping)\<close>

datatype_record no_override_rec =
  nor_a :: \<open>32 word\<close>
  nor_b :: bool
micro_rust_record no_override_rec

context
  fixes n :: no_override_rec
begin


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













end

context
  fixes msg :: \<open>String.literal\<close>
  and idx :: \<open>32 word\<close>
  and r :: \<open>('a, 'b, 'v) ref\<close>
  and nm :: \<open>String.literal\<close>
begin























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



end

lemma \<open>\<mu>\<open> \<y>\<i>\<e>\<l>\<d> \<close> = \<lbrakk> \<y>\<i>\<e>\<l>\<d> \<rbrakk>\<close> by (rule refl)
lemma \<open>\<mu>\<open> \<y>\<i>\<e>\<l>\<d>; () \<close> = \<lbrakk> \<y>\<i>\<e>\<l>\<d>; () \<rbrakk>\<close> by (rule refl)

subsection\<open>Miscellaneous Features\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin

end

subsubsection\<open>Array and Slice Expression Literals\<close>




lemma \<open>\<mu>\<open> & mut [] \<close> = \<lbrakk> & mut [] \<rbrakk>\<close> by (rule refl)




subsubsection\<open>Vec Macro\<close>

text\<open>
These rows are promoted in \<open>Parser_Test_Expr_Conformance.thy\<close>, including empty,
nested, indexed, parenthesized, and borrow-interaction variants.
\<close>





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



end

subsubsection\<open>Indexing\<close>

context
  fixes xs :: \<open>nat list\<close>
  fixes xss :: \<open>nat list list\<close>
begin



end

subsubsection\<open>Const Bindings\<close>



subsubsection\<open>Scoping and Block Expressions\<close>

context
  fixes x :: \<open>'s\<close>
begin
lemma \<open>(\<mu>\<open> 1 \<close> :: ('s, nat, 'r, 'abort, 'i, 'o) expression) = (\<lbrakk> 1 \<rbrakk> :: ('s, nat, 'r, 'abort, 'i, 'o) expression)\<close> by (rule refl)
end

subsubsection\<open>Sequencing\<close>



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








end

subsection\<open>Disjunctive Patterns\<close>

datatype three_case = CaseA nat | CaseB nat | CaseC



context
  fixes x :: \<open>32 word\<close>
begin

end

context
  fixes x :: \<open>32 word option\<close>
begin

end



context
  fixes x :: \<open>64 word\<close>
begin

end




subsection\<open>Mutable Pattern Destructuring\<close>





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


end

context fixes fl :: flags begin


end

context fixes w :: wrapper begin

end

context fixes ln :: line begin



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



context fixes c :: color begin

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
