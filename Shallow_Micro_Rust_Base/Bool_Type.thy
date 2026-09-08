(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Bool_Type
  imports Core_Expression "HOL-Library.Word" Word_Lib.Bit_Shifts_Infix_Syntax
begin
(*>*)

section\<open>The \<^emph>\<open>Bool\<close> type\<close>

text\<open>This section covers basic material about Boolean-valued expressions in uRust.\<close>

subsection\<open>Truth constants\<close>

text\<open>First, we lift the HOL \<^term>\<open>True\<close> and \<^term>\<open>False\<close> constants into Micro Rust, to model the
equivalent constants in Rust. The truth constant first:\<close>
definition true :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>true \<equiv> literal True\<close>

text\<open>And now falsity:\<close>
definition false :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>false \<equiv> literal False\<close>

subsection\<open>Conditionals\<close>

text\<open>The two-armed conditional is the standard \<^verbatim>\<open>if-then-else\<close> construct from programming languages.
Note that the construct is typed: the \<^emph>\<open>test\<close> expression must evaluate to a Boolean value, and both
the branches must also evaluate to a value of the same type (\<^typ>\<open>'a\<close>):\<close>
definition two_armed_conditional :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>Test expression\<close>
                                     ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>   \<comment> \<open>True-case expression\<close>
                                     ('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>   \<comment> \<open>False-case expression\<close>
                                     ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>two_armed_conditional test this that \<equiv> bind test (\<lambda>test. 
        if test then this else that)\<close>

text\<open>The one-armed conditional is the standard "if-then" \<^emph>\<open>statement\<close> from most programming
languages.  Note, again, that we use HOL's type system to ensure that the expressions are correctly
typed: whilst the \<^emph>\<open>test\<close> expression must evaluate to a Boolean value, the single arm of the
conditional must instead evaluate to \<^typ>\<open>unit\<close> type.  Here \<^term>\<open>skip\<close> is useful, and is used in the
false branch of the conditional to signal nothing changes if the test fails.  We merely add this
as an \<^emph>\<open>abbreviation\<close> for the two-armed conditional, here, meaning that all of the properties that
we established for the two-armed variant, above, automatically apply to this, too:\<close>
abbreviation one_armed_conditional :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>Test expression\<close>
                                     ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow> \<comment> \<open>True-case expression\<close>
                                     ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>one_armed_conditional test this \<equiv> two_armed_conditional test this skip\<close>

definition assert_val :: \<open>bool \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>assert_val v \<equiv> if v then literal () else abort AssertionFailed\<close>

definition assert_ne_val :: \<open>'v \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>assert_ne_val v w \<equiv> assert_val (v \<noteq> w)\<close>

definition assert_eq_val :: \<open>'v \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>assert_eq_val v w \<equiv> assert_val (v = w)\<close>

text\<open>The \<^emph>\<open>assert\<close> construct is an implicit form of conditional which aborts the program is an
assertion fails or continues in the same state:\<close>
definition assert :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>assert test \<equiv> bind test assert_val\<close>

definition assert_ne :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>assert_ne \<equiv> bind2 assert_ne_val\<close>

definition assert_eq :: \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>assert_eq \<equiv> bind2 assert_eq_val\<close>

subsection\<open>Connectives\<close>

subsubsection\<open>Negation\<close>

text\<open>The following is the logical negation operator:\<close>
definition negation :: \<open>('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>negation e \<equiv> bind e (\<lambda>e. literal (\<not>e))\<close>

subsubsection\<open>Conjunction\<close>

text\<open>Next, we define the conjunction of Boolean-valued uRust expressions. As in Rust, the LHS is evaluated
first, and the RHS only evaluated if the LHS evaluates to \<^term>\<open>True\<close>.\<close>

definition urust_conj :: \<open>('s, bool, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>urust_conj e f \<equiv> bind e (\<lambda>e. if e then f else false)\<close>

subsubsection\<open>Disjunction\<close>

text\<open>Next we define the disjunction of Boolean-valued uRust expressions. Again, we evaluate the RHS lazily
depending on the result of the evaluation of the LHS.\<close>

definition urust_disj :: \<open>('s, bool, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>urust_disj e f \<equiv> bind e (\<lambda>r. if r then true else f)\<close>

subsection\<open>Equality and inequality\<close>

text\<open>The following is the equality operator:\<close>
definition urust_eq :: \<open>('s, 'v, bool, 'r, 'abort, 'i, 'o) urust_binop2\<close> where
  \<open>urust_eq \<equiv> bindlift2 (=)\<close>

text\<open>We abbreviate the inequality operator by negating equality:\<close>
definition urust_neq :: \<open>('s, 'v, bool, 'r, 'abort, 'i, 'o) urust_binop2\<close> where
  \<open>urust_neq \<equiv> bindlift2 (\<noteq>)\<close>

subsection\<open>Comparison operators\<close>

definition comp_lt :: \<open>('s, 'v::{ord}, bool, 'r, 'abort, 'i, 'o) urust_binop2\<close> where
  \<open>comp_lt \<equiv> bindlift2 (<)\<close>

definition comp_le :: \<open>('s, 'v::{ord}, bool, 'r, 'abort, 'i, 'o) urust_binop2\<close> where
  \<open>comp_le \<equiv> bindlift2 (\<le>)\<close>

definition comp_gt :: \<open>('s, 'v::{ord}, bool, 'r, 'abort, 'i, 'o) urust_binop2\<close> where
  \<open>comp_gt \<equiv> bindlift2 (>)\<close>

definition comp_ge :: \<open>('s, 'v::{ord}, bool, 'r, 'abort, 'i, 'o) urust_binop2\<close> where
  \<open>comp_ge \<equiv> bindlift2 (\<ge>)\<close>

(*<*)
end
(*>*)