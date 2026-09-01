(* Positive conformance against the inner-syntax frontend. Each `urust_expr_with_check` command
   defines its expression and proves it alpha-equal to `\<lbrakk> src \<rbrakk>` by `refl`. Type
   annotations avoid hidden type variables that `Local_Theory.define` cannot expose cleanly. *)

theory Micro_Rust_Parser_Conformance
  imports Micro_Rust_Parser
begin

section\<open> Numeric literals (Corpus PART I, "Numeric Literals") \<close>

urust_expr_with_check lit_0  \<open> 0 \<close>

urust_expr_with_check lit_1  \<open> 1 \<close>

urust_expr_with_check lit_42 \<open> 42 \<close>

urust_expr_with_check lit_hex \<open> 0xff \<close>


section\<open> Suffixed integer literals (Corpus PART I, "Numeric Ascriptions") \<close>

urust_expr_with_check lit_0_u8  \<open> 0_u8 \<close>

urust_expr_with_check lit_1_u8  \<open> 1_u8 \<close>

urust_expr_with_check lit_0x4_u8 \<open> 0x4_u8 \<close>

urust_expr_with_check lit_0_u16 \<open> 0_u16 \<close>

urust_expr_with_check lit_1_u16 \<open> 1_u16 \<close>

urust_expr_with_check lit_0x12_u16 \<open> 0x12_u16 \<close>

urust_expr_with_check lit_0_u32 \<open> 0_u32 \<close>

urust_expr_with_check lit_1_u32 \<open> 1_u32 \<close>

urust_expr_with_check lit_0x2000_u32 \<open> 0x2000_u32 \<close>

urust_expr_with_check lit_0_u64 \<open> 0_u64 \<close>

urust_expr_with_check lit_1_u64 \<open> 1_u64 \<close>

urust_expr_with_check lit_0x2f0_u64 \<open> 0x2f0_u64 \<close>

urust_expr_with_check lit_0_usize \<open> 0_usize \<close>

urust_expr_with_check lit_1_usize \<open> 1_usize \<close>

urust_expr_with_check lit_0xf_usize \<open> 0xffffffff0_usize \<close>


section\<open> Unit (Corpus PART I, "Unit Literal") \<close>

urust_expr_with_check lit_unit \<open> () \<close>


section\<open> Boolean and string literals \<close>

urust_expr_with_check lit_bool_true \<open> true \<close>

urust_expr_with_check lit_bool_false \<open> false \<close>

urust_expr_with_check lit_string_empty \<open> "" \<close>

urust_expr_with_check lit_string_text \<open> "micro rust" \<close>

urust_expr_with_check lit_string_quote \<open> "say: \"hi\"" \<close>

urust_expr_with_check lit_string_backslash \<open> "a\\b" \<close>


section\<open> Value antiquotation \<open>\<llangle>_\<rrangle>\<close> (Corpus PART I, "HOL Value Injection") \<close>

text\<open> A HOL value lifted to a µRust literal; word widths 8 / 32 / 64, a boolean, and a compound value. \<close>

urust_expr_with_check lit_aq_word \<open> \<llangle>0 :: 32 word\<rrangle> \<close>

urust_expr_with_check ext_aq64 \<open> \<llangle>1 :: 64 word\<rrangle> \<close>

urust_expr_with_check ext_aq8 \<open> \<llangle>255 :: 8 word\<rrangle> \<close>

urust_expr_with_check lit_aq_true \<open> \<llangle>True\<rrangle> \<close>

urust_expr_with_check ext_aqfalse \<open> \<llangle>False\<rrangle> \<close>

urust_expr_with_check lit_aq_some \<open> \<llangle>Some (0 :: nat)\<rrangle> \<close>


section\<open> Expression antiquotation \<open>\<epsilon>\<open>_\<close>\<close> (Corpus PART I, "Boolean Literals") \<close>

text\<open> Passthrough (no \<open>literal\<close> wrapper): the body already denotes an \<open>expression\<close>. \<close>

urust_expr_with_check lit_eaq_true \<open> \<epsilon>\<open>Bool_Type.true\<close> \<close>

urust_expr_with_check aq_nested_value
  \<open> \<llangle> \<lbrakk> \<llangle>1 :: nat\<rrangle> \<rbrakk> \<rrangle> \<close>

urust_expr_with_check aq_nested_expr
  \<open> \<epsilon>\<open> \<lbrakk> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<rbrakk> \<close> \<close>


section\<open> Bare identifiers at value position (dispatch reuse) \<close>

text\<open>
For unregistered HOL constants, \<open>check_term\<close> promotes the parser's bare
\<open>Free\<close> to the same \<open>Const\<close> as the frontend fallback.
\<close>

urust_expr_with_check lit_true  \<open> True \<close>

urust_expr_with_check lit_false \<open> False \<close>

urust_expr_with_check lit_none  \<open> None \<close>

text\<open> A context-fixed free variable (unregistered, non-constant): stays a \<open>Free\<close>, with ctrl-click nav to
its \<open>fixes\<close> (D14). \<close>
context fixes foo :: nat
begin
urust_expr_with_check lit_ctx \<open> foo \<close>
end

text\<open>
Registered names use the existing \<open>urust_dispatch\<close> term-check phase.
\<close>
definition my_backend :: nat where \<open> my_backend \<equiv> 7 \<close>
micro_rust_notation (literal) my_backend ("myReg")

urust_expr_with_check lit_reg \<open> myReg \<close>


section\<open> Sequencing, `let` and `const` bindings \<close>

text\<open>
\<open>e1; e2\<close> lowers to \<open>sequence e1 e2\<close>; a trailing semicolon
sequences with \<open>skip = literal ()\<close>.
\<close>

urust_expr_with_check seq_unit \<open> (); () \<close>

urust_expr_with_check seq_trailing \<open> (); (); \<close>

text\<open>
\<open>let x = e; k\<close> lowers to HOAS \<open>bind e (\<lambda>x. k)\<close>.
Unused binders need a type pin (R1).
\<close>

urust_expr_with_check let_use \<open> let x = 5; x \<close>

urust_expr_with_check let_ab \<open> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<close>

text\<open> \<open>const x = e; k\<close> desugars byte-for-byte as \<open>let\<close> (Corpus PART I "Const Bindings"). \<close>

urust_expr_with_check const_foo \<open> const FOO = \<llangle>5 :: nat\<rrangle>; () \<close>

text\<open>
An enclosing \<open>let\<close> captures \<open>x\<close> inside both direct and nested
antiquotations.
\<close>

urust_expr_with_check let_cap \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<close>

urust_expr_with_check let_cap_deep \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<close>

text\<open>
In the shared pattern grammar, \<open>let _\<close> creates an anonymous hygienic lambda,
not a variable named \<open>_\<close>.
\<close>

urust_expr_with_check let_wild \<open> let _ = \<llangle>5 :: nat\<rrangle>; () \<close>

text\<open> Its \<open>Abs\<close>/\<open>Bound\<close> representation cannot capture an outer binder. \<close>
urust_expr_with_check let_wild_hyg \<open> let uu = \<llangle>5 :: nat\<rrangle>; let _ = \<llangle>7 :: nat\<rrangle>; uu \<close>

text\<open> Refutable \<open>let\<close> patterns and patterns unsupported by a selected match lowering have positioned
rows in \<open>Micro_Rust_Parser_Negative_Conformance.thy\<close>. \<close>

section\<open> Tuple values and irrefutable tuple binders \<close>

text\<open>
Tuple values lower to the frontend's right-nested product ending in \<open>TNil\<close>.
Tuple binders recursively admit names, wildcards, and nested tuples.
\<close>

urust_expr_with_check tuple_value_two
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>) \<close>

urust_expr_with_check tuple_value_four
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>False\<rrangle>) \<close>

urust_expr_with_check tuple_value_nested
  \<open> ((\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>), \<llangle>False\<rrangle>) \<close>

urust_expr_with_check tuple_let_two
  \<open> let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>); x \<close>

urust_expr_with_check tuple_let_three
  \<open> let (x, y, z) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); z \<close>

urust_expr_with_check tuple_const_three
  \<open> const (x, y, z) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<close>

urust_expr_with_check tuple_let_nested
  \<open> let (x, (y, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>)); y \<close>

urust_expr_with_check tuple_const_nested
  \<open> const (x, (_, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>True\<rrangle>, \<llangle>3 :: nat\<rrangle>)); z \<close>

urust_expr_with_check tuple_let_wildcards
  \<open> let (_, y, _) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); y \<close>

urust_expr_with_check tuple_let_shadow
  \<open> let x = \<llangle>0 :: nat\<rrangle>; let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<close>

urust_expr_with_check tuple_let_antiquotation
  \<open> let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); \<llangle>x + y\<rrangle> \<close>


section\<open> References and mutable bindings \<close>

definition parser_reference_fixture ::
  \<open>'v \<Rightarrow> (unit, (unit, unit, 'v) Global_Store.ref, unit, unit, unit) function_body\<close>
  where \<open> parser_reference_fixture \<equiv> undefined \<close>

definition parser_dereference_fixture ::
  \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> (unit, 'v, unit, unit, unit) function_body\<close>
  where \<open> parser_dereference_fixture \<equiv> undefined \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

subsection\<open> Mutable allocation and binders \<close>

urust_expr_with_check mut_scalar
  \<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; x \<close>

urust_expr_with_check mut_capture
  \<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; \<llangle>x\<rrangle> \<close>

urust_expr_with_check mut_shadow
  \<open> let x = \<llangle>1 :: 32 word\<rrangle>; let mut x = \<llangle>2 :: 32 word\<rrangle>; x \<close>

urust_expr_with_check mut_tuple
  \<open> let mut (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<close>

urust_expr_with_check mut_tuple_nested
  \<open> let mut (x, (_, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>True\<rrangle>, \<llangle>3 :: nat\<rrangle>)); z \<close>

urust_expr_with_check mut_borrow_chain
  \<open>
    let mut x = \<llangle>0 :: 32 word\<rrangle>;
    let xr = &x;
    let xw = & mut x;
    xw
  \<close>

subsection\<open> Borrow, dereference, and precedence \<close>

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rr :: \<open>(unit, unit, (unit, unit, 32 word) Global_Store.ref) Global_Store.ref\<close>
    and rb :: \<open>(unit, unit, bool) Global_Store.ref\<close>
    and ropt :: \<open>(unit, unit, 32 word) Global_Store.ref option\<close>
    and rhs :: \<open>32 word\<close>
begin

urust_expr_with_check ref_borrow \<open> &r \<close>

urust_expr_with_check ref_borrow_mut \<open> & mut r \<close>

urust_expr_with_check ref_borrow_group \<open> &(r) \<close>

urust_expr_with_check ref_borrow_block \<open> &{ r } \<close>

urust_expr_with_check ref_borrow_if \<open> &(if true { r } else { r }) \<close>

urust_expr_with_check ref_deref \<open> *r \<close>

urust_expr_with_check ref_double_deref \<open> **rr \<close>

urust_expr_with_check ref_deref_group \<open> *(r) \<close>

urust_expr_with_check ref_deref_block \<open> *{ r } \<close>

urust_expr_with_check ref_deref_if \<open> *(if true { r } else { r }) \<close>

urust_expr_with_check ref_deref_postfix \<open> *ropt? \<close>

urust_expr_with_check ref_deref_add \<open> *r + rhs \<close>

urust_expr_with_check ref_deref_mul \<open> *r * rhs \<close>

urust_expr_with_check ref_deref_mul2 \<open> rhs * *r \<close>

urust_expr_with_check ref_deref_band \<open> *r & rhs \<close>

urust_expr_with_check ref_not_grouped_deref \<open> !(*rb) \<close>

urust_expr_with_check ref_match_scrutinee
  \<open> match_switch *r { 0 \<Rightarrow> true, _ \<Rightarrow> false } \<close>

end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open> Pure-value operators (Corpus PART I: Arithmetic / Bitwise / Comparison / Boolean) \<close>

text\<open>
Binary operators lower to the frontend constants; value antiquotations pin word types.
\<close>

subsection\<open> Arithmetic \<close>

urust_expr_with_check op_add \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_add3 \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> + \<llangle>3 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_sub \<open> \<llangle>5 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_mul \<open> \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_div \<open> \<llangle>6 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_mod \<open> \<llangle>7 :: 32 word\<rrangle> % \<llangle>3 :: 32 word\<rrangle> \<close>

text\<open> Precedence: \<open>*\<close> binds tighter than \<open>+\<close>, so this parses as \<open>a + (b * c)\<close>. \<close>
urust_expr_with_check op_precmul \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close>

subsection\<open> Bitwise and shifts (shift RHS is a \<open>64 word\<close>) \<close>

urust_expr_with_check op_band \<open> \<llangle>6 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_bor \<open> \<llangle>6 :: 32 word\<rrangle> | \<llangle>3 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_bxor \<open> \<llangle>6 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_shl \<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>4 :: 64 word\<rrangle> \<close>

urust_expr_with_check op_shr \<open> \<llangle>16 :: 32 word\<rrangle> >> \<llangle>2 :: 64 word\<rrangle> \<close>

subsection\<open> Comparison (non-associative; word operands, boolean-expression result) \<close>

urust_expr_with_check op_lt \<open> \<llangle>1 :: 32 word\<rrangle> < \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_le \<open> \<llangle>1 :: 32 word\<rrangle> <= \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_gt \<open> \<llangle>2 :: 32 word\<rrangle> > \<llangle>1 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_ge \<open> \<llangle>2 :: 32 word\<rrangle> >= \<llangle>1 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_eq \<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>1 :: 32 word\<rrangle> \<close>

urust_expr_with_check op_ne \<open> \<llangle>1 :: 32 word\<rrangle> != \<llangle>2 :: 32 word\<rrangle> \<close>

subsection\<open> Boolean connectives and unary \<open>!\<close> (all four truth-table rows each; \<open>!!\<close> = \<open>!(!_)\<close>) \<close>

urust_expr_with_check op_and \<open> True && False \<close>

urust_expr_with_check ext_and_tt \<open> True && True \<close>

urust_expr_with_check ext_and_ft \<open> False && True \<close>

urust_expr_with_check and_ff \<open> False && False \<close>

urust_expr_with_check op_or \<open> True || False \<close>

urust_expr_with_check ext_or_tt \<open> True || True \<close>

urust_expr_with_check or_ft \<open> False || True \<close>

urust_expr_with_check ext_or_ff \<open> False || False \<close>

urust_expr_with_check op_not \<open> !True \<close>

urust_expr_with_check ext_notfalse \<open> !False \<close>

urust_expr_with_check op_notnot \<open> !!True \<close>

text\<open> Precedence: \<open>&&\<close> binds tighter than \<open>||\<close>; unary \<open>!\<close> over a parenthesized comparison. \<close>
urust_expr_with_check op_prec \<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>

urust_expr_with_check op_mixed \<open> !(\<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle>) \<close>

subsection\<open> Let-bound variables as operator operands (bound-var use in operator position) \<close>

urust_expr_with_check ext_let_add \<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<close>

urust_expr_with_check ext_let_sub \<open> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<close>

urust_expr_with_check ext_let_mul \<open> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<close>

urust_expr_with_check lop_div \<open> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<close>

urust_expr_with_check lop_mod \<open> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<close>

urust_expr_with_check ext_let_band \<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<close>

urust_expr_with_check lop_bor \<open> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<close>

urust_expr_with_check lop_bxor \<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<close>

urust_expr_with_check ext_let_shl \<open> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<close>

urust_expr_with_check lop_shr \<open> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<close>

urust_expr_with_check ext_let_not \<open> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<close>

urust_expr_with_check ext_let_cmp \<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a < b \<close>

subsection\<open> Context-fixed variables as operator operands \<close>
context fixes m n :: \<open>nat\<close> and x y :: \<open>64 word\<close> and w :: \<open>32 word\<close>
begin

urust_expr_with_check ext_cmp_mn \<open> m == n \<close>

urust_expr_with_check ext_cmp_ne \<open> m != n \<close>

urust_expr_with_check ext_cmp_notmn \<open> !(m == n) \<close>

urust_expr_with_check ord_lt \<open> x < y \<close>

urust_expr_with_check ord_le \<open> x <= y \<close>

urust_expr_with_check ord_gt \<open> x > y \<close>

urust_expr_with_check ord_ge \<open> x >= y \<close>

urust_expr_with_check ext_cmp_w0 \<open> w > \<llangle>0 :: 32 word\<rrangle> \<close>

urust_expr_with_check ext_not_add \<open> !x + y \<close>
  \<comment>\<open> (!x) + y : prefix ! tighter than + \<close>

urust_expr_with_check ext_not_nested \<open> !(!x == x^y) \<close>
end

subsection\<open> Precedence and associativity \<close>

text\<open>
Rows cover every adjacent frontend precedence tier, from \<open>||\<close> (42) through
\<open>* / %\<close> (50); prefix \<open>!\<close> is tightest. The negative harness covers
non-associative comparisons.
\<close>

urust_expr_with_check prec_sub_assoc \<open> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check prec_div_assoc \<open> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check prec_shl_assoc \<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>

urust_expr_with_check prec_and_assoc \<open> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>

urust_expr_with_check prec_or_assoc \<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<close>

urust_expr_with_check prec_add_shl \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
  \<comment>\<open> (a + b) << c : + (49) tighter than << (48) \<close>

urust_expr_with_check prec_shl_and \<open> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
  \<comment>\<open> a & (b << c) : << (48) tighter than & (47) \<close>

urust_expr_with_check prec_and_xor \<open> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close>
  \<comment>\<open> a ^ (b & c) : & (47) tighter than ^ (46) \<close>

urust_expr_with_check prec_xor_or \<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close>
  \<comment>\<open> a | (b ^ c) : ^ (46) tighter than | (45) \<close>

urust_expr_with_check prec_or_cmp \<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<close>
  \<comment>\<open> (a | b) == c : | (45) tighter than == (44) \<close>

urust_expr_with_check prec_cmp_and \<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<close>
  \<comment>\<open> (a == b) && c : == (44) tighter than && (43) \<close>

urust_expr_with_check prec_not_and \<open> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>
  \<comment>\<open> (!a) && b : prefix ! tighter than && \<close>

urust_expr_with_check prec_not_cmp \<open> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<close>
  \<comment>\<open> (!a) == b : prefix ! tighter than == \<close>


section\<open> Block expressions (Corpus "Scoping and Block Expressions") \<close>

text\<open>
Because frontend \<open>_urust_scoping\<close> is the identity (SE:360-362), blocks
erase without a \<open>scoped\<close> wrapper. Their statements sequence with semicolons,
and blocks may be operator operands.
\<close>

urust_expr_with_check blk_lit \<open> { \<llangle>1 :: nat\<rrangle> } \<close>

urust_expr_with_check blk_seq \<open> { (); () } \<close>

urust_expr_with_check blk_let \<open> { let x = \<llangle>5 :: nat\<rrangle>; x } \<close>

urust_expr_with_check ext_blk_bare \<open> { 42 } \<close>

urust_expr_with_check ext_blk_nest \<open> {{ 42 }} \<close>

urust_expr_with_check ext_blk_deep \<open> {{{{{ \<llangle>1 :: nat\<rrangle> }}}}} \<close>

urust_expr_with_check ext_blk_op \<open> { \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> } \<close>

urust_expr_with_check ext_blk_operand_l \<open> { \<llangle>1 :: 32 word\<rrangle> } + \<llangle>2 :: 32 word\<rrangle> \<close>

urust_expr_with_check ext_blk_operand_r \<open> \<llangle>1 :: 32 word\<rrangle> + { \<llangle>2 :: 32 word\<rrangle> } \<close>

urust_expr_with_check ext_not_blk \<open> !{ \<llangle>True\<rrangle> } \<close>


section\<open> \<open>if\<close> / \<open>else\<close> (Corpus "Control Flow - Conditionals") \<close>

text\<open>
Two-armed \<open>if\<close> lowers to \<open>two_armed_conditional\<close>. A missing else becomes
\<open>skip\<close>, so the then-branch must be unit-typed. Else-if nests another
\<open>if\<close> (SE:364-365; SYN:661-662).
\<close>

urust_expr_with_check if_two \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> } \<close>

urust_expr_with_check if_one \<open> if \<llangle>True\<rrangle> { () } \<close>

urust_expr_with_check ext_if_one_bare \<open> if True { () } \<close>

urust_expr_with_check if_elif \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else if \<llangle>False\<rrangle> { \<llangle>2 :: nat\<rrangle> } else { \<llangle>3 :: nat\<rrangle> } \<close>

urust_expr_with_check if_elif2 \<open> if \<llangle>True\<rrangle> { () } else if \<llangle>False\<rrangle> { () } \<close>  \<comment>\<open> else-if, no final else (unit arms) \<close>

urust_expr_with_check ext_elif_word \<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<close>

urust_expr_with_check ext_elif3 \<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<close>

text\<open>
Rows cover compound conditions, nested branches, deep blocks, let RHSs, and sequencing.
\<close>

urust_expr_with_check if_cmp \<open> if \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> { () } else { () } \<close>

urust_expr_with_check if_nest \<open> if \<llangle>True\<rrangle> { if \<llangle>False\<rrangle> { () } else { () } } else { () } \<close>

urust_expr_with_check ext_if_par_cond \<open> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<close>

urust_expr_with_check ext_if_deepblock \<open> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<close>

urust_expr_with_check ext_if_cond \<open> if if \<llangle>True\<rrangle> { \<llangle>True\<rrangle> } else { \<llangle>False\<rrangle> } { () } else { () } \<close>  \<comment>\<open> if-expr as condition \<close>

urust_expr_with_check ext_let_if \<open> let x = if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }; x \<close>

urust_expr_with_check ext_seq_if \<open> { if \<llangle>True\<rrangle> { () } else { () }; () } \<close>


section\<open> Function calls (Corpus "Functions", "Option and Result") \<close>

text\<open>
Calls lower to \<open>funcallN\<close>; callees resolve in NFunction context without a
\<open>literal\<close> wrapper, and arguments are ordinary value expressions. Fixtures use
concrete \<open>64 word\<close> types and \<open>lift_funN\<close> to satisfy R1.
\<close>

definition cf0 :: \<open>(unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf0 \<equiv> lift_fun0 0 \<close>
definition cf1 :: \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf1 \<equiv> lift_fun1 (\<lambda>x. x) \<close>
definition cf2 :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf2 \<equiv> lift_fun2 (+) \<close>
definition cf3 :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf3 \<equiv> lift_fun3 (\<lambda>a b c. a + b + c) \<close>
definition cf4 :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf4 \<equiv> lift_fun4 (\<lambda>a b c d. a + b + c + d) \<close>
definition cf5 :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf5 \<equiv> lift_fun5 (\<lambda>a b c d e. a + b + c + d + e) \<close>

text\<open>
For unregistered global callees, parser and frontend fallbacks resolve the same
\<open>Const\<close>. Rows cover arities 0 through 5 and 14.
\<close>
urust_expr_with_check call0 \<open> cf0() \<close>

urust_expr_with_check call1 \<open> cf1(\<llangle>1 :: 64 word\<rrangle>) \<close>

urust_expr_with_check call2 \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) \<close>

urust_expr_with_check call3 \<open> cf3(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>) \<close>

urust_expr_with_check call4 \<open> cf4(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>, \<llangle>4 :: 64 word\<rrangle>) \<close>

urust_expr_with_check call5 \<open> cf5(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>, \<llangle>4 :: 64 word\<rrangle>, \<llangle>5 :: 64 word\<rrangle>) \<close>

context
  fixes cf14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin
urust_expr_with_check call14 \<open> cf14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<close>
end

text\<open> Nested call \<open>f(g(c), b)\<close>: the inner call is an ordinary argument expression. \<close>
urust_expr_with_check call_nested \<open> cf2(cf1(\<llangle>1 :: 64 word\<rrangle>), \<llangle>2 :: 64 word\<rrangle>) \<close>

text\<open>
Registered callees use NFunction dispatch. Rows cover a local notation and the
\<open>Some\<close>, \<open>Ok\<close>, and \<open>Err\<close> call notations.
\<close>
micro_rust_notation (call) cf1 ("regCall")
urust_expr_with_check call_reg \<open> regCall(\<llangle>3 :: 64 word\<rrangle>) \<close>

urust_expr_with_check call_some \<open> Some(\<llangle>42 :: nat\<rrangle>) \<close>

urust_expr_with_check call_ok \<open> Ok(\<llangle>42 :: nat\<rrangle>) \<close>

urust_expr_with_check call_err \<open> Err(\<llangle>42 :: nat\<rrangle>) \<close>

text\<open>
A let-bound callee uses lexical scope without dispatch or a \<open>literal\<close> wrapper.
\<close>
urust_expr_with_check call_letbound \<open> let h = \<llangle>cf1\<rrangle>; h(\<llangle>4 :: 64 word\<rrangle>) \<close>

text\<open>
Context-fixed, function-typed callees remain \<open>Free\<close>. Rows cover word, unit,
and boolean arguments.
\<close>
context fixes g :: \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
begin
urust_expr_with_check call_ctx \<open> g(\<llangle>5 :: 64 word\<rrangle>) \<close>
end

context
  fixes uf :: \<open>unit \<Rightarrow> (unit, unit, unit, unit, unit) function_body\<close>
  fixes ug :: \<open>unit \<Rightarrow> bool \<Rightarrow> (unit, unit, unit, unit, unit) function_body\<close>
begin
urust_expr_with_check call_funit \<open> uf(()) \<close>

urust_expr_with_check call_gunitbool \<open> ug((), True) \<close>
end


section\<open> Method calls (Corpus "Method-Style Calls") \<close>

text\<open>
Method syntax prepends the receiver to a plain NFunction call (SE:380-381,
416-417). It binds tighter than operators. Bare field access uses the composable
NField/lens postfix added below (D37).
\<close>

urust_expr_with_check mcall0 \<open> \<llangle>5 :: 64 word\<rrangle>.cf1() \<close>

urust_expr_with_check mcall1 \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>) \<close>

text\<open>
The inclusive \<open>funcall14\<close> limit permits 13 explicit method arguments because
the receiver is prepended as the first lowered argument.
\<close>
context
  fixes receiver :: nat
  fixes m14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin
urust_expr_with_check mcall13 \<open> receiver.m14(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<close>
end

text\<open> Rows cover call-result receivers, method chains, and operator precedence. \<close>
urust_expr_with_check mcall_on_call \<open> cf1(\<llangle>1 :: 64 word\<rrangle>).cf1() \<close>

urust_expr_with_check mcall_chain \<open> \<llangle>5 :: 64 word\<rrangle>.cf1().cf1() \<close>

urust_expr_with_check mcall_operand \<open> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> \<close>

text\<open> Context-fixed methods are tested alone and in an equality condition. \<close>
context fixes m n :: \<open>nat\<close> and h :: \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
begin
urust_expr_with_check mcall_ctx \<open> m.h() \<close>

urust_expr_with_check mcall_if \<open> if m.h() == n { m } else { n } \<close>
end


section\<open> Postfix propagation and field access \<close>

subsection\<open> Error propagation \<close>

context
  fixes opt :: \<open>nat option\<close>
  fixes res :: \<open>(nat, bool) result\<close>
begin
urust_expr_with_check postfix_option \<open> opt? \<close>

urust_expr_with_check postfix_result \<open> res? \<close>

urust_expr_with_check postfix_block \<open> { opt }? \<close>

urust_expr_with_check postfix_parenthesized_if \<open> (if true { opt } else { opt })? \<close>
end

context
  fixes next_opt :: \<open>(unit, nat option, unit, unit, unit) function_body\<close>
  fixes nested_opt :: \<open>nat option option\<close>
begin
urust_expr_with_check postfix_after_call \<open> next_opt()? \<close>

urust_expr_with_check postfix_repeated \<open> nested_opt?? \<close>
end

context
  fixes flag :: \<open>bool option\<close>
  fixes lhs :: \<open>64 word option\<close>
  fixes rhs :: \<open>64 word\<close>
begin
urust_expr_with_check postfix_unary_precedence \<open> !flag? \<close>

urust_expr_with_check postfix_binary_precedence \<open> lhs? + rhs \<close>
end

subsection\<open> Field registrations and composition \<close>

datatype_record postfix_default =
  postfix_default_value :: \<open>64 word\<close>
micro_rust_record postfix_default

datatype_record postfix_inner =
  postfix_inner_value :: \<open>64 word\<close>
  postfix_inner_secondary :: \<open>64 word\<close>
micro_rust_record postfix_inner
  (postfix_inner_value = "value",
   postfix_inner_secondary = "secondary")

datatype_record postfix_outer =
  postfix_outer_inner :: postfix_inner
  postfix_outer_optional :: \<open>postfix_inner option\<close>
micro_rust_record postfix_outer
  (postfix_outer_inner = "inner",
   postfix_outer_optional = "optional")

datatype_record postfix_dual =
  postfix_dual_pick :: \<open>64 word\<close>
micro_rust_record postfix_dual (postfix_dual_pick = "pick")

definition postfix_pick_method ::
  \<open>postfix_dual \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> postfix_pick_method \<equiv> lift_fun1 postfix_dual_pick \<close>
micro_rust_notation (call) postfix_pick_method ("pick")

definition postfix_to_value ::
  \<open>postfix_inner \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> postfix_to_value \<equiv> lift_fun1 postfix_inner_value \<close>
micro_rust_notation (call) postfix_to_value ("to_value")

context
  fixes d :: postfix_default
  fixes i :: postfix_inner
  fixes self :: postfix_outer
  fixes dual :: postfix_dual
begin
urust_expr_with_check postfix_field_default \<open> d.postfix_default_value \<close>

urust_expr_with_check postfix_field_renamed \<open> i.value \<close>

urust_expr_with_check postfix_field_nested \<open> self.inner.value \<close>

urust_expr_with_check postfix_field_then_propagate \<open> self.optional? \<close>

urust_expr_with_check postfix_propagate_then_field \<open> self.optional?.secondary \<close>

urust_expr_with_check postfix_field_disambiguation \<open> dual.pick \<close>

urust_expr_with_check postfix_method_disambiguation \<open> dual.pick() \<close>
end

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context fixes rp :: \<open>(unit, unit, postfix_inner) Global_Store.ref\<close>
begin
urust_expr_with_check ref_deref_field_postfix \<open> *rp.value \<close>
end

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open> Explicit places and simple assignment \<close>

definition parser_update_fixture ::
  \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
    (unit, unit, unit, unit, unit) function_body\<close>
  where \<open> parser_update_fixture \<equiv> undefined \<close>

definition parser_assign_add_fixture ::
  \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> 'w \<Rightarrow>
    (unit, unit, unit, unit, unit) function_body\<close>
  where \<open> parser_assign_add_fixture \<equiv> undefined \<close>

definition assignment_sink ::
  \<open>unit \<Rightarrow> (unit, unit, unit, unit, unit) function_body\<close>
  where \<open> assignment_sink \<equiv> lift_fun1 (\<lambda>_. ()) \<close>

definition assignment_shadow_backend ::
  \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  where \<open> assignment_shadow_backend \<equiv> undefined \<close>

micro_rust_notation (literal) assignment_shadow_backend ("assignmentPlace")

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture
adhoc_overloading assign_add_const \<rightleftharpoons> parser_assign_add_fixture

subsection\<open> Identifier, grouping, and dereference places \<close>

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rhs other :: \<open>32 word\<close>
begin

urust_expr_with_check assign_identifier \<open> r = rhs \<close>

urust_expr_with_check assign_grouped \<open> (r) = rhs \<close>

urust_expr_with_check assign_nested_groups \<open> (((r))) = rhs \<close>

urust_expr_with_check assign_deref \<open> *r = rhs \<close>

urust_expr_with_check assign_grouped_deref \<open> (*r) = rhs \<close>

urust_expr_with_check assign_deref_group \<open> *(r) = rhs \<close>

urust_expr_with_check assign_rhs_operator \<open> r = rhs + other \<close>

urust_expr_with_check assign_block_rhs \<open> r = { rhs } \<close>

urust_expr_with_check assign_sequence \<open> r = rhs; *r \<close>

urust_expr_with_check assign_block \<open> { r = rhs; *r } \<close>

urust_expr_with_check assign_call_argument \<open> assignment_sink(r = rhs) \<close>

urust_expr_with_check assign_lexical_shadow
  \<open> let assignmentPlace = \<llangle>r\<rrangle>; assignmentPlace = rhs \<close>

end

urust_expr_with_check assign_notation_target \<open> assignmentPlace = \<llangle>7 :: 32 word\<rrangle> \<close>

subsection\<open> Associativity and composition \<close>

context
  fixes outer :: \<open>(unit, unit, unit) Global_Store.ref\<close>
    and inner :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rhs :: \<open>32 word\<close>
begin

urust_expr_with_check assign_right_associative \<open> outer = inner = rhs \<close>

end

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and lhs rhs :: \<open>32 word\<close>
    and flag :: bool
begin

urust_expr_with_check assign_if_branches
  \<open> if flag { r = lhs } else { r = rhs } \<close>

urust_expr_with_check assign_match_arms
  \<open> match flag { true \<Rightarrow> r = lhs, false \<Rightarrow> r = rhs } \<close>

urust_expr_with_check assign_control_rhs
  \<open> r = (if flag { lhs } else { rhs }) \<close>

urust_expr_with_check assign_mutable_binding
  \<open> let mut x = lhs; *x = rhs; *x \<close>

end

subsection\<open> Field places \<close>

context
  fixes rp :: \<open>(unit, unit, postfix_outer) Global_Store.ref\<close>
    and field_value :: \<open>64 word\<close>
begin

urust_expr_with_check assign_field \<open> rp.inner = \<llangle>undefined :: postfix_inner\<rrangle> \<close>

urust_expr_with_check assign_field_chain \<open> rp.inner.value = field_value \<close>

urust_expr_with_check assign_grouped_deref_field \<open> (*rp.inner.value) = field_value \<close>

urust_expr_with_check assign_deref_field_chain \<open> *rp.inner.value = field_value \<close>

end

section\<open> Compound assignment \<close>

subsection\<open> Supported operators and places \<close>

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rhs other :: \<open>32 word\<close>
begin

urust_expr_with_check compound_add_identifier \<open> r += rhs \<close>

urust_expr_with_check compound_sub_grouped \<open> (r) -= rhs \<close>

urust_expr_with_check compound_mul_deref \<open> *r *= rhs \<close>

urust_expr_with_check compound_mod_identifier \<open> r %= rhs \<close>

urust_expr_with_check compound_and_identifier \<open> r &= rhs \<close>

urust_expr_with_check compound_or_identifier \<open> r |= rhs \<close>

urust_expr_with_check compound_xor_identifier \<open> r ^= rhs \<close>

urust_expr_with_check compound_rhs_precedence \<open> r -= rhs * other \<close>

urust_expr_with_check compound_block_rhs \<open> r ^= { rhs } \<close>

end

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and shift :: \<open>64 word\<close>
begin

urust_expr_with_check compound_shift_left \<open> r <<= shift \<close>

urust_expr_with_check compound_shift_right \<open> r >>= shift \<close>

end

context
  fixes rp :: \<open>(unit, unit, postfix_outer) Global_Store.ref\<close>
    and field_value :: \<open>64 word\<close>
begin

urust_expr_with_check compound_field_chain \<open> rp.inner.value %= field_value \<close>

end

subsection\<open> Mutable locals, associativity, and control-flow boundaries \<close>

context
  fixes a b :: \<open>32 word\<close>
begin

urust_expr_with_check compound_mutable_local
  \<open> let mut x = a; x += b; *x \<close>

end

context
  fixes outer :: \<open>(unit, unit, unit) Global_Store.ref\<close>
    and inner :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rhs :: \<open>32 word\<close>
begin

urust_expr_with_check compound_simple_then_compound \<open> outer = inner -= rhs \<close>

urust_expr_with_check compound_then_simple \<open> outer += inner = rhs \<close>

urust_expr_with_check compound_right_associative \<open> outer += inner += rhs \<close>

end

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and lhs rhs :: \<open>32 word\<close>
    and flag :: bool
begin

urust_expr_with_check compound_grouped_control_rhs
  \<open> r |= (if flag { lhs } else { rhs }) \<close>

end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture
no_adhoc_overloading assign_add_const \<rightleftharpoons> parser_assign_add_fixture


section\<open> Cross-feature robustness (calls / methods x operators / control-flow / binders) \<close>

text\<open>
Cross-feature rows stress call/method precedence, binder capture in arguments and
receivers, and deep nesting. Concrete callees and pinned arguments satisfy R1.
\<close>

subsection\<open> Calls as / with operators (precedence) \<close>

urust_expr_with_check rc_arg_op \<open> cf1(\<llangle>1 :: 64 word\<rrangle> + \<llangle>2 :: 64 word\<rrangle>) \<close>

urust_expr_with_check rc_call_plus_call \<open> cf1(\<llangle>10 :: 64 word\<rrangle>) + cf1(\<llangle>20 :: 64 word\<rrangle>) \<close>

urust_expr_with_check rc_call_times \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) * \<llangle>3 :: 64 word\<rrangle> \<close>

urust_expr_with_check rc_bang_cmp \<open> !(cf1(\<llangle>1 :: 64 word\<rrangle>) == cf1(\<llangle>2 :: 64 word\<rrangle>)) \<close>

subsection\<open> Calls in control-flow and binder positions \<close>

urust_expr_with_check rc_call_let \<open> let r = cf1(\<llangle>7 :: 64 word\<rrangle>); r \<close>

urust_expr_with_check rc_call_if \<open> if \<llangle>True\<rrangle> { cf0() } else { cf1(\<llangle>1 :: 64 word\<rrangle>) } \<close>

urust_expr_with_check rc_call_block \<open> { cf0(); cf1(\<llangle>1 :: 64 word\<rrangle>) } \<close>

urust_expr_with_check rc_if_arg \<open> cf1((if \<llangle>True\<rrangle> { \<llangle>1 :: 64 word\<rrangle> } else { \<llangle>2 :: 64 word\<rrangle> })) \<close>

subsection\<open> Deep argument nesting \<close>

urust_expr_with_check rc_deep3 \<open> cf1(cf1(cf1(\<llangle>1 :: 64 word\<rrangle>))) \<close>

urust_expr_with_check rc_two_call_args \<open> cf2(cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>), cf1(\<llangle>3 :: 64 word\<rrangle>)) \<close>

subsection\<open> Binder capture inside call / method arguments \<close>

urust_expr_with_check rc_cap_args \<open> let a = \<llangle>10 :: 64 word\<rrangle>; let b = \<llangle>20 :: 64 word\<rrangle>; cf2(\<llangle>a\<rrangle>, \<llangle>b\<rrangle>) \<close>

urust_expr_with_check rc_mcall_let_recv \<open> let x = \<llangle>5 :: 64 word\<rrangle>; x.cf1() \<close>

subsection\<open> Method calls x nesting / precedence \<close>

urust_expr_with_check rc_mchain2 \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>).cf1() \<close>

urust_expr_with_check rc_m_on_call \<open> cf1(\<llangle>1 :: 64 word\<rrangle>).cf2(\<llangle>2 :: 64 word\<rrangle>) \<close>

urust_expr_with_check rc_m_call_arg \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(cf1(\<llangle>2 :: 64 word\<rrangle>)) \<close>

urust_expr_with_check rc_m_prec \<open> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> * \<llangle>3 :: 64 word\<rrangle> \<close>


section\<open> Match \<open>match_switch\<close> (Corpus "Match Expressions" -- numeric/wildcard, first-order) \<close>

text\<open>
\<open>match_switch\<close> binds the scrutinee into \<open>ncase_selector\<close> (D26).
Numerals become \<open>Some\<close> keys, wildcard becomes \<open>None\<close>, and or-patterns
duplicate the key/body pair. It is first-order; constant and path keys remain deferred.
\<close>

urust_expr_with_check msw_lit \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

context fixes n :: nat
begin

text\<open> Multiple numeral arms + wildcard fall-through (context-fixed scrutinee). \<close>
urust_expr_with_check msw_multi \<open> match_switch n { 0 \<Rightarrow> \<llangle>False\<rrangle>, 1 \<Rightarrow> \<llangle>True\<rrangle>, 2 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<close>

urust_expr_with_check msw_hex \<open> match_switch n { 0xff \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

text\<open> Or-pattern: \<open>1 | 2 | 3\<close> expands to three \<open>(Some _, body)\<close> pairs sharing the arm body. \<close>
urust_expr_with_check msw_or \<open> match_switch n { 1 | 2 | 3 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

text\<open>
Rows cover a let RHS and statement position, where explicit \<open>match_switch\<close>
requires a semicolon.
\<close>
urust_expr_with_check msw_let \<open> let r = match_switch n { 0 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }; r \<close>

urust_expr_with_check msw_stmt \<open> match_switch n { 0 \<Rightarrow> () , _ \<Rightarrow> () } ; () \<close>
end


section\<open> Match \<open>match_case\<close> (Corpus "Match Expressions" -- binding patterns, D27) \<close>

text\<open>
\<open>match_case\<close> builds the Ctr_Sugar skeleton that \<open>Case_Translation\<close>
folds to the frontend term (D27). These baseline rows cover wildcard, variable,
nullary-constructor, and single-level constructor patterns. Later sections exercise
recursive, guarded, value, tuple, alias, range, slice, and struct patterns.
\<close>

datatype pair2 = P2 nat nat   \<comment>\<open> a 2-ary constructor, to exercise the multi-binder (leftmost-outermost) arm path \<close>

context fixes x :: \<open>nat option\<close> and xr :: \<open>(nat, nat) result\<close> and p :: \<open>pair2\<close>
begin

text\<open> Option: variable binder + nullary constructor. \<close>
urust_expr_with_check mc_opt \<open> match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 } \<close>

text\<open> Result: two variable-binding constructors. \<close>
urust_expr_with_check mc_res \<open> match_case xr { Ok(v) \<Rightarrow> v, Err(e) \<Rightarrow> e } \<close>

text\<open> Wildcard \<open>_\<close> arm. \<close>
urust_expr_with_check mc_wild \<open> match_case x { Some(y) \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>

text\<open> Constructor with a wildcard argument \<open>Some(_)\<close>. \<close>
urust_expr_with_check mc_cwild \<open> match_case x { Some(_) \<Rightarrow> \<llangle>True\<rrangle>, None \<Rightarrow> \<llangle>False\<rrangle> } \<close>

text\<open> Single-level 2-ary constructor: two binders (leftmost outermost). \<close>
urust_expr_with_check mc_pair \<open> match_case p { P2(a, b) \<Rightarrow> a } \<close>

urust_expr_with_check mc_var \<open> match_case x { y \<Rightarrow> y } \<close>

urust_expr_with_check mc_pair_left \<open> match_case p { P2(a, _) \<Rightarrow> a } \<close>

urust_expr_with_check mc_pair_right \<open> match_case p { P2(_, b) \<Rightarrow> b } \<close>

urust_expr_with_check mc_shadow
  \<open> let y = \<llangle>7 :: nat\<rrangle>; match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> y } \<close>

text\<open> As a value (let-RHS). \<close>
urust_expr_with_check mc_let \<open> let r = match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 }; r \<close>

text\<open> As a \<open>;\<close>-terminated statement (the \<open>match_case\<close> keyword has no no-\<open>;\<close> form, like \<open>match_switch\<close>). \<close>
urust_expr_with_check mc_stmt \<open> match_case x { Some(_) \<Rightarrow> () , None \<Rightarrow> () } ; () \<close>

subsection\<open> Anonymous-binder hygiene \<close>

text\<open>
Wildcards and desugaring binders use \<open>Abs\<close>/\<open>Bound\<close>, preventing name capture.
Rows cover wildcard arms, constructor slots, differing types, and sibling binders.
\<close>

urust_expr_with_check mc_hyg_wild \<open> let uu = \<llangle>Some 5 :: nat option\<rrangle>; match_case x { _ \<Rightarrow> uu } \<close>

text\<open> Wildcard constructor argument. \<close>
urust_expr_with_check mc_hyg_ctor_arg \<open> let uu = \<llangle>7 :: nat\<rrangle>; match_case x { Some(_) \<Rightarrow> uu, None \<Rightarrow> uu } \<close>

text\<open> Scrutinee and result types differ. \<close>
urust_expr_with_check mc_hyg_typed \<open> let uu = \<llangle>7 :: nat\<rrangle>; match_case x { _ \<Rightarrow> uu } \<close>

text\<open> Source binder with the former scrutinee hint name. \<close>
urust_expr_with_check mc_hyg_scrut \<open> let anon_case = \<llangle>7 :: nat\<rrangle>; match_case x { Some(y) \<Rightarrow> anon_case, None \<Rightarrow> anon_case } \<close>

text\<open> Named and anonymous sibling slots. \<close>
urust_expr_with_check mc_hyg_sibling \<open> match_case p { P2(uu, _) \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<close>

end


section\<open> Rich case-pattern lowering \<close>

text\<open>
Case arms are normalized in stages: recursive disjunction expansion, recursive
constructor compilation, and ordered guard fall-through. Case numerals remain
frontend-fidelity rejections. These rows replace the four former D-7 negative tests.
\<close>

subsection\<open> Former D-7 rejection rows \<close>

urust_expr_with_check rich_explicit_nested
  \<open> match_case \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<close>

urust_expr_with_check rich_explicit_or
  \<open> match_case \<llangle>Some (0 :: nat)\<rrangle> { Some(_) | None \<Rightarrow> () } \<close>

urust_expr_with_check rich_bare_nested
  \<open> match \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<close>

urust_expr_with_check rich_bare_or
  \<open> match \<llangle>Some (0 :: nat)\<rrangle> { Some(_) | None \<Rightarrow> () } \<close>

subsection\<open> Guards \<close>

context fixes x :: \<open>32 word option\<close>
begin

urust_expr_with_check rich_guard_scope
  \<open> let floor = \<llangle>0 :: 32 word\<rrangle>; match x { Some(y) if y > floor \<Rightarrow> y, _ \<Rightarrow> floor } \<close>

urust_expr_with_check rich_guard_fallthrough
  \<open> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_guard_multi_fallthrough
  \<open> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) if False \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>, Some(y) if True \<Rightarrow> y, _ \<Rightarrow> \<llangle>3 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_guard_intervening_pattern
  \<open> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, None \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, _ \<Rightarrow> \<llangle>3 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_guard_wild_fallthrough
  \<open> match x { _ if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_guard_if
  \<open> match x { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_guard_match
  \<open> match x { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

end

subsection\<open> Disjunction expansion \<close>

datatype rich_case = RMA "32 word" | RMB "32 word" | RMD "32 word" | RMC
datatype rich_leaf = RLA | RLB | RLC
datatype rich_pair = RP rich_leaf rich_leaf

context fixes r :: rich_case and ro :: \<open>rich_case option\<close> and rp :: rich_pair
begin

urust_expr_with_check rich_or_top
  \<open> match_case r { RMA(x) | RMB(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_or_three_top
  \<open> match_case r { RMA(x) | RMB(x) | RMD(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_or_nested
  \<open> match_case ro { Some(RMA(x) | RMB(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_or_guarded
  \<open> match r { RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_expr_with_check rich_or_nested_slot
  \<open> match_case rp { RP(RLA, RLA | RLB) \<Rightarrow> True, _ \<Rightarrow> False } \<close>

urust_expr_with_check rich_or_three_nested_slot
  \<open> match_case rp { RP(RLA, RLA | RLB | RLC) \<Rightarrow> True, _ \<Rightarrow> False } \<close>

urust_expr_with_check rich_or_three_guard_fallthrough
  \<open> match r { RMA(x) | RMB(x) | RMD(x) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, RMA(x) | RMB(x) | RMD(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

end

context fixes outer :: nat and x :: \<open>nat option\<close>
begin
urust_expr_with_check rich_or_independent
  \<open> match_case x { Some(outer) | None \<Rightarrow> outer } \<close>
end

subsection\<open> Recursive constructors and capture \<close>

context
  fixes deep2 :: \<open>nat option option\<close>
  fixes deep3 :: \<open>nat option option option\<close>
  fixes mixed :: \<open>pair2 option\<close>
begin

urust_expr_with_check rich_depth_two
  \<open> match_case deep2 { Some(Some(y)) \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check rich_depth_three
  \<open> match_case deep3 { Some(Some(Some(_))) \<Rightarrow> True, _ \<Rightarrow> False } \<close>

urust_expr_with_check rich_mixed_slots
  \<open> match_case mixed { Some(P2(_, y)) \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check rich_antiquotation_capture
  \<open> match_case deep2 { Some(Some(y)) \<Rightarrow> \<llangle>y\<rrangle>, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check rich_shadow
  \<open> let y = \<llangle>7 :: nat\<rrangle>; match_case deep2 { Some(Some(y)) \<Rightarrow> \<llangle>y\<rrangle>, _ \<Rightarrow> y } \<close>

end

subsection\<open> Numeric switch boundary \<close>

text\<open>
Bare numeric matches continue to select switch lowering. Explicit or constructor-nested
case numerals are pinned as frontend-fidelity rejections in the negative theory.
\<close>

context fixes n :: nat
begin

urust_expr_with_check rich_numeric_switch
  \<open> match n { 2 \<Rightarrow> True, _ \<Rightarrow> False } \<close>

end

section\<open> Value patterns \<close>

text\<open>
Boolean, string, and value-antiquotation patterns lower through equality guards.
Nested forms reproduce the frontend's generated argument binding, nested match guard,
and RHS extraction wrapper.
\<close>

datatype value_pat_pair = VPP bool String.literal | VPOther

context
  fixes b :: bool
  fixes s :: String.literal
  fixes n :: nat
  fixes ob :: \<open>bool option\<close>
  fixes on :: \<open>nat option\<close>
begin

urust_expr_with_check value_pat_bool
  \<open> match b { true \<Rightarrow> "yes", false \<Rightarrow> "no" } \<close>

urust_expr_with_check value_pat_string_explicit
  \<open> match_case s { "ok" \<Rightarrow> True, _ \<Rightarrow> False } \<close>

urust_expr_with_check value_pat_antiquotation
  \<open> match n { \<llangle>(2 :: nat)\<rrangle> \<Rightarrow> True, _ \<Rightarrow> False } \<close>

urust_expr_with_check value_pat_nested_constructor
  \<open> match ob { Some(true) \<Rightarrow> False, Some(false) \<Rightarrow> True, None \<Rightarrow> False } \<close>

urust_expr_with_check value_pat_disjunction
  \<open> match b { true | false \<Rightarrow> True } \<close>

urust_expr_with_check value_pat_source_guard
  \<open> match b { true if False \<Rightarrow> True, _ \<Rightarrow> False } \<close>

urust_expr_with_check value_pat_capture
  \<open> let needle = \<llangle>2 :: nat\<rrangle>; match on { Some(\<llangle>needle\<rrangle>) \<Rightarrow> needle, _ \<Rightarrow> 0 } \<close>

end

urust_expr_with_check value_pat_nested_tuple
  \<open> match_case \<llangle>(True, (Some False, TNil))\<rrangle> {
      (true, Some(x)) \<Rightarrow> x, _ \<Rightarrow> False } \<close>

urust_expr_with_check value_pat_guard_order
  \<open> match \<llangle>VPP True (String.implode ''ok'')\<rrangle> {
      VPP(true, "ok") if True \<Rightarrow> True, _ \<Rightarrow> False } \<close>

section\<open> Tuple case patterns \<close>

text\<open>
Tuple case patterns lower to generated \<open>Pair\<close>/\<open>TNil\<close> trees. They compose
recursively with constructors and disjunction expansion.
\<close>

urust_expr_with_check tuple_match_explicit
  \<open> match_case \<llangle>(1 :: nat, (True, TNil))\<rrangle> { (x, _) \<Rightarrow> x } \<close>

urust_expr_with_check tuple_match_bare
  \<open> match \<llangle>(1 :: nat, (True, TNil))\<rrangle> { (_, y) \<Rightarrow> y } \<close>

urust_expr_with_check tuple_match_three
  \<open> match_case \<llangle>(1 :: nat, (True, (2 :: nat, TNil)))\<rrangle> { (x, _, z) \<Rightarrow> z } \<close>

urust_expr_with_check tuple_match_nested
  \<open> match_case \<llangle>(1 :: nat, ((True, (2 :: nat, TNil)), TNil))\<rrangle> { (x, (_, z)) \<Rightarrow> z } \<close>

urust_expr_with_check tuple_match_in_constructor
  \<open> match_case \<llangle>Some (1 :: nat, (True, TNil))\<rrangle> { Some((x, y)) \<Rightarrow> x, None \<Rightarrow> 0 } \<close>

urust_expr_with_check tuple_match_constructor_inside
  \<open> match_case \<llangle>(Some (1 :: nat), (True, TNil))\<rrangle> { (Some(x), _) \<Rightarrow> x, (None, _) \<Rightarrow> 0 } \<close>

urust_expr_with_check tuple_match_or_inside
  \<open> match_case \<llangle>(Some (1 :: nat), (True, TNil))\<rrangle> { (Some(_) | None, y) \<Rightarrow> y } \<close>


section\<open> Advanced pattern parity \<close>

subsection\<open> Grouped, borrow, alias, and range patterns \<close>

urust_expr_with_check adv_grouped
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { (Some(x)) \<Rightarrow> x, (_) \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_grouped_let \<open> let (x) = \<llangle>7 :: nat\<rrangle>; x \<close>

urust_expr_with_check adv_grouped_switch
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { (1) \<Rightarrow> \<llangle>True\<rrangle>, (_) \<Rightarrow> \<llangle>False\<rrangle> } \<close>

urust_expr_with_check adv_borrow
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(&x) \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_borrow_mut
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(& mut x) \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_alias
  \<open> match \<llangle>Some (7 :: nat)\<rrangle> { whole @ Some(v) \<Rightarrow> whole, _ \<Rightarrow> None } \<close>

urust_expr_with_check adv_alias_nested
  \<open> match \<llangle>Some (Some (7 :: nat))\<rrangle> { Some(whole @ Some(v)) \<Rightarrow> \<llangle>whole\<rrangle>, _ \<Rightarrow> \<llangle>None\<rrangle> } \<close>

urust_expr_with_check adv_alias_shadow
  \<open> let whole = \<llangle>None :: nat option\<rrangle>; match \<llangle>Some (7 :: nat)\<rrangle> { whole @ Some(v) \<Rightarrow> whole, _ \<Rightarrow> whole } \<close>

urust_expr_with_check adv_range_exclusive
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(5..7) \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<close>

urust_expr_with_check adv_range_inclusive
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(5..=7) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

urust_expr_with_check adv_range_guard
  \<open> match_case \<llangle>Some (6 :: nat)\<rrangle> { Some(5..=7) if True \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Some(5..=7) \<Rightarrow> \<llangle>2 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>3 :: nat\<rrangle> } \<close>

urust_expr_with_check adv_range_nested
  \<open> match \<llangle>Some (6 :: nat)\<rrangle> { Some(5..=7) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

subsection\<open> Slice patterns \<close>

text\<open>
The old frontend already accepts a terminal comma in slice patterns because its
slice-argument grammar has an empty tail. These same-source rows cover ordinary,
rest, and recursively nested slice lists.
\<close>

urust_expr_with_check trailing_slice_closed
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, y,] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check trailing_slice_rest
  \<open> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [head, ..,] \<Rightarrow> head, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check trailing_slice_nested
  \<open> match \<llangle>[[1 :: nat, 2], [3]]\<rrangle> { [[x, y,], [z,],] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_slice_empty
  \<open> match \<llangle>([] :: nat list)\<rrangle> { [] \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

urust_expr_with_check adv_slice_closed
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, y] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_slice_prefix
  \<open> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_slice_suffix
  \<open> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_slice_middle
  \<open> match \<llangle>[1 :: nat, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> z, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_slice_short
  \<open> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

urust_expr_with_check adv_slice_nested
  \<open> match \<llangle>Some [1 :: nat, 2, 3]\<rrangle> { Some([a, .., z]) \<Rightarrow> z, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_slice_guard_or
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, ..] | [] if True \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>

subsection\<open> Struct patterns \<close>

datatype adv_struct_fixture =
  AdvStruct (adv_left: nat) (adv_right: nat)
| AdvOther

datatype adv_nested_fixture =
  AdvNested (adv_option: "nat option") (adv_values: "nat list")

datatype_record adv_datatype_record =
  adv_dr_left :: nat
  adv_dr_right :: nat

record adv_record_fixture =
  adv_rec_left :: nat
  adv_rec_right :: nat

text\<open>
This direct resolver regression checks that an HOL record uses the record-specific result variant and
contains only its two source-visible fields, rather than generic constructor metadata or a synthetic
extension slot.
\<close>

ML\<open>
val _ =
  let
    val wildcard = URust_AST.P_Wild Position.none
    val fields =
      [URust_AST.SF_Field ("adv_rec_left", Position.none, wildcard),
       URust_AST.SF_Field ("adv_rec_right", Position.none, wildcard)]
  in
    (case URust_Resolution.resolve_struct_pattern
        \<^context> ("adv_record_fixture", Position.none, fields) of
       URust_Resolution.Resolved_Record_Struct (record_name, ordered) =>
         if Long_Name.base_name record_name = "adv_record_fixture" andalso length ordered = 2
         then ()
         else error "record struct-pattern metadata has the wrong source-visible fields"
     | URust_Resolution.Resolved_Constructor_Struct _ =>
         error "HOL record resolved through generic constructor metadata")
  end
\<close>

urust_expr_with_check adv_struct_reordered
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_right: y, adv_left: x } \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_struct_shorthand
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left, adv_right } \<Rightarrow> adv_right, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_struct_rest
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left, .. } \<Rightarrow> adv_left, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_struct_nested
  \<open> match \<llangle>AdvNested (Some (3 :: nat)) [4, 5]\<rrangle> { AdvNested { adv_option: Some(x), adv_values: [y, .., z] } if True \<Rightarrow> z, _ \<Rightarrow> 0 } \<close>

urust_expr_with_check adv_struct_or
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left: _, adv_right: _ } | AdvOther \<Rightarrow> \<llangle>True\<rrangle> } \<close>

urust_expr_with_check adv_struct_datatype_record
  \<open> match \<llangle>make_adv_datatype_record 3 4\<rrangle> { adv_datatype_record { adv_dr_right: y, adv_dr_left: x } \<Rightarrow> y } \<close>

section\<open> Bare \<open>match\<close> (automatic case/switch routing, D32) \<close>

text\<open>
Bare \<open>match\<close> routes constructor/disjunction heads to case and numerals to switch;
ambiguous identifier/wildcard heads default to case. It alone supports semicolon-free
statement sequencing.
\<close>

context fixes x :: \<open>nat option\<close> and n :: nat
begin

text\<open> Constructor and binding patterns route to the case lowering. \<close>
urust_expr_with_check ma_case \<open> match x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 } \<close>

text\<open> Numeral and wildcard patterns route to the switch lowering. \<close>
urust_expr_with_check ma_switch \<open> match n { 0 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<close>

text\<open> Identifier/wildcard arms are compatible with both lowerings and deliberately default to case. \<close>
urust_expr_with_check ma_ambiguous \<open> match x { None \<Rightarrow> 0, _ \<Rightarrow> 1 } \<close>

text\<open> Bare \<open>match\<close> in a let RHS. \<close>
urust_expr_with_check ma_let \<open> let r = match x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 }; r \<close>

text\<open> Bare \<open>match\<close> is a semicolon-free block-like statement; the explicit forms remain unchanged. \<close>
urust_expr_with_check ma_stmt \<open> match x { Some(_) \<Rightarrow> (), None \<Rightarrow> () } () \<close>

text\<open> Nested bare matches re-enter \<open>uval\<close>; the outer arms route to case and the inner arms to switch. \<close>
urust_expr_with_check ma_nested
  \<open> match x { Some(y) \<Rightarrow> match y { 0 \<Rightarrow> 1, _ \<Rightarrow> 2 }, None \<Rightarrow> 0 } \<close>

end


section\<open> Binder scope and shadowing robustness \<close>

text\<open>
These rows pin lexical scope boundaries, not only successful name lookup. A binding RHS sees the
outer environment, its continuation sees the new binder, sibling match arms are independent, and
binders are visible in guards and antiquotations. The matrix also covers wildcard hygiene, tuple
destructuring, mutable allocation, HOL-fixed variables, and names already meaningful to HOL or the
micro-Rust notation registry.
\<close>

subsection\<open> Sequential and tuple bindings \<close>

urust_expr_with_check bind_let_rhs_outer
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let x = x; x \<close>

urust_expr_with_check bind_let_three_deep
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let x = x; let x = x; \<llangle>x\<rrangle> \<close>

urust_expr_with_check bind_let_cross_names
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let y = x; let x = y; \<llangle>x + y\<rrangle> \<close>

urust_expr_with_check bind_const_then_let
  \<open> const x = \<llangle>1 :: nat\<rrangle>; let x = x; \<llangle>x\<rrangle> \<close>

urust_expr_with_check bind_let_then_const
  \<open> let x = \<llangle>1 :: nat\<rrangle>; const x = x; \<llangle>x\<rrangle> \<close>

text\<open> A binder introduced inside a block or branch is absent from the enclosing continuation. \<close>

urust_expr_with_check bind_block_scope
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let result = { let x = \<llangle>2 :: nat\<rrangle>; x }; x \<close>

urust_expr_with_check bind_if_branch_scope
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let result = if True { let x = x; x } else { let x = x; x }; x \<close>

text\<open> Expression antiquotations use the same lexical environment as value antiquotations. \<close>

urust_expr_with_check bind_expression_antiquotation
  \<open> let x = \<llangle>5 :: nat\<rrangle>; \<epsilon>\<open>\<up>x\<close> \<close>

urust_expr_with_check bind_tuple_rhs_outer
  \<open>
    let x = \<llangle>1 :: nat\<rrangle>;
    let y = \<llangle>True\<rrangle>;
    let (x, y) = (x, y);
    \<llangle>(x, y)\<rrangle>
  \<close>

urust_expr_with_check bind_tuple_nested_shadow
  \<open>
    let x = \<llangle>1 :: nat\<rrangle>;
    let y = \<llangle>2 :: nat\<rrangle>;
    let z = \<llangle>3 :: nat\<rrangle>;
    let (x, (y, z)) = (x, (y, z));
    \<llangle>x + y + z\<rrangle>
  \<close>

urust_expr_with_check bind_tuple_wildcard_preserves_outer
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let (_, y) = (x, \<llangle>True\<rrangle>); \<llangle>(x, y)\<rrangle> \<close>

urust_expr_with_check bind_const_tuple_shadow
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let y = \<llangle>2 :: nat\<rrangle>; const (x, y) = (y, x); \<llangle>x + y\<rrangle> \<close>

urust_expr_with_check bind_tuple_successive_shadow
  \<open>
    let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>);
    let (x, y) = (y, x);
    \<llangle>x + y\<rrangle>
  \<close>


subsection\<open> Mutable and immutable transitions \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

urust_expr_with_check bind_immutable_to_mutable
  \<open> let x = \<llangle>1 :: 32 word\<rrangle>; let mut x = x; \<llangle>x\<rrangle> \<close>

urust_expr_with_check bind_mutable_to_immutable
  \<open> let mut x = \<llangle>1 :: 32 word\<rrangle>; let x = *x; \<llangle>x\<rrangle> \<close>

urust_expr_with_check bind_mutable_to_mutable
  \<open> let mut x = \<llangle>1 :: 32 word\<rrangle>; let mut x = *x; \<llangle>x\<rrangle> \<close>

urust_expr_with_check bind_mutable_block_scope
  \<open>
    let mut x = \<llangle>1 :: 32 word\<rrangle>;
    let inner = { let mut x = *x; *x };
    *x
  \<close>

urust_expr_with_check bind_mutable_then_match
  \<open>
    let mut x = \<llangle>1 :: 32 word\<rrangle>;
    match Some(*x) { Some(x) \<Rightarrow> x, None \<Rightarrow> *x }
  \<close>

urust_expr_with_check bind_match_then_mutable
  \<open>
    match \<llangle>Some (1 :: 32 word)\<rrangle> {
      Some(x) \<Rightarrow> { let mut x = x; *x },
      None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
    }
  \<close>

urust_expr_with_check bind_mutable_tuple_shadow
  \<open>
    let x = \<llangle>1 :: nat\<rrangle>;
    let y = \<llangle>2 :: nat\<rrangle>;
    let mut (x, y) = (x, y);
    \<llangle>x + y\<rrangle>
  \<close>

context fixes x :: \<open>32 word\<close>
begin
urust_expr_with_check bind_hol_mutable_shadow
  \<open> let mut x = x; \<llangle>x\<rrangle> \<close>
end


subsection\<open> Match arms, guards, and recursive patterns \<close>

datatype binder_shadow_sum =
    BinderNat nat
  | BinderBool bool

urust_expr_with_check bind_match_arm_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x }
  \<close>

urust_expr_with_check bind_match_case_arm_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x }
  \<close>

urust_expr_with_check bind_match_scrutinee_outer
  \<open>
    let x = \<llangle>Some (1 :: nat)\<rrangle>;
    match x { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: nat\<rrangle> }
  \<close>

urust_expr_with_check bind_match_guard_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) if x > \<llangle>0 :: nat\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>

urust_expr_with_check bind_match_nested_let
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) \<Rightarrow> { let x = x; \<llangle>x\<rrangle> },
      None \<Rightarrow> x
    }
  \<close>

urust_expr_with_check bind_match_nested_match
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) \<Rightarrow> match Some(x) { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x },
      None \<Rightarrow> x
    }
  \<close>

text\<open> The same source name may be independently typed in sibling alternatives. \<close>

urust_expr_with_check bind_match_sibling_types
  \<open>
    match \<llangle>BinderNat 1\<rrangle> {
      BinderNat(x) \<Rightarrow> { let _ = \<llangle>x\<rrangle>; () },
      BinderBool(x) \<Rightarrow> { let _ = \<llangle>x\<rrangle>; () }
    }
  \<close>

urust_expr_with_check bind_match_sibling_same_name
  \<open>
    match \<llangle>Ok (1 :: nat) :: (nat, nat) result\<rrangle> {
      Ok(x) \<Rightarrow> \<llangle>x\<rrangle>,
      Err(x) \<Rightarrow> \<llangle>x\<rrangle>
    }
  \<close>

urust_expr_with_check bind_match_tuple_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let y = \<llangle>True\<rrangle>;
    match \<llangle>(1 :: nat, (False, TNil))\<rrangle> { (x, y) \<Rightarrow> \<llangle>(x, y)\<rrangle> }
  \<close>

urust_expr_with_check bind_match_nested_tuple_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let y = \<llangle>True\<rrangle>;
    match \<llangle>Some (1 :: nat, (False, TNil))\<rrangle> {
      Some((x, y)) \<Rightarrow> \<llangle>(x, y)\<rrangle>,
      None \<Rightarrow> \<llangle>(x, y)\<rrangle>
    }
  \<close>

urust_expr_with_check bind_match_alias_shadow
  \<open>
    let whole = \<llangle>None :: nat option\<rrangle>;
    let value = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      whole @ Some(value) \<Rightarrow> { let _ = \<llangle>whole\<rrangle>; \<llangle>value\<rrangle> },
      _ \<Rightarrow> value
    }
  \<close>

urust_expr_with_check bind_match_slice_shadow
  \<open>
    let head = \<llangle>0 :: nat\<rrangle>;
    let tail = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>[1 :: nat, 2, 3]\<rrangle> {
      [head, .., tail] \<Rightarrow> { let _ = \<llangle>tail\<rrangle>; \<llangle>head\<rrangle> },
      _ \<Rightarrow> head
    }
  \<close>

urust_expr_with_check bind_match_struct_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let y = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>AdvStruct 1 2\<rrangle> {
      AdvStruct { adv_left: x, adv_right: y } \<Rightarrow> \<llangle>x + y\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>

text\<open> Struct shorthand binders also shadow their same-named HOL selector constants. \<close>

urust_expr_with_check bind_match_struct_shorthand_shadow
  \<open>
    let adv_left = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>AdvStruct 1 2\<rrangle> {
      AdvStruct { adv_left, adv_right } \<Rightarrow> \<llangle>adv_left + adv_right\<rrangle>,
      _ \<Rightarrow> adv_left
    }
  \<close>

urust_expr_with_check bind_match_or_shadow
  \<open>
    let x = \<llangle>0 :: 32 word\<rrangle>;
    match \<llangle>RMA (1 :: 32 word)\<rrangle> {
      RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>

urust_expr_with_check bind_match_result_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let x = match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> x, None \<Rightarrow> x };
    \<llangle>x\<rrangle>
  \<close>

text\<open> Switch lowering has no source binder; its generated scrutinee binder remains hygienic. \<close>

urust_expr_with_check bind_match_switch_hygiene
  \<open>
    let anon_case = \<llangle>7 :: nat\<rrangle>;
    match_switch \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> anon_case, _ \<Rightarrow> anon_case }
  \<close>


subsection\<open> HOL context binders shadowed by micro-Rust binders \<close>

text\<open>
Here \<open>x\<close> and \<open>y\<close> are introduced by Isabelle's surrounding proof context. Each RHS or
scrutinee initially resolves to that HOL free; a same-named micro-Rust binder then takes precedence
only in its lexical continuation or arm.
\<close>

context fixes x :: nat and y :: bool
begin

urust_expr_with_check bind_hol_context_baseline \<open> \<llangle>(x, y)\<rrangle> \<close>

urust_expr_with_check bind_hol_let_shadow
  \<open> let x = x; x \<close>

urust_expr_with_check bind_hol_let_antiquotation
  \<open> let x = x; \<llangle>x\<rrangle> \<close>

urust_expr_with_check bind_hol_let_mixed_antiquotation
  \<open> let x = x; \<llangle>(x, y)\<rrangle> \<close>

urust_expr_with_check bind_hol_let_chain
  \<open> let x = x; let x = x; \<llangle>x\<rrangle> \<close>

urust_expr_with_check bind_hol_tuple_shadow
  \<open> let (x, y) = (x, y); \<llangle>(x, y)\<rrangle> \<close>

urust_expr_with_check bind_hol_match_shadow
  \<open> match Some(x) { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x } \<close>

urust_expr_with_check bind_hol_match_guard_shadow
  \<open>
    match Some(x) {
      Some(x) if x == \<llangle>x\<rrangle> \<Rightarrow> x,
      None \<Rightarrow> x
    }
  \<close>

urust_expr_with_check bind_hol_branch_scope
  \<open> let result = if True { let x = x; x } else { x }; \<llangle>(x, y)\<rrangle> \<close>

end


subsection\<open> Binders named after HOL constants and registered notation \<close>

text\<open>
Direct identifier resolution and embedded HOL parsing must both prefer a lexical binder over a
same-named constant, constructor, selector, or registered notation. A sibling arm without that
binder must continue to resolve the outer meaning.
\<close>

urust_expr_with_check bind_constant_id_direct
  \<open> let id = \<llangle>1 :: nat\<rrangle>; id \<close>

urust_expr_with_check bind_constants_nested
  \<open> let id = \<llangle>1 :: nat\<rrangle>; let fst = id; \<llangle>id + fst\<rrangle> \<close>

urust_expr_with_check bind_constants_tuple
  \<open>
    let (id, fst) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>);
    \<llangle>id + fst\<rrangle>
  \<close>

urust_expr_with_check bind_constant_match
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(id) \<Rightarrow> \<llangle>id\<rrangle>,
      None \<Rightarrow> \<llangle>0 :: nat\<rrangle>
    }
  \<close>

urust_expr_with_check bind_constructor_names
  \<open>
    let Some = \<llangle>1 :: nat\<rrangle>;
    let None = Some;
    \<llangle>Some + None\<rrangle>
  \<close>

urust_expr_with_check bind_notation_direct
  \<open> let myReg = \<llangle>1 :: nat\<rrangle>; myReg \<close>

urust_expr_with_check bind_notation_match_scope
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(myReg) \<Rightarrow> \<llangle>myReg\<rrangle>,
      None \<Rightarrow> myReg
    }
  \<close>

urust_expr_with_check bind_constant_mutable
  \<open> let mut id = \<llangle>1 :: 32 word\<rrangle>; \<llangle>id\<rrangle> \<close>

context fixes id :: nat
begin
urust_expr_with_check bind_hol_constant_triple_shadow
  \<open> let id = id; \<llangle>id\<rrangle> \<close>
end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open> Return expressions \<close>

text\<open>
Return stores no semicolon in the parser AST. The legacy spellings remain alpha-equal:
a terminal semicolon belongs to return itself, while the optional operand is lowered in
the current lexical environment.
\<close>

urust_expr_with_check return_unit \<open> return; \<close>

urust_expr_with_check return_explicit_unit \<open> return (); \<close>

urust_expr_with_check return_typed_value \<open> return \<llangle>7 :: 32 word\<rrangle>; \<close>

urust_expr_with_check return_bound_value
  \<open> let result = \<llangle>7 :: nat\<rrangle>; return result; \<close>

urust_expr_with_check return_in_block \<open> { return; } \<close>

urust_expr_with_check return_in_conditional
  \<open>
    if \<llangle>True\<rrangle> {
      return \<llangle>1 :: nat\<rrangle>;
    } else {
      return \<llangle>2 :: nat\<rrangle>;
    }
  \<close>

urust_expr_with_check return_in_match_arms
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(value) \<Rightarrow> { return value; },
      None \<Rightarrow> { return \<llangle>0 :: nat\<rrangle>; }
    }
  \<close>


section\<open> Regression and divergence cases \<close>

text\<open>
Resolved divergences stay positive; current rejections use the negative harness or
frontend-only golden stubs.
\<close>

subsection\<open> D-1 (RESOLVED 2026-08-25): \<open>if\<close> as a binary-operator operand -- both now reject \<close>

text\<open> An unparenthesized \<open>if\<close> operand is rejected by both parsers; parentheses make it an operand. \<close>
urust_expr_with_check d1_paren_operand
  \<open> (if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> }) + \<llangle>3 :: 32 word\<rrangle> \<close>

subsection\<open> D-2 (RESOLVED 2026-08-25): no-\<open>;\<close> sequencing of block-like expressions -- now accepted \<close>

text\<open> Block-like statements sequence without a trailing \<open>;\<close>, matching the frontend. \<close>
urust_expr_with_check d2_blk_seq \<open> { () } { () } \<close>

urust_expr_with_check d2_if_seq \<open> if \<llangle>True\<rrangle> { () } () \<close>

urust_expr_with_check d2_ifelse_seq \<open> if \<llangle>True\<rrangle> { () } else { () } () \<close>

subsection\<open> D-3 (RESOLVED 2026-08-24): a HOL-const-named binder IS captured in an antiquotation \<close>

text\<open> Enclosing binders shadow same-named HOL constants and registered notation names in antiquotations. \<close>
urust_expr_with_check div_binder_const \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id\<rrangle> \<close>

urust_expr_with_check cap_const_fst \<open> let fst = \<llangle>5 :: nat\<rrangle>; \<llangle>fst\<rrangle> \<close>  \<comment>\<open> binder name = HOL \<open>Product_Type.fst\<close> \<close>

urust_expr_with_check cap_const_deep \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id + 1\<rrangle> \<close>  \<comment>\<open> buried capture of a const-named binder \<close>

urust_expr_with_check cap_notation \<open> let myReg = \<llangle>5 :: nat\<rrangle>; \<llangle>myReg\<rrangle> \<close>  \<comment>\<open> binder name = a registered notation surface name (guard) \<close>

subsection\<open> D-5: non-identifier / non-method call callees -- parser UNDER-accepts (frontend accepts) \<close>

text\<open>
D-5: identifier and method callees work; deferred frontend forms are expression and
function antiquotations, turbofish, and macros. Nested-callable forms
\<open>f(a)(b)\<close> and \<open>(g)(x)\<close> are rejected by both parsers. The expressible
antiquotation case remains a golden stub; other forms are not yet lexable. See
\<open>urust-old-new-divergences.md\<close>.
\<close>
lemma \<open> undefined = \<lbrakk> \<epsilon>\<open>cf1\<close>(\<llangle>1 :: 64 word\<rrangle>) \<rbrakk> \<close> sorry
  \<comment> \<open>frontend: \<open>funcall1 cf1 (\<up>1)\<close>; parser rejects (callee must be an identifier or a method call).\<close>

subsection\<open> D-7: advanced patterns -- resolved for current consumers \<close>

text\<open>
D-7 is closed for \<open>match\<close>, \<open>match_case\<close>, \<open>match_switch\<close>,
\<open>let\<close>, and \<open>const\<close>. Grouped and borrow patterns are transparent; aliases,
ranges, slices, and structs use case lowering and remain refutable at binder and switch
sites. Case numerals are fidelity rejections, not part of this divergence. See
\<open>urust-old-new-divergences.md\<close>.
\<close>

subsection\<open> Deferred frontend surface \<close>

text\<open>
\<open>Conformance_Corpus.thy\<close> owns deferred-feature goldens. Add negative rows here
only when the parser has a stable diagnostic.
\<close>

end
