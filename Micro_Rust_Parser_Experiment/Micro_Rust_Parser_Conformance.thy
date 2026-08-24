(* Phase 1.1 conformance: the parser's LITERAL-tier output is ALPHA-EQUAL to the inner-syntax
   frontend's golden `\<lbrakk> src \<rbrakk>` elaboration.

   For each in-scope literal row we `micro_rust_expr lit_<tag> <src>` (defining the constant via the
   custom parser) and then prove `lit_<tag> = \<lbrakk> src \<rbrakk>` by `unfolding lit_<tag>_def by (rule
   refl)`: unfolding rewrites the goal to `<parser term> = <golden term>`, which refl closes iff they
   are alpha-equal -- i.e. the kernel checks the parser reproduces the frontend exactly.

   Rows mirror the literal cases of Conformance_Corpus.thy (kept pristine as the oracle). Deferred to
   later steps (NOT clean literals): bare True/False (identifier dispatch), panic!/strings (macros),
   sequencing/return. See notes/urust-parser-plan.md. *)

theory Micro_Rust_Parser_Conformance
  imports Micro_Rust_Parser
begin

section\<open> Bare decimal numerals (Conformance_Corpus PART I, "Numeric Literals") \<close>

micro_rust_expr lit_0  \<open> 0 \<close>
lemma \<open> lit_0  = \<lbrakk> 0 \<rbrakk> \<close>
  unfolding lit_0_def  by (rule refl)

micro_rust_expr lit_1  \<open> 1 \<close>
lemma \<open> lit_1  = \<lbrakk> 1 \<rbrakk> \<close>
  unfolding lit_1_def  by (rule refl)

micro_rust_expr lit_42 \<open> 42 \<close>
lemma \<open> lit_42 = \<lbrakk> 42 \<rbrakk> \<close>
  unfolding lit_42_def by (rule refl)


section\<open> Suffixed integer literals (PART I, "Numeric Ascriptions") \<close>

micro_rust_expr lit_0_u8  \<open> 0_u8 \<close>
lemma \<open> lit_0_u8  = \<lbrakk> 0_u8 \<rbrakk> \<close>
  unfolding lit_0_u8_def  by (rule refl)

micro_rust_expr lit_1_u8  \<open> 1_u8 \<close>
lemma \<open> lit_1_u8  = \<lbrakk> 1_u8 \<rbrakk> \<close>
  unfolding lit_1_u8_def  by (rule refl)

micro_rust_expr lit_0x4_u8 \<open> 0x4_u8 \<close>
lemma \<open> lit_0x4_u8 = \<lbrakk> 0x4_u8 \<rbrakk> \<close>
  unfolding lit_0x4_u8_def by (rule refl)

micro_rust_expr lit_0_u16 \<open> 0_u16 \<close>
lemma \<open> lit_0_u16 = \<lbrakk> 0_u16 \<rbrakk> \<close>
  unfolding lit_0_u16_def by (rule refl)

micro_rust_expr lit_1_u16 \<open> 1_u16 \<close>
lemma \<open> lit_1_u16 = \<lbrakk> 1_u16 \<rbrakk> \<close>
  unfolding lit_1_u16_def by (rule refl)

micro_rust_expr lit_0x12_u16 \<open> 0x12_u16 \<close>
lemma \<open> lit_0x12_u16 = \<lbrakk> 0x12_u16 \<rbrakk> \<close>
  unfolding lit_0x12_u16_def by (rule refl)

micro_rust_expr lit_0_u32 \<open> 0_u32 \<close>
lemma \<open> lit_0_u32 = \<lbrakk> 0_u32 \<rbrakk> \<close>
  unfolding lit_0_u32_def by (rule refl)

micro_rust_expr lit_1_u32 \<open> 1_u32 \<close>
lemma \<open> lit_1_u32 = \<lbrakk> 1_u32 \<rbrakk> \<close>
  unfolding lit_1_u32_def by (rule refl)

micro_rust_expr lit_0x2000_u32 \<open> 0x2000_u32 \<close>
lemma \<open> lit_0x2000_u32 = \<lbrakk> 0x2000_u32 \<rbrakk> \<close>
  unfolding lit_0x2000_u32_def by (rule refl)

micro_rust_expr lit_0_u64 \<open> 0_u64 \<close>
lemma \<open> lit_0_u64 = \<lbrakk> 0_u64 \<rbrakk> \<close>
  unfolding lit_0_u64_def by (rule refl)

micro_rust_expr lit_1_u64 \<open> 1_u64 \<close>
lemma \<open> lit_1_u64 = \<lbrakk> 1_u64 \<rbrakk> \<close>
  unfolding lit_1_u64_def by (rule refl)

micro_rust_expr lit_0x2f0_u64 \<open> 0x2f0_u64 \<close>
lemma \<open> lit_0x2f0_u64 = \<lbrakk> 0x2f0_u64 \<rbrakk> \<close>
  unfolding lit_0x2f0_u64_def by (rule refl)

micro_rust_expr lit_0_usize \<open> 0_usize \<close>
lemma \<open> lit_0_usize = \<lbrakk> 0_usize \<rbrakk> \<close>
  unfolding lit_0_usize_def by (rule refl)

micro_rust_expr lit_1_usize \<open> 1_usize \<close>
lemma \<open> lit_1_usize = \<lbrakk> 1_usize \<rbrakk> \<close>
  unfolding lit_1_usize_def by (rule refl)

micro_rust_expr lit_0xf_usize \<open> 0xffffffff0_usize \<close>
lemma \<open> lit_0xf_usize = \<lbrakk> 0xffffffff0_usize \<rbrakk> \<close>
  unfolding lit_0xf_usize_def by (rule refl)


section\<open> Unit (PART I, "Unit Literal") \<close>

micro_rust_expr lit_unit \<open> () \<close>
lemma \<open> lit_unit = \<lbrakk> () \<rbrakk> \<close>
  unfolding lit_unit_def by (rule refl)


section\<open> Value antiquotation \<open>\<llangle>_\<rrangle>\<close> (PART I, "Numeric Literals" / "HOL Value Injection") \<close>

micro_rust_expr lit_aq_word \<open> \<llangle>0 :: 32 word\<rrangle> \<close>
lemma \<open> lit_aq_word = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding lit_aq_word_def by (rule refl)

micro_rust_expr lit_aq_true \<open> \<llangle>True\<rrangle> \<close>
lemma \<open> lit_aq_true = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk> \<close>
  unfolding lit_aq_true_def by (rule refl)

micro_rust_expr lit_aq_some \<open> \<llangle>Some (0 :: nat)\<rrangle> \<close>
lemma \<open> lit_aq_some = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk> \<close>
  unfolding lit_aq_some_def by (rule refl)


section\<open> Expression antiquotation \<open>\<epsilon>\<open>_\<close>\<close> (PART I, "Boolean Literals") \<close>

micro_rust_expr lit_eaq_true \<open> \<epsilon>\<open>Bool_Type.true\<close> \<close>
lemma \<open> lit_eaq_true = \<lbrakk> \<epsilon>\<open>Bool_Type.true\<close> \<rbrakk> \<close>
  unfolding lit_eaq_true_def by (rule refl)


section\<open> Bare identifiers at value position (dispatch reuse) \<close>

text\<open> Unregistered HOL constants: the parser emits a bare \<open>Free name\<close>, which \<open>check_term\<close> promotes
to the corresponding \<open>Const\<close> (exactly as the frontend's \<open>lookup_id_tr\<close> fallback does). Rows True /
False mirror Conformance_Corpus PART I "Boolean Literals" L49-50. \<close>
micro_rust_expr lit_true  \<open> True \<close>
lemma \<open> lit_true  = \<lbrakk> True \<rbrakk> \<close>
  unfolding lit_true_def  by (rule refl)

micro_rust_expr lit_false \<open> False \<close>
lemma \<open> lit_false = \<lbrakk> False \<rbrakk> \<close>
  unfolding lit_false_def by (rule refl)

micro_rust_expr lit_none  \<open> None \<close>
lemma \<open> lit_none  = \<lbrakk> None \<rbrakk> \<close>
  unfolding lit_none_def  by (rule refl)

text\<open> A context-fixed free variable (unregistered, non-constant): stays a \<open>Free\<close>. \<close>
context fixes foo :: nat
begin
micro_rust_expr lit_ctx \<open> foo \<close>
lemma \<open> lit_ctx = \<lbrakk> foo \<rbrakk> \<close>
  unfolding lit_ctx_def by (rule refl)
end

text\<open> A registered \<open>micro_rust_notation\<close>: the parser emits a \<open>urust_dispatch\<close> marker that the
globally-installed \<open>term_check\<close> phases resolve to the registered backend -- the dispatch path,
reproduced without reimplementing dispatch. \<close>
definition my_backend :: nat where \<open> my_backend \<equiv> 7 \<close>
micro_rust_notation (literal) my_backend ("myReg")
micro_rust_expr lit_reg \<open> myReg \<close>
lemma \<open> lit_reg = \<lbrakk> myReg \<rbrakk> \<close>
  unfolding lit_reg_def by (rule refl)


section\<open> Sequencing and `let` / `const` bindings \<close>

text\<open> Sequencing (Conformance_Corpus PART I "Sequencing"): `e1; e2` -> `sequence e1 e2`; a trailing
`;` -> `sequence e skip` (skip = literal ()). Bodies here use only atoms (operators/return are later). \<close>
micro_rust_expr seq_unit \<open> (); () \<close>
lemma \<open> seq_unit = \<lbrakk> (); () \<rbrakk> \<close>
  unfolding seq_unit_def by (rule refl)

micro_rust_expr seq_trailing \<open> (); (); \<close>
lemma \<open> seq_trailing = \<lbrakk> (); (); \<rbrakk> \<close>
  unfolding seq_trailing_def by (rule refl)

text\<open> Plain immutable `let x = e; k` -> `bind e (\<lambda>x. k)` (HOAS); a bound-variable use in the body
is captured by the enclosing binder. \<close>
micro_rust_expr let_use \<open> let x = 5; x \<close>
lemma \<open> let_use = \<lbrakk> let x = 5; x \<rbrakk> \<close>
  unfolding let_use_def by (rule refl)

text\<open> Nested `let` + use of the OUTER binder (cf. Conformance_Corpus PART I "Sequencing",
`let a = 1; let b = 2; a`). The unused binder `b`'s type is pinned via `\<llangle>_ :: nat\<rrangle>`:
with a bare `2` its type would be a free type variable NOT in the result type, and `definition`
reflects such a hidden tvar as a spurious `itself` argument (the corpus's `undefined = \<dots>` stubs
dodge this because `undefined` is fully polymorphic; our named-definition harness does not). \<close>
micro_rust_expr let_ab \<open> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<close>
lemma \<open> let_ab = \<lbrakk> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<rbrakk> \<close>
  unfolding let_ab_def by (rule refl)

text\<open> `const x = e; k` is byte-for-byte the same desugaring as `let` (cf. Conformance_Corpus PART I
"Const Bindings", `const FOO = 5; ()`); `FOO` is unused so its type is pinned (as above). \<close>
micro_rust_expr const_foo \<open> const FOO = \<llangle>5 :: nat\<rrangle>; () \<close>
lemma \<open> const_foo = \<lbrakk> const FOO = \<llangle>5 :: nat\<rrangle>; () \<rbrakk> \<close>
  unfolding const_foo_def by (rule refl)

text\<open> Antiquotation capture under `let`: the HOL `x` inside `\<llangle>x\<rrangle>` is captured by the toy's
binder (the enclosing Term.lambda over `Free x`). \<close>
micro_rust_expr let_cap \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<close>
lemma \<open> let_cap = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding let_cap_def by (rule refl)

text\<open> Capture of a variable BURIED in a larger antiquotation body (`\<llangle>x + 1\<rrangle>`), not just a
bare `\<llangle>x\<rrangle>` -- exercises the general parse_antiq path (the enclosing binder in scope). \<close>
micro_rust_expr let_cap_deep \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<close>
lemma \<open> let_cap_deep = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<rbrakk> \<close>
  unfolding let_cap_deep_def by (rule refl)


section\<open> Pure-value operators (PART I: Arithmetic / Bitwise / Comparison / Boolean) \<close>

text\<open> Arithmetic (word operands pinned via value antiquotations; no unused binders, so no type pins).
Each `a <op> b` -> the frontend's operator const applied to the two elaborated operands. \<close>
micro_rust_expr op_add \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_add = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_add_def by (rule refl)

micro_rust_expr op_add3 \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> + \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_add3 = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> + \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_add3_def by (rule refl)

micro_rust_expr op_sub \<open> \<llangle>5 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_sub = \<lbrakk> \<llangle>5 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_sub_def by (rule refl)

micro_rust_expr op_mul \<open> \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_mul = \<lbrakk> \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_mul_def by (rule refl)

micro_rust_expr op_div \<open> \<llangle>6 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_div = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_div_def by (rule refl)

micro_rust_expr op_mod \<open> \<llangle>7 :: 32 word\<rrangle> % \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_mod = \<lbrakk> \<llangle>7 :: 32 word\<rrangle> % \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_mod_def by (rule refl)

text\<open> Precedence: `*` binds tighter than `+`, so this parses as `a + (b * c)`. \<close>
micro_rust_expr op_precmul \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_precmul = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_precmul_def by (rule refl)


text\<open> Bitwise (shift RHS is a `64 word`). \<close>
micro_rust_expr op_band \<open> \<llangle>6 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_band = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_band_def by (rule refl)

micro_rust_expr op_bor \<open> \<llangle>6 :: 32 word\<rrangle> | \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_bor = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> | \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_bor_def by (rule refl)

micro_rust_expr op_bxor \<open> \<llangle>6 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_bxor = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_bxor_def by (rule refl)

micro_rust_expr op_shl \<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>4 :: 64 word\<rrangle> \<close>
lemma \<open> op_shl = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> << \<llangle>4 :: 64 word\<rrangle> \<rbrakk> \<close>
  unfolding op_shl_def by (rule refl)

micro_rust_expr op_shr \<open> \<llangle>16 :: 32 word\<rrangle> >> \<llangle>2 :: 64 word\<rrangle> \<close>
lemma \<open> op_shr = \<lbrakk> \<llangle>16 :: 32 word\<rrangle> >> \<llangle>2 :: 64 word\<rrangle> \<rbrakk> \<close>
  unfolding op_shr_def by (rule refl)


text\<open> Comparison (non-associative; word operands, boolean-expression result). \<close>
micro_rust_expr op_lt \<open> \<llangle>1 :: 32 word\<rrangle> < \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_lt = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> < \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_lt_def by (rule refl)

micro_rust_expr op_le \<open> \<llangle>1 :: 32 word\<rrangle> <= \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_le = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> <= \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_le_def by (rule refl)

micro_rust_expr op_gt \<open> \<llangle>2 :: 32 word\<rrangle> > \<llangle>1 :: 32 word\<rrangle> \<close>
lemma \<open> op_gt = \<lbrakk> \<llangle>2 :: 32 word\<rrangle> > \<llangle>1 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_gt_def by (rule refl)

micro_rust_expr op_ge \<open> \<llangle>2 :: 32 word\<rrangle> >= \<llangle>1 :: 32 word\<rrangle> \<close>
lemma \<open> op_ge = \<lbrakk> \<llangle>2 :: 32 word\<rrangle> >= \<llangle>1 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_ge_def by (rule refl)

micro_rust_expr op_eq \<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>1 :: 32 word\<rrangle> \<close>
lemma \<open> op_eq = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>1 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_eq_def by (rule refl)

micro_rust_expr op_ne \<open> \<llangle>1 :: 32 word\<rrangle> != \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_ne = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> != \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding op_ne_def by (rule refl)


text\<open> Boolean connectives and unary `!` (`!!` = `!(!_)`, no special-case). Precedence: `&&` binds
tighter than `||`. \<close>
micro_rust_expr op_and \<open> True && False \<close>
lemma \<open> op_and = \<lbrakk> True && False \<rbrakk> \<close>
  unfolding op_and_def by (rule refl)

micro_rust_expr op_or \<open> True || False \<close>
lemma \<open> op_or = \<lbrakk> True || False \<rbrakk> \<close>
  unfolding op_or_def by (rule refl)

micro_rust_expr op_not \<open> !True \<close>
lemma \<open> op_not = \<lbrakk> !True \<rbrakk> \<close>
  unfolding op_not_def by (rule refl)

micro_rust_expr op_notnot \<open> !!True \<close>
lemma \<open> op_notnot = \<lbrakk> !!True \<rbrakk> \<close>
  unfolding op_notnot_def by (rule refl)

micro_rust_expr op_prec \<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>
lemma \<open> op_prec = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk> \<close>
  unfolding op_prec_def by (rule refl)

text\<open> Unary `!` over a parenthesized comparison (exercises `LPAR uexp RPAR` grouping + a boolean-result
binary op). \<close>
micro_rust_expr op_mixed \<open> !(\<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle>) \<close>
lemma \<open> op_mixed = \<lbrakk> !(\<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle>) \<rbrakk> \<close>
  unfolding op_mixed_def by (rule refl)


section\<open> Operator precedence & associativity probes (grouping = frontend, kernel-checked) \<close>

text\<open> Each row proves the new parser groups a MIXED-operator expression IDENTICALLY to the frontend
(the oracle): both parse-shapes usually type-check, so `refl` closes iff the parse trees match. Together
they pin every adjacent precedence tier and each associativity, verified against the frontend fixities
in Micro_Rust_Syntax.thy:543-603:
  loosest  ||(infixl 42) < &&(43) < {== != < <= > >=}(infix 44, NON-assoc) < |(45) < ^(46) < &(47)
           < {<< >>}(48) < {+ -}(49) < {* / %}(50)  tightest;  prefix ! (300) tighter than all binary.
Comparison non-associativity (frontend `infix`, our `%nonassoc`) rejects `a == b == c` in BOTH — a
parse error, so it is checked out-of-band (see notes), not by a refl row. \<close>

text\<open> Associativity: every binary operator is LEFT-associative (frontend infixl / our %left).
`op_add3` (a+b+c) already covers `+`; these cover `-`, `/`, `<<`, `&&`, `||`. \<close>
micro_rust_expr prec_sub_assoc \<open> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> prec_sub_assoc = \<lbrakk> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_sub_assoc_def by (rule refl)

micro_rust_expr prec_div_assoc \<open> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> prec_div_assoc = \<lbrakk> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_div_assoc_def by (rule refl)

micro_rust_expr prec_shl_assoc \<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> prec_shl_assoc = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_shl_assoc_def by (rule refl)

micro_rust_expr prec_and_assoc \<open> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>
lemma \<open> prec_and_assoc = \<lbrakk> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk> \<close>
  unfolding prec_and_assoc_def by (rule refl)

micro_rust_expr prec_or_assoc \<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<close>
lemma \<open> prec_or_assoc = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<rbrakk> \<close>
  unfolding prec_or_assoc_def by (rule refl)

text\<open> Adjacent-tier precedence (the tighter operator groups first). `op_precmul` (a + b*c) covers
* > +; `op_prec` (a || b && c) covers && > ||. These cover every other boundary. \<close>
micro_rust_expr prec_add_shl \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> prec_add_shl = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_add_shl_def by (rule refl)     \<comment>\<open> (a + b) << c :  + (49) tighter than << (48) \<close>

micro_rust_expr prec_shl_and \<open> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> prec_shl_and = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_shl_and_def by (rule refl)     \<comment>\<open> a & (b << c) :  << (48) tighter than & (47) \<close>

micro_rust_expr prec_and_xor \<open> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> prec_and_xor = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_and_xor_def by (rule refl)     \<comment>\<open> a ^ (b & c) :  & (47) tighter than ^ (46) \<close>

micro_rust_expr prec_xor_or \<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> prec_xor_or = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_xor_or_def by (rule refl)      \<comment>\<open> a | (b ^ c) :  ^ (46) tighter than | (45) \<close>

micro_rust_expr prec_or_cmp \<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> prec_or_cmp = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding prec_or_cmp_def by (rule refl)      \<comment>\<open> (a | b) == c :  | (45) tighter than == (44) \<close>

micro_rust_expr prec_cmp_and \<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<close>
lemma \<open> prec_cmp_and = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<rbrakk> \<close>
  unfolding prec_cmp_and_def by (rule refl)     \<comment>\<open> (a == b) && c :  == (44) tighter than && (43) \<close>

micro_rust_expr prec_not_and \<open> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>
lemma \<open> prec_not_and = \<lbrakk> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk> \<close>
  unfolding prec_not_and_def by (rule refl)     \<comment>\<open> (!a) && b :  prefix ! tighter than && \<close>

micro_rust_expr prec_not_cmp \<open> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<close>
lemma \<open> prec_not_cmp = \<lbrakk> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<rbrakk> \<close>
  unfolding prec_not_cmp_def by (rule refl)     \<comment>\<open> (!a) == b :  prefix ! tighter than == \<close>


section\<open> Block expressions and if / else \<close>

text\<open> Blocks ERASE: the frontend `_urust_scoping` is the identity (SE:360-362), so \<open>{ e }\<close> elaborates to
exactly \<open>\<lbrakk> e \<rbrakk>\<close> -- no `scoped` wrapper. Statements inside sequence via the existing `;` (`sequence`). \<close>
micro_rust_expr blk_lit \<open> { \<llangle>1 :: nat\<rrangle> } \<close>
lemma \<open> blk_lit = \<lbrakk> { \<llangle>1 :: nat\<rrangle> } \<rbrakk> \<close>
  unfolding blk_lit_def by (rule refl)

micro_rust_expr blk_seq \<open> { (); () } \<close>
lemma \<open> blk_seq = \<lbrakk> { (); () } \<rbrakk> \<close>
  unfolding blk_seq_def by (rule refl)

micro_rust_expr blk_let \<open> { let x = \<llangle>5 :: nat\<rrangle>; x } \<close>
lemma \<open> blk_let = \<lbrakk> { let x = \<llangle>5 :: nat\<rrangle>; x } \<rbrakk> \<close>
  unfolding blk_let_def by (rule refl)

text\<open> `if c { t } else { e }` -> `two_armed_conditional \<lbrakk>c\<rbrakk> \<lbrakk>t\<rbrakk> \<lbrakk>e\<rbrakk>` (Bool_Type.thy:30-35, via SE:364-365). \<close>
micro_rust_expr if_two \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> } \<close>
lemma \<open> if_two = \<lbrakk> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> } \<rbrakk> \<close>
  unfolding if_two_def by (rule refl)

text\<open> One-armed `if c { t }` fills the missing else with `skip` (= `literal ()`): the frontend `{...}`-path
emits `two_armed_conditional \<lbrakk>c\<rbrakk> \<lbrakk>t\<rbrakk> skip` (SE:366-367), NOT the `one_armed_conditional` const. Because
`two_armed_conditional` needs both arms at the SAME value type and the implicit else is unit-typed, a
one-armed (and an else-if with no final else) is only well-typed with a UNIT then-branch -- exactly
Rust's rule that a no-`else` `if` has type `()`. (This holds for the frontend golden identically.) \<close>
micro_rust_expr if_one \<open> if \<llangle>True\<rrangle> { () } \<close>
lemma \<open> if_one = \<lbrakk> if \<llangle>True\<rrangle> { () } \<rbrakk> \<close>
  unfolding if_one_def by (rule refl)

text\<open> else-if chains desugar to nested ifs (SYN:661-662): the else branch is itself an `if`. \<close>
micro_rust_expr if_elif \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else if \<llangle>False\<rrangle> { \<llangle>2 :: nat\<rrangle> } else { \<llangle>3 :: nat\<rrangle> } \<close>
lemma \<open> if_elif = \<lbrakk> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else if \<llangle>False\<rrangle> { \<llangle>2 :: nat\<rrangle> } else { \<llangle>3 :: nat\<rrangle> } \<rbrakk> \<close>
  unfolding if_elif_def by (rule refl)

micro_rust_expr if_elif2 \<open> if \<llangle>True\<rrangle> { () } else if \<llangle>False\<rrangle> { () } \<close>  \<comment>\<open> else-if, no final else (unit arms) \<close>
lemma \<open> if_elif2 = \<lbrakk> if \<llangle>True\<rrangle> { () } else if \<llangle>False\<rrangle> { () } \<rbrakk> \<close>
  unfolding if_elif2_def by (rule refl)

text\<open> Condition is an arbitrary expression (here a comparison); a nested if in a branch. \<close>
micro_rust_expr if_cmp \<open> if \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> { () } else { () } \<close>
lemma \<open> if_cmp = \<lbrakk> if \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> { () } else { () } \<rbrakk> \<close>
  unfolding if_cmp_def by (rule refl)

micro_rust_expr if_nest \<open> if \<llangle>True\<rrangle> { if \<llangle>False\<rrangle> { () } else { () } } else { () } \<close>
lemma \<open> if_nest = \<lbrakk> if \<llangle>True\<rrangle> { if \<llangle>False\<rrangle> { () } else { () } } else { () } \<rbrakk> \<close>
  unfolding if_nest_def by (rule refl)

end
