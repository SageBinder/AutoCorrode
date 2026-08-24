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


section\<open> Extended coverage (review pass) \<close>

text\<open> Broader pulls from Conformance_Corpus.thy across the already-implemented features, plus adjacent
edge cases, added during the 2026-08-24 review pass. Every row is `refl` against the frontend golden.
Two golden cases were found to DIVERGE and are deliberately omitted (documented in the parser change
log / design decisions): (1) an `if`/`else` used directly as a binary-operator OPERAND
(`if c {a} else {b} + x`) is ACCEPTED by this parser but REJECTED by the frontend (the frontend gives
`if`-then-else result-priority 21, too low to be a `+` operand without parentheses; our `uif` is a plain
`uexp` atom with no such floor) -- an over-acceptance, not a wrong term; (2) the no-`;` block-like-expr
sequencing (`{ e } stmt`, `if ... {} stmt` with no separating `;`) is accepted by the frontend but
rejected by this parser (a deferred feature). Blocks `{}` (frontend priority 1000) as operands, `if` as
a condition / `let`-RHS, and `a == b == c` non-associativity (rejected by both) all AGREE. \<close>

subsection\<open> Antiquotation widths / boolean value escapes \<close>

micro_rust_expr ext_aq64 \<open> \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> ext_aq64 = \<lbrakk> \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding ext_aq64_def by (rule refl)

micro_rust_expr ext_aq8 \<open> \<llangle>255 :: 8 word\<rrangle> \<close>
lemma \<open> ext_aq8 = \<lbrakk> \<llangle>255 :: 8 word\<rrangle> \<rbrakk> \<close> unfolding ext_aq8_def by (rule refl)

micro_rust_expr ext_aqfalse \<open> \<llangle>False\<rrangle> \<close>
lemma \<open> ext_aqfalse = \<lbrakk> \<llangle>False\<rrangle> \<rbrakk> \<close> unfolding ext_aqfalse_def by (rule refl)

subsection\<open> Boolean-literal operator combinations (bare True/False via dispatch) \<close>

micro_rust_expr ext_notfalse \<open> !False \<close>
lemma \<open> ext_notfalse = \<lbrakk> !False \<rbrakk> \<close> unfolding ext_notfalse_def by (rule refl)

micro_rust_expr ext_and_tt \<open> True && True \<close>
lemma \<open> ext_and_tt = \<lbrakk> True && True \<rbrakk> \<close> unfolding ext_and_tt_def by (rule refl)

micro_rust_expr ext_and_ft \<open> False && True \<close>
lemma \<open> ext_and_ft = \<lbrakk> False && True \<rbrakk> \<close> unfolding ext_and_ft_def by (rule refl)

micro_rust_expr ext_or_tt \<open> True || True \<close>
lemma \<open> ext_or_tt = \<lbrakk> True || True \<rbrakk> \<close> unfolding ext_or_tt_def by (rule refl)

micro_rust_expr ext_or_ff \<open> False || False \<close>
lemma \<open> ext_or_ff = \<lbrakk> False || False \<rbrakk> \<close> unfolding ext_or_ff_def by (rule refl)

subsection\<open> Let-bound variables as operator operands (bound-var use in operator position) \<close>

micro_rust_expr ext_let_add \<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<close>
lemma \<open> ext_let_add = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<rbrakk> \<close> unfolding ext_let_add_def by (rule refl)

micro_rust_expr ext_let_sub \<open> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<close>
lemma \<open> ext_let_sub = \<lbrakk> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<rbrakk> \<close> unfolding ext_let_sub_def by (rule refl)

micro_rust_expr ext_let_mul \<open> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<close>
lemma \<open> ext_let_mul = \<lbrakk> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<rbrakk> \<close> unfolding ext_let_mul_def by (rule refl)

micro_rust_expr ext_let_band \<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<close>
lemma \<open> ext_let_band = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<rbrakk> \<close> unfolding ext_let_band_def by (rule refl)

micro_rust_expr ext_let_shl \<open> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<close>
lemma \<open> ext_let_shl = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding ext_let_shl_def by (rule refl)

micro_rust_expr ext_let_not \<open> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<close>
lemma \<open> ext_let_not = \<lbrakk> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<rbrakk> \<close> unfolding ext_let_not_def by (rule refl)

micro_rust_expr ext_let_cmp \<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a < b \<close>
lemma \<open> ext_let_cmp = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a < b \<rbrakk> \<close> unfolding ext_let_cmp_def by (rule refl)

subsection\<open> Comparison / precedence with context-fixed free variables as operands \<close>
context fixes m n :: \<open>nat\<close> and x y :: \<open>64 word\<close> and w :: \<open>32 word\<close>
begin

micro_rust_expr ext_cmp_mn \<open> m == n \<close>
lemma \<open> ext_cmp_mn = \<lbrakk> m == n \<rbrakk> \<close> unfolding ext_cmp_mn_def by (rule refl)

micro_rust_expr ext_cmp_ne \<open> m != n \<close>
lemma \<open> ext_cmp_ne = \<lbrakk> m != n \<rbrakk> \<close> unfolding ext_cmp_ne_def by (rule refl)

micro_rust_expr ext_cmp_notmn \<open> !(m == n) \<close>
lemma \<open> ext_cmp_notmn = \<lbrakk> !(m == n) \<rbrakk> \<close> unfolding ext_cmp_notmn_def by (rule refl)

micro_rust_expr ext_cmp_w0 \<open> w > \<llangle>0 :: 32 word\<rrangle> \<close>
lemma \<open> ext_cmp_w0 = \<lbrakk> w > \<llangle>0 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding ext_cmp_w0_def by (rule refl)

micro_rust_expr ext_not_add \<open> !x + y \<close>
lemma \<open> ext_not_add = \<lbrakk> !x + y \<rbrakk> \<close> unfolding ext_not_add_def by (rule refl)  \<comment>\<open> (!x) + y : prefix ! tighter than + \<close>

micro_rust_expr ext_not_nested \<open> !(!x == x^y) \<close>
lemma \<open> ext_not_nested = \<lbrakk> !(!x == x^y) \<rbrakk> \<close> unfolding ext_not_nested_def by (rule refl)
end

subsection\<open> Block nesting, block bodies, and blocks as operands (frontend priority 1000: agree) \<close>

micro_rust_expr ext_blk_bare \<open> { 42 } \<close>
lemma \<open> ext_blk_bare = \<lbrakk> { 42 } \<rbrakk> \<close> unfolding ext_blk_bare_def by (rule refl)

micro_rust_expr ext_blk_nest \<open> {{ 42 }} \<close>
lemma \<open> ext_blk_nest = \<lbrakk> {{ 42 }} \<rbrakk> \<close> unfolding ext_blk_nest_def by (rule refl)

micro_rust_expr ext_blk_deep \<open> {{{{{ \<llangle>1 :: nat\<rrangle> }}}}} \<close>
lemma \<open> ext_blk_deep = \<lbrakk> {{{{{ \<llangle>1 :: nat\<rrangle> }}}}} \<rbrakk> \<close> unfolding ext_blk_deep_def by (rule refl)

micro_rust_expr ext_blk_op \<open> { \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_blk_op = \<lbrakk> { \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_blk_op_def by (rule refl)

micro_rust_expr ext_blk_operand_l \<open> { \<llangle>1 :: 32 word\<rrangle> } + \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> ext_blk_operand_l = \<lbrakk> { \<llangle>1 :: 32 word\<rrangle> } + \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding ext_blk_operand_l_def by (rule refl)

micro_rust_expr ext_blk_operand_r \<open> \<llangle>1 :: 32 word\<rrangle> + { \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_blk_operand_r = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + { \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_blk_operand_r_def by (rule refl)

micro_rust_expr ext_not_blk \<open> !{ \<llangle>True\<rrangle> } \<close>
lemma \<open> ext_not_blk = \<lbrakk> !{ \<llangle>True\<rrangle> } \<rbrakk> \<close> unfolding ext_not_blk_def by (rule refl)

subsection\<open> if / else: else-if depth, bare conditions, parenthesized-precedence conditions, deep blocks \<close>

micro_rust_expr ext_elif_word \<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_elif_word = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_elif_word_def by (rule refl)

micro_rust_expr ext_elif3 \<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_elif3 = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_elif3_def by (rule refl)

micro_rust_expr ext_if_one_bare \<open> if True { () } \<close>
lemma \<open> ext_if_one_bare = \<lbrakk> if True { () } \<rbrakk> \<close> unfolding ext_if_one_bare_def by (rule refl)

micro_rust_expr ext_if_par_cond \<open> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<close>
lemma \<open> ext_if_par_cond = \<lbrakk> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<rbrakk> \<close> unfolding ext_if_par_cond_def by (rule refl)

micro_rust_expr ext_if_deepblock \<open> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<close>
lemma \<open> ext_if_deepblock = \<lbrakk> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<rbrakk> \<close> unfolding ext_if_deepblock_def by (rule refl)

micro_rust_expr ext_if_cond \<open> if if \<llangle>True\<rrangle> { \<llangle>True\<rrangle> } else { \<llangle>False\<rrangle> } { () } else { () } \<close>  \<comment>\<open> if-expr as condition (frontend cond priority 20 admits an if at 21) \<close>
lemma \<open> ext_if_cond = \<lbrakk> if if \<llangle>True\<rrangle> { \<llangle>True\<rrangle> } else { \<llangle>False\<rrangle> } { () } else { () } \<rbrakk> \<close> unfolding ext_if_cond_def by (rule refl)

micro_rust_expr ext_let_if \<open> let x = if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }; x \<close>
lemma \<open> ext_let_if = \<lbrakk> let x = if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }; x \<rbrakk> \<close> unfolding ext_let_if_def by (rule refl)

micro_rust_expr ext_seq_if \<open> { if \<llangle>True\<rrangle> { () } else { () }; () } \<close>
lemma \<open> ext_seq_if = \<lbrakk> { if \<llangle>True\<rrangle> { () } else { () }; () } \<rbrakk> \<close> unfolding ext_seq_if_def by (rule refl)


section\<open> Function calls (PART I: "Function Calls") \<close>

text\<open> \<open>f(a0, ..., a{N-1})\<close> -> \<open>funcallN f \<lbrakk>a0\<rbrakk> ... \<lbrakk>a{N-1}\<rbrakk>\<close> (Core_Syntax.thy:503-587). The callee
resolves in the NFunction (\<open>call\<close>) dispatch context and is NOT wrapped in \<open>literal\<close>; arguments are
ordinary value expressions, so nested calls fall out of the recursion. Callee-typing note: to keep
\<open>micro_rust_expr\<close>'s emitted \<open>definition\<close> well-formed (no free type variable outside the result type --
the R1 named-def harness limitation), callee value types are concrete (\<open>64 word\<close>) and every argument is
pinned via a value antiquotation. Callees are built with \<open>lift_funN\<close> (Core_Expression.thy:404-445), the
same idiom the corpus uses (Conformance_Corpus.thy:1044-1047). \<close>

definition cf0 :: \<open>(unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf0 \<equiv> lift_fun0 0 \<close>
definition cf1 :: \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf1 \<equiv> lift_fun1 (\<lambda>x. x) \<close>
definition cf2 :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> cf2 \<equiv> lift_fun2 (+) \<close>

text\<open> Arity 0 / 1 / 2, unregistered global-constant callee: both the parser (NFunction lookup miss ->
\<open>Syntax.parse_term\<close>) and the frontend (\<open>lookup_id_tr\<close> miss -> bare \<open>Free\<close> promoted by \<open>decode_term\<close>)
resolve the bare name to the SAME \<open>Const\<close>. \<close>
micro_rust_expr call0 \<open> cf0() \<close>
lemma \<open> call0 = \<lbrakk> cf0() \<rbrakk> \<close> unfolding call0_def by (rule refl)

micro_rust_expr call1 \<open> cf1(\<llangle>1 :: 64 word\<rrangle>) \<close>
lemma \<open> call1 = \<lbrakk> cf1(\<llangle>1 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call1_def by (rule refl)

micro_rust_expr call2 \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> call2 = \<lbrakk> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call2_def by (rule refl)

text\<open> Nested call \<open>f(g(c), b)\<close>: the inner call is an ordinary argument expression (\<open>cf1\<close>'s \<open>64 word\<close>
result matches \<open>cf2\<close>'s first parameter). \<close>
micro_rust_expr call_nested \<open> cf2(cf1(\<llangle>1 :: 64 word\<rrangle>), \<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> call_nested = \<lbrakk> cf2(cf1(\<llangle>1 :: 64 word\<rrangle>), \<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close>
  unfolding call_nested_def by (rule refl)

text\<open> Registered \<open>(call)\<close> notation callee: the parser emits a \<open>urust_dispatch\<close> NFunction marker that the
installed \<open>term_check\<close> phases resolve to the backend -- the same dispatch path as \<open>myReg\<close>, in call
context. \<close>
micro_rust_notation (call) cf1 ("regCall")
micro_rust_expr call_reg \<open> regCall(\<llangle>3 :: 64 word\<rrangle>) \<close>
lemma \<open> call_reg = \<lbrakk> regCall(\<llangle>3 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_reg_def by (rule refl)

text\<open> A \<open>let\<close>-bound callee: lexical scope wins (env \<open>Free\<close>, no dispatch, no \<open>literal\<close> wrapper) and the use
ctrl-clicks to its binder -- matching the frontend's witness-precedence for a bound name in call
position. \<close>
micro_rust_expr call_letbound \<open> let h = \<llangle>cf1\<rrangle>; h(\<llangle>4 :: 64 word\<rrangle>) \<close>
lemma \<open> call_letbound = \<lbrakk> let h = \<llangle>cf1\<rrangle>; h(\<llangle>4 :: 64 word\<rrangle>) \<rbrakk> \<close>
  unfolding call_letbound_def by (rule refl)

text\<open> Unregistered context-fixed callee (function-typed free): stays a \<open>Free\<close> on both sides (exercises
the \<open>Syntax.parse_term\<close> / \<open>lookup_free\<close> fallback, as \<open>lit_ctx\<close> does at value position). \<close>
context fixes g :: \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
begin
micro_rust_expr call_ctx \<open> g(\<llangle>5 :: 64 word\<rrangle>) \<close>
lemma \<open> call_ctx = \<lbrakk> g(\<llangle>5 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_ctx_def by (rule refl)
end


section\<open> Known parser divergences (old frontend vs new parser) -- recorded, not proven \<close>

text\<open> Per \<open>urust-rules-and-conventions.md\<close>: a divergence between the inner-syntax frontend and the new
parser is NEVER silently dropped -- it is kept here as a test case. Where a well-typed \<open>NAME = \<lbrakk> src \<rbrakk>\<close>
goal can be stated it is a \<open>sorry\<close>'d lemma; where it CANNOT (the frontend rejects \<open>src\<close> so \<open>\<lbrakk> src \<rbrakk>\<close>
does not parse / the parser rejects \<open>src\<close> so the command errors / the two terms have incompatible types)
the case is recorded via whichever of \<open>micro_rust_expr\<close> (parser accepts) or a golden \<open>undefined = \<lbrakk> src \<rbrakk>\<close>
stub (frontend accepts) builds, plus a comment. Canonical tracker: \<open>notes/claude/urust-old-new-divergences.md\<close>. \<close>

subsection\<open> D-1: `if`/`else` as a binary-operator operand -- parser OVER-accepts (frontend rejects) \<close>

text\<open> Source: \<open>if \<llangle>True\<rrangle> { \<llangle>1::32 word\<rrangle> } else { \<llangle>2::32 word\<rrangle> } + \<llangle>3::32 word\<rrangle>\<close>. The
frontend REJECTS this (its `if` mixfix result-priority 21 is too low to be a `+` operand without parens),
so the golden \<open>\<lbrakk> ... + ... \<rbrakk>\<close> does NOT parse and no \<open>= \<lbrakk> src \<rbrakk>\<close> lemma (even \<open>sorry\<close>'d) can be written.
Our parser accepts it as \<open>(if...) + 3\<close>; on inputs both accept the terms are alpha-equal. Recorded via the
\<open>micro_rust_expr\<close> that succeeds. General fix (deferred): stratify control-flow vs operator expressions,
once, with `match`/loops. \<close>
micro_rust_expr div_if_operand
  \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } + \<llangle>3 :: 32 word\<rrangle> \<close>
  \<comment> \<open>parser accepts (defines `urust_add (two_armed_conditional ...) (\<up>3)`); the frontend rejects the
     same source with an inner-syntax error, so there is no golden RHS to equate against.\<close>

subsection\<open> D-2: no-`;` sequencing of block-like expressions -- parser UNDER-accepts (frontend accepts) \<close>

text\<open> Source: \<open>{ () } { () }\<close>. The frontend accepts it as sequencing (\<open>\<up>() ; \<up>()\<close>); our parser
REJECTS it (a block/`if` in statement position currently needs a trailing `;` -- the deferred no-`;`
"optional semicolon after a block-like expression" feature). \<open>micro_rust_expr\<close> on it would error, so we
record only the frontend golden as a \<open>sorry\<close>'d stub. \<close>
lemma \<open> undefined = \<lbrakk> { () } { () } \<rbrakk> \<close> sorry
  \<comment> \<open>frontend sequences the two blocks; parser rejects (deferred feature, not a bug).\<close>

subsection\<open> D-3 (RESOLVED 2026-08-24): a HOL-const-named binder IS now captured in an antiquotation \<close>

text\<open> WAS a divergence: \<open>let id = \<llangle>5::nat\<rrangle>; \<llangle>id\<rrangle>\<close> (binder `id` = HOL \<open>Fun.id\<close>) elaborated to
\<open>bind (\<up>5) (\<lambda>id. \<up>Fun.id)\<close> -- `id` resolved to the CONSTANT, NOT captured -- diverging from the frontend's
captured \<open>bind (\<up>5) (\<lambda>id. \<up>id)\<close>. FIXED: \<open>Parser_Utils.parse_antiq\<close> now \<open>Variable.add_fixes_direct\<close>es the
enclosing binder names before \<open>Syntax.parse_term\<close>, so a binder shadows a same-named HOL constant (matching
the frontend's single-context HOAS). The intended equalities now close by \<open>refl\<close>. Only genuine HOL-CONSTANT
binder names were ever affected: a registered \<open>micro_rust_notation\<close> SURFACE name (e.g. \<open>myReg\<close>) is not a HOL
const, so \<open>Syntax.parse_term\<close> already yielded a \<open>Free\<close> for it inside \<open>\<llangle>_\<rrangle>\<close> -- \<open>cap_notation\<close> is
included as a guard. See \<open>urust-old-new-divergences.md\<close> (D-3). \<close>
micro_rust_expr div_binder_const \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id\<rrangle> \<close>
lemma \<open> div_binder_const = \<lbrakk> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id\<rrangle> \<rbrakk> \<close>
  unfolding div_binder_const_def by (rule refl)

micro_rust_expr cap_const_fst \<open> let fst = \<llangle>5 :: nat\<rrangle>; \<llangle>fst\<rrangle> \<close>
  \<comment> \<open>binder name = HOL \<open>Product_Type.fst\<close>\<close>
lemma \<open> cap_const_fst = \<lbrakk> let fst = \<llangle>5 :: nat\<rrangle>; \<llangle>fst\<rrangle> \<rbrakk> \<close>
  unfolding cap_const_fst_def by (rule refl)

micro_rust_expr cap_const_deep \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id + 1\<rrangle> \<close>
  \<comment> \<open>buried capture of a HOL-const-named binder inside a compound antiquotation body\<close>
lemma \<open> cap_const_deep = \<lbrakk> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id + 1\<rrangle> \<rbrakk> \<close>
  unfolding cap_const_deep_def by (rule refl)

micro_rust_expr cap_notation \<open> let myReg = \<llangle>5 :: nat\<rrangle>; \<llangle>myReg\<rrangle> \<close>
  \<comment> \<open>binder name = a registered \<open>micro_rust_notation\<close> surface name (guard; not a HOL const)\<close>
lemma \<open> cap_notation = \<lbrakk> let myReg = \<llangle>5 :: nat\<rrangle>; \<llangle>myReg\<rrangle> \<rbrakk> \<close>
  unfolding cap_notation_def by (rule refl)

subsection\<open> D-4: antiquotation start-states do not balance nested delimiters (LATENT) \<close>

text\<open> A \<open>\<epsilon>\<open> ... \<close>\<close> body containing an inner cartouche \<open>\<open>...\<close>\<close> (or a \<open>\<llangle>...\<rrangle>\<close> body
containing a nested \<open>\<llangle>\<close>/\<open>\<rrangle>\<close>) closes on the FIRST closer and silently mis-parses the tail. No
current conformance row triggers it (real HOL bodies here contain no nested cartouche), so it is recorded
as a note rather than a runnable case; a runnable trigger + the depth-counting fix belong with the
nested-\<open>\<lbrakk>...\<rbrakk>\<close> / antiquotation tier. \<close>

subsection\<open> D-5: non-identifier call callees -- parser UNDER-accepts (frontend accepts) \<close>

text\<open> The function-call grammar is IDENTIFIER-headed (\<open>IDENT LPAR ... RPAR\<close>), so only \<open>f(args)\<close> with an
identifier callee parses. The frontend's \<open>urust_callable\<close> is richer (\<open>Micro_Rust_Syntax.thy:221-258\<close>):
method/struct callee \<open>x.m(a)\<close>, antiquotation callee \<open>\<epsilon>\<open>g\<close>(a)\<close>, turbofish \<open>f::\<open>N\<close>(a)\<close>, and
(macro) \<open>m!(...)\<close>. These are deferred; each is an under-acceptance recorded here. (\<open>f(a)(b)\<close> and
\<open>(g)(x)\<close> are rejected by BOTH -- a funcall result / grouped expr cannot fill the callable slot -- so
they are NOT divergences and need no stub.) The two directly expressible forms are kept as \<open>sorry\<close>'d
golden stubs; the rest are recorded as a note (turbofish needs \<open>::\<close> + const-generics; macros' \<open>!\<close> and
paths' \<open>::\<close> are additionally unlexable in the current parser). Canonical tracker:
\<open>notes/claude/urust-old-new-divergences.md\<close> (D-5). \<close>

text\<open> Method/struct callee \<open>recv.m(a)\<close> desugars to \<open>funcall (N+1) m recv a...\<close> (receiver prepended,
method name via NFunction dispatch, \<open>Core_Syntax.thy:589-594\<close>); the parser has no \<open>.\<close> token. \<close>
lemma \<open> undefined = \<lbrakk> \<llangle>0 :: 64 word\<rrangle>.cf2(\<llangle>1 :: 64 word\<rrangle>) \<rbrakk> \<close> sorry
  \<comment> \<open>frontend: \<open>funcall2 cf2 (\<up>0) (\<up>1)\<close> (receiver prepended); parser rejects (no method syntax yet).\<close>

text\<open> Antiquotation callee \<open>\<epsilon>\<open>expr\<close>(a)\<close>: the callee is a HOL-embedded expression, not an
identifier (\<open>Micro_Rust_Syntax.thy:223\<close>). \<close>
lemma \<open> undefined = \<lbrakk> \<epsilon>\<open>cf1\<close>(\<llangle>1 :: 64 word\<rrangle>) \<rbrakk> \<close> sorry
  \<comment> \<open>frontend: \<open>funcall1 cf1 (\<up>1)\<close>; parser rejects (callee must be a bare identifier).\<close>

text\<open> Turbofish \<open>f::\<open>N\<close>(a)\<close>, macros \<open>m!(...)\<close>, and path callees \<open>Foo::bar(a)\<close> are further deferred:
turbofish needs const-generic params, and the macro \<open>!\<close> / path \<open>::\<close> are not yet lexed (they hit the
positioned catch-all). Recorded as a note; runnable stubs land with the \<open>::\<close> / macro tiers. \<close>

end
