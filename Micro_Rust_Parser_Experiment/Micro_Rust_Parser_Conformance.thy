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
lemma \<open> lit_0  = \<lbrakk> 0 \<rbrakk> \<close>  unfolding lit_0_def  by (rule refl)

micro_rust_expr lit_1  \<open> 1 \<close>
lemma \<open> lit_1  = \<lbrakk> 1 \<rbrakk> \<close>  unfolding lit_1_def  by (rule refl)

micro_rust_expr lit_42 \<open> 42 \<close>
lemma \<open> lit_42 = \<lbrakk> 42 \<rbrakk> \<close> unfolding lit_42_def by (rule refl)


section\<open> Suffixed integer literals (PART I, "Numeric Ascriptions") \<close>

micro_rust_expr lit_0_u8  \<open> 0_u8 \<close>
lemma \<open> lit_0_u8  = \<lbrakk> 0_u8 \<rbrakk> \<close>  unfolding lit_0_u8_def  by (rule refl)

micro_rust_expr lit_1_u8  \<open> 1_u8 \<close>
lemma \<open> lit_1_u8  = \<lbrakk> 1_u8 \<rbrakk> \<close>  unfolding lit_1_u8_def  by (rule refl)

micro_rust_expr lit_0x4_u8 \<open> 0x4_u8 \<close>
lemma \<open> lit_0x4_u8 = \<lbrakk> 0x4_u8 \<rbrakk> \<close> unfolding lit_0x4_u8_def by (rule refl)

micro_rust_expr lit_0_u16 \<open> 0_u16 \<close>
lemma \<open> lit_0_u16 = \<lbrakk> 0_u16 \<rbrakk> \<close> unfolding lit_0_u16_def by (rule refl)

micro_rust_expr lit_1_u16 \<open> 1_u16 \<close>
lemma \<open> lit_1_u16 = \<lbrakk> 1_u16 \<rbrakk> \<close> unfolding lit_1_u16_def by (rule refl)

micro_rust_expr lit_0x12_u16 \<open> 0x12_u16 \<close>
lemma \<open> lit_0x12_u16 = \<lbrakk> 0x12_u16 \<rbrakk> \<close> unfolding lit_0x12_u16_def by (rule refl)

micro_rust_expr lit_0_u32 \<open> 0_u32 \<close>
lemma \<open> lit_0_u32 = \<lbrakk> 0_u32 \<rbrakk> \<close> unfolding lit_0_u32_def by (rule refl)

micro_rust_expr lit_1_u32 \<open> 1_u32 \<close>
lemma \<open> lit_1_u32 = \<lbrakk> 1_u32 \<rbrakk> \<close> unfolding lit_1_u32_def by (rule refl)

micro_rust_expr lit_0x2000_u32 \<open> 0x2000_u32 \<close>
lemma \<open> lit_0x2000_u32 = \<lbrakk> 0x2000_u32 \<rbrakk> \<close> unfolding lit_0x2000_u32_def by (rule refl)

micro_rust_expr lit_0_u64 \<open> 0_u64 \<close>
lemma \<open> lit_0_u64 = \<lbrakk> 0_u64 \<rbrakk> \<close> unfolding lit_0_u64_def by (rule refl)

micro_rust_expr lit_1_u64 \<open> 1_u64 \<close>
lemma \<open> lit_1_u64 = \<lbrakk> 1_u64 \<rbrakk> \<close> unfolding lit_1_u64_def by (rule refl)

micro_rust_expr lit_0x2f0_u64 \<open> 0x2f0_u64 \<close>
lemma \<open> lit_0x2f0_u64 = \<lbrakk> 0x2f0_u64 \<rbrakk> \<close> unfolding lit_0x2f0_u64_def by (rule refl)

micro_rust_expr lit_0_usize \<open> 0_usize \<close>
lemma \<open> lit_0_usize = \<lbrakk> 0_usize \<rbrakk> \<close> unfolding lit_0_usize_def by (rule refl)

micro_rust_expr lit_1_usize \<open> 1_usize \<close>
lemma \<open> lit_1_usize = \<lbrakk> 1_usize \<rbrakk> \<close> unfolding lit_1_usize_def by (rule refl)

micro_rust_expr lit_0xf_usize \<open> 0xffffffff0_usize \<close>
lemma \<open> lit_0xf_usize = \<lbrakk> 0xffffffff0_usize \<rbrakk> \<close> unfolding lit_0xf_usize_def by (rule refl)


section\<open> Unit (PART I, "Unit Literal") \<close>

micro_rust_expr lit_unit \<open> () \<close>
lemma \<open> lit_unit = \<lbrakk> () \<rbrakk> \<close> unfolding lit_unit_def by (rule refl)


section\<open> Value antiquotation \<open>\<llangle>_\<rrangle>\<close> (PART I, "Numeric Literals" / "HOL Value Injection") \<close>

micro_rust_expr lit_aq_word \<open> \<llangle>0 :: 32 word\<rrangle> \<close>
lemma \<open> lit_aq_word = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding lit_aq_word_def by (rule refl)

micro_rust_expr lit_aq_true \<open> \<llangle>True\<rrangle> \<close>
lemma \<open> lit_aq_true = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk> \<close> unfolding lit_aq_true_def by (rule refl)

micro_rust_expr lit_aq_some \<open> \<llangle>Some (0 :: nat)\<rrangle> \<close>
lemma \<open> lit_aq_some = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk> \<close> unfolding lit_aq_some_def by (rule refl)


section\<open> Expression antiquotation \<open>\<epsilon>\<open>_\<close>\<close> (PART I, "Boolean Literals") \<close>

micro_rust_expr lit_eaq_true \<open> \<epsilon>\<open>Bool_Type.true\<close> \<close>
lemma \<open> lit_eaq_true = \<lbrakk> \<epsilon>\<open>Bool_Type.true\<close> \<rbrakk> \<close> unfolding lit_eaq_true_def by (rule refl)


section\<open> Bare identifiers at value position (dispatch reuse) \<close>

text\<open> Unregistered HOL constants: the parser emits a bare \<open>Free name\<close>, which \<open>check_term\<close> promotes
to the corresponding \<open>Const\<close> (exactly as the frontend's \<open>lookup_id_tr\<close> fallback does). Rows True /
False mirror Conformance_Corpus PART I "Boolean Literals" L49-50. \<close>
micro_rust_expr lit_true  \<open> True \<close>
lemma \<open> lit_true  = \<lbrakk> True \<rbrakk> \<close>  unfolding lit_true_def  by (rule refl)

micro_rust_expr lit_false \<open> False \<close>
lemma \<open> lit_false = \<lbrakk> False \<rbrakk> \<close> unfolding lit_false_def by (rule refl)

micro_rust_expr lit_none  \<open> None \<close>
lemma \<open> lit_none  = \<lbrakk> None \<rbrakk> \<close>  unfolding lit_none_def  by (rule refl)

text\<open> A context-fixed free variable (unregistered, non-constant): stays a \<open>Free\<close>. \<close>
context fixes foo :: nat
begin
micro_rust_expr lit_ctx \<open> foo \<close>
lemma \<open> lit_ctx = \<lbrakk> foo \<rbrakk> \<close> unfolding lit_ctx_def by (rule refl)
end

text\<open> A registered \<open>micro_rust_notation\<close>: the parser emits a \<open>urust_dispatch\<close> marker that the
globally-installed \<open>term_check\<close> phases resolve to the registered backend -- the dispatch path,
reproduced without reimplementing dispatch. \<close>
definition my_backend :: nat where \<open> my_backend \<equiv> 7 \<close>
micro_rust_notation (literal) my_backend ("myReg")
micro_rust_expr lit_reg \<open> myReg \<close>
lemma \<open> lit_reg = \<lbrakk> myReg \<rbrakk> \<close> unfolding lit_reg_def by (rule refl)


section\<open> Sequencing and `let` / `const` bindings \<close>

text\<open> Sequencing (Conformance_Corpus PART I "Sequencing"): `e1; e2` -> `sequence e1 e2`; a trailing
`;` -> `sequence e skip` (skip = literal ()). Bodies here use only atoms (operators/return are later). \<close>
micro_rust_expr seq_unit \<open> (); () \<close>
lemma \<open> seq_unit = \<lbrakk> (); () \<rbrakk> \<close> unfolding seq_unit_def by (rule refl)

micro_rust_expr seq_trailing \<open> (); (); \<close>
lemma \<open> seq_trailing = \<lbrakk> (); (); \<rbrakk> \<close> unfolding seq_trailing_def by (rule refl)

text\<open> Plain immutable `let x = e; k` -> `bind e (\<lambda>x. k)` (HOAS); a bound-variable use in the body
is captured by the enclosing binder. \<close>
micro_rust_expr let_use \<open> let x = 5; x \<close>
lemma \<open> let_use = \<lbrakk> let x = 5; x \<rbrakk> \<close> unfolding let_use_def by (rule refl)

text\<open> Nested `let` + use of the OUTER binder (cf. Conformance_Corpus PART I "Sequencing",
`let a = 1; let b = 2; a`). The unused binder `b`'s type is pinned via `\<llangle>_ :: nat\<rrangle>`:
with a bare `2` its type would be a free type variable NOT in the result type, and `definition`
reflects such a hidden tvar as a spurious `itself` argument (the corpus's `undefined = \<dots>` stubs
dodge this because `undefined` is fully polymorphic; our named-definition harness does not). \<close>
micro_rust_expr let_ab \<open> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<close>
lemma \<open> let_ab = \<lbrakk> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<rbrakk> \<close> unfolding let_ab_def by (rule refl)

text\<open> `const x = e; k` is byte-for-byte the same desugaring as `let` (cf. Conformance_Corpus PART I
"Const Bindings", `const FOO = 5; ()`); `FOO` is unused so its type is pinned (as above). \<close>
micro_rust_expr const_foo \<open> const FOO = \<llangle>5 :: nat\<rrangle>; () \<close>
lemma \<open> const_foo = \<lbrakk> const FOO = \<llangle>5 :: nat\<rrangle>; () \<rbrakk> \<close> unfolding const_foo_def by (rule refl)

text\<open> Antiquotation capture under `let`: the HOL `x` inside `\<llangle>x\<rrangle>` is captured by the toy's
binder (the enclosing Term.lambda over `Free x`). \<close>
micro_rust_expr let_cap \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<close>
lemma \<open> let_cap = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<rbrakk> \<close> unfolding let_cap_def by (rule refl)

text\<open> Capture of a variable BURIED in a larger antiquotation body (`\<llangle>x + 1\<rrangle>`), not just a
bare `\<llangle>x\<rrangle>` -- exercises the general parse_antiq path (the enclosing binder in scope). \<close>
micro_rust_expr let_cap_deep \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<close>
lemma \<open> let_cap_deep = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<rbrakk> \<close> unfolding let_cap_deep_def by (rule refl)

end
