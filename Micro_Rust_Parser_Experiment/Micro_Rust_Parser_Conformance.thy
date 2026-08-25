(* Conformance of the custom µRust parser against the inner-syntax frontend.

   For every implemented construct we `urust_expr NAME <src>` (defining a constant via the custom
   parser: ml_lex_yacc URust grammar -> reified URust_AST -> URust_Translate -> shallow term, dummyT +
   one check_term) and then prove `NAME = \<lbrakk> src \<rbrakk>` by `unfolding NAME_def by (rule refl)`.
   Unfolding rewrites the goal to `<parser term> = <frontend golden term>`, which `refl` closes IFF the
   two are ALPHA-EQUAL -- i.e. the kernel checks that the parser reproduces the frontend's `\<lbrakk> _ \<rbrakk>`
   elaboration exactly. Conformance_Corpus.thy is the pristine oracle (its `undefined = \<lbrakk> src \<rbrakk> sorry`
   stubs); rows whose `src` uses only implemented features are mirrored here as proved `refl` rows.

   Coverage (each a section below): numeric / suffixed / unit literals; value + expression antiquotations;
   bare identifiers (dispatch); sequencing / `let` / `const`; pure-value operators (arithmetic, bitwise,
   comparison, boolean, unary) with antiquotation / let-bound / context-fixed operands, and precedence /
   associativity probes; blocks; `if` / `else`; function calls; method calls; a cross-feature robustness
   tier; and the "Known parser divergences" tier (recorded, not all proved -- per rule C2).

   Definability note (R1): `urust_expr` DEFINES a constant, so a `src` leaving a free type variable
   NOT in the result type (e.g. an unused polymorphic binder, or a call arg whose type is absorbed into a
   polymorphic callee) cannot be `definition`'d cleanly -- `Local_Theory.define` reflects it as a spurious
   `itself` argument and `refl` fails to type-check. The corpus dodges this (its `undefined` is fully
   polymorphic). We pin such types (word widths, `\<llangle>_ :: T\<rrangle>` on arguments) so every row is a
   clean named definition. *)

theory Micro_Rust_Parser_Conformance
  imports Micro_Rust_Parser
begin

section\<open> Numeric literals (Corpus PART I, "Numeric Literals") \<close>

urust_expr lit_0  \<open> 0 \<close>
lemma \<open> lit_0  = \<lbrakk> 0 \<rbrakk> \<close> unfolding lit_0_def  by (rule refl)

urust_expr lit_1  \<open> 1 \<close>
lemma \<open> lit_1  = \<lbrakk> 1 \<rbrakk> \<close> unfolding lit_1_def  by (rule refl)

urust_expr lit_42 \<open> 42 \<close>
lemma \<open> lit_42 = \<lbrakk> 42 \<rbrakk> \<close> unfolding lit_42_def by (rule refl)


section\<open> Suffixed integer literals (Corpus PART I, "Numeric Ascriptions") \<close>

urust_expr lit_0_u8  \<open> 0_u8 \<close>
lemma \<open> lit_0_u8  = \<lbrakk> 0_u8 \<rbrakk> \<close> unfolding lit_0_u8_def  by (rule refl)

urust_expr lit_1_u8  \<open> 1_u8 \<close>
lemma \<open> lit_1_u8  = \<lbrakk> 1_u8 \<rbrakk> \<close> unfolding lit_1_u8_def  by (rule refl)

urust_expr lit_0x4_u8 \<open> 0x4_u8 \<close>
lemma \<open> lit_0x4_u8 = \<lbrakk> 0x4_u8 \<rbrakk> \<close> unfolding lit_0x4_u8_def by (rule refl)

urust_expr lit_0_u16 \<open> 0_u16 \<close>
lemma \<open> lit_0_u16 = \<lbrakk> 0_u16 \<rbrakk> \<close> unfolding lit_0_u16_def by (rule refl)

urust_expr lit_1_u16 \<open> 1_u16 \<close>
lemma \<open> lit_1_u16 = \<lbrakk> 1_u16 \<rbrakk> \<close> unfolding lit_1_u16_def by (rule refl)

urust_expr lit_0x12_u16 \<open> 0x12_u16 \<close>
lemma \<open> lit_0x12_u16 = \<lbrakk> 0x12_u16 \<rbrakk> \<close> unfolding lit_0x12_u16_def by (rule refl)

urust_expr lit_0_u32 \<open> 0_u32 \<close>
lemma \<open> lit_0_u32 = \<lbrakk> 0_u32 \<rbrakk> \<close> unfolding lit_0_u32_def by (rule refl)

urust_expr lit_1_u32 \<open> 1_u32 \<close>
lemma \<open> lit_1_u32 = \<lbrakk> 1_u32 \<rbrakk> \<close> unfolding lit_1_u32_def by (rule refl)

urust_expr lit_0x2000_u32 \<open> 0x2000_u32 \<close>
lemma \<open> lit_0x2000_u32 = \<lbrakk> 0x2000_u32 \<rbrakk> \<close> unfolding lit_0x2000_u32_def by (rule refl)

urust_expr lit_0_u64 \<open> 0_u64 \<close>
lemma \<open> lit_0_u64 = \<lbrakk> 0_u64 \<rbrakk> \<close> unfolding lit_0_u64_def by (rule refl)

urust_expr lit_1_u64 \<open> 1_u64 \<close>
lemma \<open> lit_1_u64 = \<lbrakk> 1_u64 \<rbrakk> \<close> unfolding lit_1_u64_def by (rule refl)

urust_expr lit_0x2f0_u64 \<open> 0x2f0_u64 \<close>
lemma \<open> lit_0x2f0_u64 = \<lbrakk> 0x2f0_u64 \<rbrakk> \<close> unfolding lit_0x2f0_u64_def by (rule refl)

urust_expr lit_0_usize \<open> 0_usize \<close>
lemma \<open> lit_0_usize = \<lbrakk> 0_usize \<rbrakk> \<close> unfolding lit_0_usize_def by (rule refl)

urust_expr lit_1_usize \<open> 1_usize \<close>
lemma \<open> lit_1_usize = \<lbrakk> 1_usize \<rbrakk> \<close> unfolding lit_1_usize_def by (rule refl)

urust_expr lit_0xf_usize \<open> 0xffffffff0_usize \<close>
lemma \<open> lit_0xf_usize = \<lbrakk> 0xffffffff0_usize \<rbrakk> \<close> unfolding lit_0xf_usize_def by (rule refl)


section\<open> Unit (Corpus PART I, "Unit Literal") \<close>

urust_expr lit_unit \<open> () \<close>
lemma \<open> lit_unit = \<lbrakk> () \<rbrakk> \<close> unfolding lit_unit_def by (rule refl)


section\<open> Value antiquotation \<open>\<llangle>_\<rrangle>\<close> (Corpus PART I, "HOL Value Injection") \<close>

text\<open> A HOL value lifted to a µRust literal; word widths 8 / 32 / 64, a boolean, and a compound value. \<close>

urust_expr lit_aq_word \<open> \<llangle>0 :: 32 word\<rrangle> \<close>
lemma \<open> lit_aq_word = \<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding lit_aq_word_def by (rule refl)

urust_expr ext_aq64 \<open> \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> ext_aq64 = \<lbrakk> \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding ext_aq64_def by (rule refl)

urust_expr ext_aq8 \<open> \<llangle>255 :: 8 word\<rrangle> \<close>
lemma \<open> ext_aq8 = \<lbrakk> \<llangle>255 :: 8 word\<rrangle> \<rbrakk> \<close> unfolding ext_aq8_def by (rule refl)

urust_expr lit_aq_true \<open> \<llangle>True\<rrangle> \<close>
lemma \<open> lit_aq_true = \<lbrakk> \<llangle>True\<rrangle> \<rbrakk> \<close> unfolding lit_aq_true_def by (rule refl)

urust_expr ext_aqfalse \<open> \<llangle>False\<rrangle> \<close>
lemma \<open> ext_aqfalse = \<lbrakk> \<llangle>False\<rrangle> \<rbrakk> \<close> unfolding ext_aqfalse_def by (rule refl)

urust_expr lit_aq_some \<open> \<llangle>Some (0 :: nat)\<rrangle> \<close>
lemma \<open> lit_aq_some = \<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk> \<close> unfolding lit_aq_some_def by (rule refl)


section\<open> Expression antiquotation \<open>\<epsilon>\<open>_\<close>\<close> (Corpus PART I, "Boolean Literals") \<close>

text\<open> Passthrough (no \<open>literal\<close> wrapper): the body already denotes an \<open>expression\<close>. \<close>

urust_expr lit_eaq_true \<open> \<epsilon>\<open>Bool_Type.true\<close> \<close>
lemma \<open> lit_eaq_true = \<lbrakk> \<epsilon>\<open>Bool_Type.true\<close> \<rbrakk> \<close> unfolding lit_eaq_true_def by (rule refl)


section\<open> Bare identifiers at value position (dispatch reuse) \<close>

text\<open> Unregistered HOL constants: the parser emits a bare \<open>Free name\<close>, which \<open>check_term\<close> promotes to
the corresponding \<open>Const\<close> (exactly as the frontend's \<open>lookup_id_tr\<close> fallback does). Rows True / False /
None mirror Corpus PART I "Boolean Literals" / "Option and Result". \<close>

urust_expr lit_true  \<open> True \<close>
lemma \<open> lit_true  = \<lbrakk> True \<rbrakk> \<close> unfolding lit_true_def  by (rule refl)

urust_expr lit_false \<open> False \<close>
lemma \<open> lit_false = \<lbrakk> False \<rbrakk> \<close> unfolding lit_false_def by (rule refl)

urust_expr lit_none  \<open> None \<close>
lemma \<open> lit_none  = \<lbrakk> None \<rbrakk> \<close> unfolding lit_none_def  by (rule refl)

text\<open> A context-fixed free variable (unregistered, non-constant): stays a \<open>Free\<close>, with ctrl-click nav to
its \<open>fixes\<close> (D14). \<close>
context fixes foo :: nat
begin
urust_expr lit_ctx \<open> foo \<close>
lemma \<open> lit_ctx = \<lbrakk> foo \<rbrakk> \<close> unfolding lit_ctx_def by (rule refl)
end

text\<open> A registered \<open>micro_rust_notation\<close>: the parser emits a \<open>urust_dispatch\<close> marker that the
globally-installed \<open>term_check\<close> phases resolve to the registered backend -- the dispatch path,
reproduced without reimplementing dispatch. \<close>
definition my_backend :: nat where \<open> my_backend \<equiv> 7 \<close>
micro_rust_notation (literal) my_backend ("myReg")

urust_expr lit_reg \<open> myReg \<close>
lemma \<open> lit_reg = \<lbrakk> myReg \<rbrakk> \<close> unfolding lit_reg_def by (rule refl)


section\<open> Sequencing, `let` and `const` bindings \<close>

text\<open> Sequencing (Corpus PART I "Sequencing"): \<open>e1; e2\<close> -> \<open>sequence e1 e2\<close>; a trailing \<open>;\<close> ->
\<open>sequence e skip\<close> (\<open>skip = literal ()\<close>). \<close>

urust_expr seq_unit \<open> (); () \<close>
lemma \<open> seq_unit = \<lbrakk> (); () \<rbrakk> \<close> unfolding seq_unit_def by (rule refl)

urust_expr seq_trailing \<open> (); (); \<close>
lemma \<open> seq_trailing = \<lbrakk> (); (); \<rbrakk> \<close> unfolding seq_trailing_def by (rule refl)

text\<open> Plain immutable \<open>let x = e; k\<close> -> \<open>bind e (\<lambda>x. k)\<close> (HOAS); a bound-variable use in the body is
captured by the enclosing binder. An UNUSED binder's type is pinned via \<open>\<llangle>_ :: nat\<rrangle>\<close> (R1). \<close>

urust_expr let_use \<open> let x = 5; x \<close>
lemma \<open> let_use = \<lbrakk> let x = 5; x \<rbrakk> \<close> unfolding let_use_def by (rule refl)

urust_expr let_ab \<open> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<close>
lemma \<open> let_ab = \<lbrakk> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<rbrakk> \<close> unfolding let_ab_def by (rule refl)

text\<open> \<open>const x = e; k\<close> desugars byte-for-byte as \<open>let\<close> (Corpus PART I "Const Bindings"). \<close>

urust_expr const_foo \<open> const FOO = \<llangle>5 :: nat\<rrangle>; () \<close>
lemma \<open> const_foo = \<lbrakk> const FOO = \<llangle>5 :: nat\<rrangle>; () \<rbrakk> \<close> unfolding const_foo_def by (rule refl)

text\<open> Antiquotation capture under \<open>let\<close>: the HOL \<open>x\<close> inside \<open>\<llangle>x\<rrangle>\<close> is captured by the enclosing
binder (\<open>Term.lambda\<close> over \<open>Free x\<close>), both as a bare \<open>\<llangle>x\<rrangle>\<close> and buried in a larger body. \<close>

urust_expr let_cap \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<close>
lemma \<open> let_cap = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<rbrakk> \<close> unfolding let_cap_def by (rule refl)

urust_expr let_cap_deep \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<close>
lemma \<open> let_cap_deep = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<rbrakk> \<close> unfolding let_cap_deep_def by (rule refl)


section\<open> Pure-value operators (Corpus PART I: Arithmetic / Bitwise / Comparison / Boolean) \<close>

text\<open> Each \<open>a <op> b\<close> -> the frontend's operator const applied to the two elaborated operands. Word
operands are pinned via value antiquotations (no unused binders, so no type pins needed). \<close>

subsection\<open> Arithmetic \<close>

urust_expr op_add \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_add = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_add_def by (rule refl)

urust_expr op_add3 \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> + \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_add3 = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> + \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_add3_def by (rule refl)

urust_expr op_sub \<open> \<llangle>5 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_sub = \<lbrakk> \<llangle>5 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_sub_def by (rule refl)

urust_expr op_mul \<open> \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_mul = \<lbrakk> \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_mul_def by (rule refl)

urust_expr op_div \<open> \<llangle>6 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_div = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_div_def by (rule refl)

urust_expr op_mod \<open> \<llangle>7 :: 32 word\<rrangle> % \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_mod = \<lbrakk> \<llangle>7 :: 32 word\<rrangle> % \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_mod_def by (rule refl)

text\<open> Precedence: \<open>*\<close> binds tighter than \<open>+\<close>, so this parses as \<open>a + (b * c)\<close>. \<close>
urust_expr op_precmul \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_precmul = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> * \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_precmul_def by (rule refl)

subsection\<open> Bitwise and shifts (shift RHS is a \<open>64 word\<close>) \<close>

urust_expr op_band \<open> \<llangle>6 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_band = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_band_def by (rule refl)

urust_expr op_bor \<open> \<llangle>6 :: 32 word\<rrangle> | \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_bor = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> | \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_bor_def by (rule refl)

urust_expr op_bxor \<open> \<llangle>6 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> op_bxor = \<lbrakk> \<llangle>6 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_bxor_def by (rule refl)

urust_expr op_shl \<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>4 :: 64 word\<rrangle> \<close>
lemma \<open> op_shl = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> << \<llangle>4 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding op_shl_def by (rule refl)

urust_expr op_shr \<open> \<llangle>16 :: 32 word\<rrangle> >> \<llangle>2 :: 64 word\<rrangle> \<close>
lemma \<open> op_shr = \<lbrakk> \<llangle>16 :: 32 word\<rrangle> >> \<llangle>2 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding op_shr_def by (rule refl)

subsection\<open> Comparison (non-associative; word operands, boolean-expression result) \<close>

urust_expr op_lt \<open> \<llangle>1 :: 32 word\<rrangle> < \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_lt = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> < \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_lt_def by (rule refl)

urust_expr op_le \<open> \<llangle>1 :: 32 word\<rrangle> <= \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_le = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> <= \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_le_def by (rule refl)

urust_expr op_gt \<open> \<llangle>2 :: 32 word\<rrangle> > \<llangle>1 :: 32 word\<rrangle> \<close>
lemma \<open> op_gt = \<lbrakk> \<llangle>2 :: 32 word\<rrangle> > \<llangle>1 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_gt_def by (rule refl)

urust_expr op_ge \<open> \<llangle>2 :: 32 word\<rrangle> >= \<llangle>1 :: 32 word\<rrangle> \<close>
lemma \<open> op_ge = \<lbrakk> \<llangle>2 :: 32 word\<rrangle> >= \<llangle>1 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_ge_def by (rule refl)

urust_expr op_eq \<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>1 :: 32 word\<rrangle> \<close>
lemma \<open> op_eq = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>1 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_eq_def by (rule refl)

urust_expr op_ne \<open> \<llangle>1 :: 32 word\<rrangle> != \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> op_ne = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> != \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding op_ne_def by (rule refl)

subsection\<open> Boolean connectives and unary \<open>!\<close> (all four truth-table rows each; \<open>!!\<close> = \<open>!(!_)\<close>) \<close>

urust_expr op_and \<open> True && False \<close>
lemma \<open> op_and = \<lbrakk> True && False \<rbrakk> \<close> unfolding op_and_def by (rule refl)

urust_expr ext_and_tt \<open> True && True \<close>
lemma \<open> ext_and_tt = \<lbrakk> True && True \<rbrakk> \<close> unfolding ext_and_tt_def by (rule refl)

urust_expr ext_and_ft \<open> False && True \<close>
lemma \<open> ext_and_ft = \<lbrakk> False && True \<rbrakk> \<close> unfolding ext_and_ft_def by (rule refl)

urust_expr and_ff \<open> False && False \<close>
lemma \<open> and_ff = \<lbrakk> False && False \<rbrakk> \<close> unfolding and_ff_def by (rule refl)

urust_expr op_or \<open> True || False \<close>
lemma \<open> op_or = \<lbrakk> True || False \<rbrakk> \<close> unfolding op_or_def by (rule refl)

urust_expr ext_or_tt \<open> True || True \<close>
lemma \<open> ext_or_tt = \<lbrakk> True || True \<rbrakk> \<close> unfolding ext_or_tt_def by (rule refl)

urust_expr or_ft \<open> False || True \<close>
lemma \<open> or_ft = \<lbrakk> False || True \<rbrakk> \<close> unfolding or_ft_def by (rule refl)

urust_expr ext_or_ff \<open> False || False \<close>
lemma \<open> ext_or_ff = \<lbrakk> False || False \<rbrakk> \<close> unfolding ext_or_ff_def by (rule refl)

urust_expr op_not \<open> !True \<close>
lemma \<open> op_not = \<lbrakk> !True \<rbrakk> \<close> unfolding op_not_def by (rule refl)

urust_expr ext_notfalse \<open> !False \<close>
lemma \<open> ext_notfalse = \<lbrakk> !False \<rbrakk> \<close> unfolding ext_notfalse_def by (rule refl)

urust_expr op_notnot \<open> !!True \<close>
lemma \<open> op_notnot = \<lbrakk> !!True \<rbrakk> \<close> unfolding op_notnot_def by (rule refl)

text\<open> Precedence: \<open>&&\<close> binds tighter than \<open>||\<close>; unary \<open>!\<close> over a parenthesized comparison. \<close>
urust_expr op_prec \<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>
lemma \<open> op_prec = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk> \<close> unfolding op_prec_def by (rule refl)

urust_expr op_mixed \<open> !(\<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle>) \<close>
lemma \<open> op_mixed = \<lbrakk> !(\<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle>) \<rbrakk> \<close> unfolding op_mixed_def by (rule refl)

subsection\<open> Let-bound variables as operator operands (bound-var use in operator position) \<close>

urust_expr ext_let_add \<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<close>
lemma \<open> ext_let_add = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a + b \<rbrakk> \<close> unfolding ext_let_add_def by (rule refl)

urust_expr ext_let_sub \<open> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<close>
lemma \<open> ext_let_sub = \<lbrakk> let a = \<llangle>5 :: 32 word\<rrangle>; let b = \<llangle>3 :: 32 word\<rrangle>; a - b \<rbrakk> \<close> unfolding ext_let_sub_def by (rule refl)

urust_expr ext_let_mul \<open> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<close>
lemma \<open> ext_let_mul = \<lbrakk> let a = \<llangle>3 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a * b \<rbrakk> \<close> unfolding ext_let_mul_def by (rule refl)

urust_expr lop_div \<open> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<close>
lemma \<open> lop_div = \<lbrakk> let a = \<llangle>12 :: 32 word\<rrangle>; let b = \<llangle>4 :: 32 word\<rrangle>; a / b \<rbrakk> \<close> unfolding lop_div_def by (rule refl)

urust_expr lop_mod \<open> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<close>
lemma \<open> lop_mod = \<lbrakk> let a = \<llangle>17 :: 32 word\<rrangle>; let b = \<llangle>5 :: 32 word\<rrangle>; a % b \<rbrakk> \<close> unfolding lop_mod_def by (rule refl)

urust_expr ext_let_band \<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<close>
lemma \<open> ext_let_band = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a & b \<rbrakk> \<close> unfolding ext_let_band_def by (rule refl)

urust_expr lop_bor \<open> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<close>
lemma \<open> lop_bor = \<lbrakk> let a = \<llangle>0xF0 :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a | b \<rbrakk> \<close> unfolding lop_bor_def by (rule refl)

urust_expr lop_bxor \<open> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<close>
lemma \<open> lop_bxor = \<lbrakk> let a = \<llangle>0xFF :: 32 word\<rrangle>; let b = \<llangle>0x0F :: 32 word\<rrangle>; a ^ b \<rbrakk> \<close> unfolding lop_bxor_def by (rule refl)

urust_expr ext_let_shl \<open> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<close>
lemma \<open> ext_let_shl = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; a << \<llangle>4 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding ext_let_shl_def by (rule refl)

urust_expr lop_shr \<open> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<close>
lemma \<open> lop_shr = \<lbrakk> let a = \<llangle>16 :: 32 word\<rrangle>; a >> \<llangle>2 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding lop_shr_def by (rule refl)

urust_expr ext_let_not \<open> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<close>
lemma \<open> ext_let_not = \<lbrakk> let a = \<llangle>0x00 :: 8 word\<rrangle>; !a \<rbrakk> \<close> unfolding ext_let_not_def by (rule refl)

urust_expr ext_let_cmp \<open> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a < b \<close>
lemma \<open> ext_let_cmp = \<lbrakk> let a = \<llangle>1 :: 32 word\<rrangle>; let b = \<llangle>2 :: 32 word\<rrangle>; a < b \<rbrakk> \<close> unfolding ext_let_cmp_def by (rule refl)

subsection\<open> Context-fixed variables as operator operands \<close>
context fixes m n :: \<open>nat\<close> and x y :: \<open>64 word\<close> and w :: \<open>32 word\<close>
begin

urust_expr ext_cmp_mn \<open> m == n \<close>
lemma \<open> ext_cmp_mn = \<lbrakk> m == n \<rbrakk> \<close> unfolding ext_cmp_mn_def by (rule refl)

urust_expr ext_cmp_ne \<open> m != n \<close>
lemma \<open> ext_cmp_ne = \<lbrakk> m != n \<rbrakk> \<close> unfolding ext_cmp_ne_def by (rule refl)

urust_expr ext_cmp_notmn \<open> !(m == n) \<close>
lemma \<open> ext_cmp_notmn = \<lbrakk> !(m == n) \<rbrakk> \<close> unfolding ext_cmp_notmn_def by (rule refl)

urust_expr ord_lt \<open> x < y \<close>
lemma \<open> ord_lt = \<lbrakk> x < y \<rbrakk> \<close> unfolding ord_lt_def by (rule refl)

urust_expr ord_le \<open> x <= y \<close>
lemma \<open> ord_le = \<lbrakk> x <= y \<rbrakk> \<close> unfolding ord_le_def by (rule refl)

urust_expr ord_gt \<open> x > y \<close>
lemma \<open> ord_gt = \<lbrakk> x > y \<rbrakk> \<close> unfolding ord_gt_def by (rule refl)

urust_expr ord_ge \<open> x >= y \<close>
lemma \<open> ord_ge = \<lbrakk> x >= y \<rbrakk> \<close> unfolding ord_ge_def by (rule refl)

urust_expr ext_cmp_w0 \<open> w > \<llangle>0 :: 32 word\<rrangle> \<close>
lemma \<open> ext_cmp_w0 = \<lbrakk> w > \<llangle>0 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding ext_cmp_w0_def by (rule refl)

urust_expr ext_not_add \<open> !x + y \<close>
lemma \<open> ext_not_add = \<lbrakk> !x + y \<rbrakk> \<close> unfolding ext_not_add_def by (rule refl)  \<comment>\<open> (!x) + y : prefix ! tighter than + \<close>

urust_expr ext_not_nested \<open> !(!x == x^y) \<close>
lemma \<open> ext_not_nested = \<lbrakk> !(!x == x^y) \<rbrakk> \<close> unfolding ext_not_nested_def by (rule refl)
end

subsection\<open> Operator precedence and associativity probes (grouping = frontend, kernel-checked) \<close>

text\<open> Each row proves the new parser groups a MIXED-operator expression IDENTICALLY to the frontend
(the oracle). Together they pin every adjacent precedence tier and each associativity, against the
frontend fixities (Micro_Rust_Syntax.thy:543-603):
  \<open>|| (infixl 42)\<close> < \<open>&& (43)\<close> < \<open>== != < <= > >= (infix 44, NON-assoc)\<close> < \<open>| (45)\<close> < \<open>^ (46)\<close> <
  \<open>& (47)\<close> < \<open><< >> (48)\<close> < \<open>+ - (49)\<close> < \<open>* / % (50)\<close>; prefix \<open>!\<close> (300) tighter than all binary.
Comparison non-associativity (\<open>a == b == c\<close>) is rejected by BOTH (a parse error), so it is checked
out-of-band, not as a refl row. \<open>op_add3\<close>/\<open>op_precmul\<close>/\<open>op_prec\<close> above cover \<open>+\<close>-assoc / \<open>*\<close>>\<open>+\<close> /
\<open>&&\<close>>\<open>||\<close>. \<close>

urust_expr prec_sub_assoc \<open> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> prec_sub_assoc = \<lbrakk> \<llangle>9 :: 32 word\<rrangle> - \<llangle>3 :: 32 word\<rrangle> - \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding prec_sub_assoc_def by (rule refl)

urust_expr prec_div_assoc \<open> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> prec_div_assoc = \<lbrakk> \<llangle>12 :: 32 word\<rrangle> / \<llangle>3 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding prec_div_assoc_def by (rule refl)

urust_expr prec_shl_assoc \<open> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> prec_shl_assoc = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding prec_shl_assoc_def by (rule refl)

urust_expr prec_and_assoc \<open> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>
lemma \<open> prec_and_assoc = \<lbrakk> \<llangle>True\<rrangle> && \<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk> \<close> unfolding prec_and_assoc_def by (rule refl)

urust_expr prec_or_assoc \<open> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<close>
lemma \<open> prec_or_assoc = \<lbrakk> \<llangle>True\<rrangle> || \<llangle>True\<rrangle> || \<llangle>False\<rrangle> \<rbrakk> \<close> unfolding prec_or_assoc_def by (rule refl)

urust_expr prec_add_shl \<open> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> prec_add_shl = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding prec_add_shl_def by (rule refl)     \<comment>\<open> (a + b) << c :  + (49) tighter than << (48) \<close>

urust_expr prec_shl_and \<open> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<close>
lemma \<open> prec_shl_and = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> & \<llangle>2 :: 32 word\<rrangle> << \<llangle>1 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding prec_shl_and_def by (rule refl)     \<comment>\<open> a & (b << c) :  << (48) tighter than & (47) \<close>

urust_expr prec_and_xor \<open> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> prec_and_xor = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> ^ \<llangle>2 :: 32 word\<rrangle> & \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding prec_and_xor_def by (rule refl)     \<comment>\<open> a ^ (b & c) :  & (47) tighter than ^ (46) \<close>

urust_expr prec_xor_or \<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> prec_xor_or = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> ^ \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding prec_xor_or_def by (rule refl)      \<comment>\<open> a | (b ^ c) :  ^ (46) tighter than | (45) \<close>

urust_expr prec_or_cmp \<open> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> prec_or_cmp = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> | \<llangle>2 :: 32 word\<rrangle> == \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding prec_or_cmp_def by (rule refl)      \<comment>\<open> (a | b) == c :  | (45) tighter than == (44) \<close>

urust_expr prec_cmp_and \<open> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<close>
lemma \<open> prec_cmp_and = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> && \<llangle>True\<rrangle> \<rbrakk> \<close> unfolding prec_cmp_and_def by (rule refl)     \<comment>\<open> (a == b) && c :  == (44) tighter than && (43) \<close>

urust_expr prec_not_and \<open> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<close>
lemma \<open> prec_not_and = \<lbrakk> !\<llangle>True\<rrangle> && \<llangle>False\<rrangle> \<rbrakk> \<close> unfolding prec_not_and_def by (rule refl)     \<comment>\<open> (!a) && b :  prefix ! tighter than && \<close>

urust_expr prec_not_cmp \<open> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<close>
lemma \<open> prec_not_cmp = \<lbrakk> !\<llangle>True\<rrangle> == \<llangle>False\<rrangle> \<rbrakk> \<close> unfolding prec_not_cmp_def by (rule refl)     \<comment>\<open> (!a) == b :  prefix ! tighter than == \<close>


section\<open> Block expressions (Corpus "Scoping and Block Expressions") \<close>

text\<open> Blocks ERASE: the frontend \<open>_urust_scoping\<close> is the identity (SE:360-362), so \<open>{ e }\<close> elaborates
to exactly \<open>\<lbrakk> e \<rbrakk>\<close> -- no \<open>scoped\<close> wrapper. Statements inside sequence via \<open>;\<close>. Blocks (frontend
priority 1000) are valid operator operands (AGREE). \<close>

urust_expr blk_lit \<open> { \<llangle>1 :: nat\<rrangle> } \<close>
lemma \<open> blk_lit = \<lbrakk> { \<llangle>1 :: nat\<rrangle> } \<rbrakk> \<close> unfolding blk_lit_def by (rule refl)

urust_expr blk_seq \<open> { (); () } \<close>
lemma \<open> blk_seq = \<lbrakk> { (); () } \<rbrakk> \<close> unfolding blk_seq_def by (rule refl)

urust_expr blk_let \<open> { let x = \<llangle>5 :: nat\<rrangle>; x } \<close>
lemma \<open> blk_let = \<lbrakk> { let x = \<llangle>5 :: nat\<rrangle>; x } \<rbrakk> \<close> unfolding blk_let_def by (rule refl)

urust_expr ext_blk_bare \<open> { 42 } \<close>
lemma \<open> ext_blk_bare = \<lbrakk> { 42 } \<rbrakk> \<close> unfolding ext_blk_bare_def by (rule refl)

urust_expr ext_blk_nest \<open> {{ 42 }} \<close>
lemma \<open> ext_blk_nest = \<lbrakk> {{ 42 }} \<rbrakk> \<close> unfolding ext_blk_nest_def by (rule refl)

urust_expr ext_blk_deep \<open> {{{{{ \<llangle>1 :: nat\<rrangle> }}}}} \<close>
lemma \<open> ext_blk_deep = \<lbrakk> {{{{{ \<llangle>1 :: nat\<rrangle> }}}}} \<rbrakk> \<close> unfolding ext_blk_deep_def by (rule refl)

urust_expr ext_blk_op \<open> { \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_blk_op = \<lbrakk> { \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_blk_op_def by (rule refl)

urust_expr ext_blk_operand_l \<open> { \<llangle>1 :: 32 word\<rrangle> } + \<llangle>2 :: 32 word\<rrangle> \<close>
lemma \<open> ext_blk_operand_l = \<lbrakk> { \<llangle>1 :: 32 word\<rrangle> } + \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close> unfolding ext_blk_operand_l_def by (rule refl)

urust_expr ext_blk_operand_r \<open> \<llangle>1 :: 32 word\<rrangle> + { \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_blk_operand_r = \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + { \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_blk_operand_r_def by (rule refl)

urust_expr ext_not_blk \<open> !{ \<llangle>True\<rrangle> } \<close>
lemma \<open> ext_not_blk = \<lbrakk> !{ \<llangle>True\<rrangle> } \<rbrakk> \<close> unfolding ext_not_blk_def by (rule refl)


section\<open> \<open>if\<close> / \<open>else\<close> (Corpus "Control Flow - Conditionals") \<close>

text\<open> \<open>if c { t } else { e }\<close> -> \<open>two_armed_conditional \<lbrakk>c\<rbrakk> \<lbrakk>t\<rbrakk> \<lbrakk>e\<rbrakk>\<close> (Bool_Type.thy:30-35, via
SE:364-365). One-armed \<open>if c { t }\<close> fills the missing else with \<open>skip = literal ()\<close> (NOT the
\<open>one_armed_conditional\<close> const); since \<open>two_armed_conditional\<close> needs both arms at the SAME value type and
the implicit else is unit-typed, a no-\<open>else\<close> \<open>if\<close> is only well-typed with a UNIT then-branch -- exactly
Rust's rule. else-if desugars to a nested \<open>if\<close> (SYN:661-662). \<close>

urust_expr if_two \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> } \<close>
lemma \<open> if_two = \<lbrakk> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> } \<rbrakk> \<close> unfolding if_two_def by (rule refl)

urust_expr if_one \<open> if \<llangle>True\<rrangle> { () } \<close>
lemma \<open> if_one = \<lbrakk> if \<llangle>True\<rrangle> { () } \<rbrakk> \<close> unfolding if_one_def by (rule refl)

urust_expr ext_if_one_bare \<open> if True { () } \<close>
lemma \<open> ext_if_one_bare = \<lbrakk> if True { () } \<rbrakk> \<close> unfolding ext_if_one_bare_def by (rule refl)

urust_expr if_elif \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else if \<llangle>False\<rrangle> { \<llangle>2 :: nat\<rrangle> } else { \<llangle>3 :: nat\<rrangle> } \<close>
lemma \<open> if_elif = \<lbrakk> if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else if \<llangle>False\<rrangle> { \<llangle>2 :: nat\<rrangle> } else { \<llangle>3 :: nat\<rrangle> } \<rbrakk> \<close> unfolding if_elif_def by (rule refl)

urust_expr if_elif2 \<open> if \<llangle>True\<rrangle> { () } else if \<llangle>False\<rrangle> { () } \<close>  \<comment>\<open> else-if, no final else (unit arms) \<close>
lemma \<open> if_elif2 = \<lbrakk> if \<llangle>True\<rrangle> { () } else if \<llangle>False\<rrangle> { () } \<rbrakk> \<close> unfolding if_elif2_def by (rule refl)

urust_expr ext_elif_word \<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_elif_word = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if True { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_elif_word_def by (rule refl)

urust_expr ext_elif3 \<open> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<close>
lemma \<open> ext_elif3 = \<lbrakk> if False { \<llangle>0 :: 32 word\<rrangle> } else if False { \<llangle>1 :: 32 word\<rrangle> } else if True { \<llangle>2 :: 32 word\<rrangle> } else { \<llangle>3 :: 32 word\<rrangle> } \<rbrakk> \<close> unfolding ext_elif3_def by (rule refl)

text\<open> Condition is an arbitrary expression (comparison / parenthesized boolean / an \<open>if\<close>-expression);
nested \<open>if\<close> in a branch; deep block branch; \<open>if\<close> as a \<open>let\<close>-RHS; \<open>if\<close> sequenced inside a block. \<close>

urust_expr if_cmp \<open> if \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> { () } else { () } \<close>
lemma \<open> if_cmp = \<lbrakk> if \<llangle>1 :: 32 word\<rrangle> == \<llangle>2 :: 32 word\<rrangle> { () } else { () } \<rbrakk> \<close> unfolding if_cmp_def by (rule refl)

urust_expr if_nest \<open> if \<llangle>True\<rrangle> { if \<llangle>False\<rrangle> { () } else { () } } else { () } \<close>
lemma \<open> if_nest = \<lbrakk> if \<llangle>True\<rrangle> { if \<llangle>False\<rrangle> { () } else { () } } else { () } \<rbrakk> \<close> unfolding if_nest_def by (rule refl)

urust_expr ext_if_par_cond \<open> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<close>
lemma \<open> ext_if_par_cond = \<lbrakk> if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) { \<epsilon>\<open>\<up>0\<close> } else { \<epsilon>\<open>\<up>0\<close> } \<rbrakk> \<close> unfolding ext_if_par_cond_def by (rule refl)

urust_expr ext_if_deepblock \<open> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<close>
lemma \<open> ext_if_deepblock = \<lbrakk> if True || !True { {{{{{{{{{{ 42 }}}}}}}}}} } else { 0 } \<rbrakk> \<close> unfolding ext_if_deepblock_def by (rule refl)

urust_expr ext_if_cond \<open> if if \<llangle>True\<rrangle> { \<llangle>True\<rrangle> } else { \<llangle>False\<rrangle> } { () } else { () } \<close>  \<comment>\<open> if-expr as condition \<close>
lemma \<open> ext_if_cond = \<lbrakk> if if \<llangle>True\<rrangle> { \<llangle>True\<rrangle> } else { \<llangle>False\<rrangle> } { () } else { () } \<rbrakk> \<close> unfolding ext_if_cond_def by (rule refl)

urust_expr ext_let_if \<open> let x = if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }; x \<close>
lemma \<open> ext_let_if = \<lbrakk> let x = if \<llangle>True\<rrangle> { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }; x \<rbrakk> \<close> unfolding ext_let_if_def by (rule refl)

urust_expr ext_seq_if \<open> { if \<llangle>True\<rrangle> { () } else { () }; () } \<close>
lemma \<open> ext_seq_if = \<lbrakk> { if \<llangle>True\<rrangle> { () } else { () }; () } \<rbrakk> \<close> unfolding ext_seq_if_def by (rule refl)


section\<open> Function calls (Corpus "Functions", "Option and Result") \<close>

text\<open> \<open>f(a0, ..., a{N-1})\<close> -> \<open>funcallN f \<lbrakk>a0\<rbrakk> ... \<lbrakk>a{N-1}\<rbrakk>\<close> (Core_Syntax.thy:503-587). The callee
resolves in the NFunction (\<open>call\<close>) dispatch context and is NOT \<open>literal\<close>-wrapped; arguments are ordinary
value expressions (so nested calls fall out of the recursion). To keep the emitted \<open>definition\<close>
well-formed (R1), callee value types are concrete (\<open>64 word\<close>) and arguments are pinned. Concrete callees
are built with \<open>lift_funN\<close> (Core_Expression.thy:404-445), the idiom the corpus uses. \<close>

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

text\<open> Arity 0..5, unregistered global-constant callee: both the parser (NFunction lookup miss ->
\<open>Syntax.parse_term\<close>) and the frontend (\<open>lookup_id_tr\<close> miss -> bare \<open>Free\<close> promoted by \<open>decode_term\<close>)
resolve the bare name to the SAME \<open>Const\<close>. \<close>
urust_expr call0 \<open> cf0() \<close>
lemma \<open> call0 = \<lbrakk> cf0() \<rbrakk> \<close> unfolding call0_def by (rule refl)

urust_expr call1 \<open> cf1(\<llangle>1 :: 64 word\<rrangle>) \<close>
lemma \<open> call1 = \<lbrakk> cf1(\<llangle>1 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call1_def by (rule refl)

urust_expr call2 \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> call2 = \<lbrakk> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call2_def by (rule refl)

urust_expr call3 \<open> cf3(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>) \<close>
lemma \<open> call3 = \<lbrakk> cf3(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call3_def by (rule refl)

urust_expr call4 \<open> cf4(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>, \<llangle>4 :: 64 word\<rrangle>) \<close>
lemma \<open> call4 = \<lbrakk> cf4(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>, \<llangle>4 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call4_def by (rule refl)

urust_expr call5 \<open> cf5(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>, \<llangle>4 :: 64 word\<rrangle>, \<llangle>5 :: 64 word\<rrangle>) \<close>
lemma \<open> call5 = \<lbrakk> cf5(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>, \<llangle>4 :: 64 word\<rrangle>, \<llangle>5 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call5_def by (rule refl)

text\<open> Nested call \<open>f(g(c), b)\<close>: the inner call is an ordinary argument expression. \<close>
urust_expr call_nested \<open> cf2(cf1(\<llangle>1 :: 64 word\<rrangle>), \<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> call_nested = \<lbrakk> cf2(cf1(\<llangle>1 :: 64 word\<rrangle>), \<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_nested_def by (rule refl)

text\<open> Registered \<open>(call)\<close>-notation callees: the parser emits a \<open>urust_dispatch\<close> NFunction marker resolved
by the installed \<open>term_check\<close> phases -- the \<open>myReg\<close> dispatch path, in call context. Both a locally
registered notation and the std-library \<open>Some\<close> / \<open>Ok\<close> / \<open>Err\<close> constructors (\<open>lift_fun1\<close> notations). \<close>
micro_rust_notation (call) cf1 ("regCall")
urust_expr call_reg \<open> regCall(\<llangle>3 :: 64 word\<rrangle>) \<close>
lemma \<open> call_reg = \<lbrakk> regCall(\<llangle>3 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_reg_def by (rule refl)

urust_expr call_some \<open> Some(\<llangle>42 :: nat\<rrangle>) \<close>
lemma \<open> call_some = \<lbrakk> Some(\<llangle>42 :: nat\<rrangle>) \<rbrakk> \<close> unfolding call_some_def by (rule refl)

urust_expr call_ok \<open> Ok(\<llangle>42 :: nat\<rrangle>) \<close>
lemma \<open> call_ok = \<lbrakk> Ok(\<llangle>42 :: nat\<rrangle>) \<rbrakk> \<close> unfolding call_ok_def by (rule refl)

urust_expr call_err \<open> Err(\<llangle>42 :: nat\<rrangle>) \<close>
lemma \<open> call_err = \<lbrakk> Err(\<llangle>42 :: nat\<rrangle>) \<rbrakk> \<close> unfolding call_err_def by (rule refl)

text\<open> A \<open>let\<close>-bound callee: lexical scope wins (env \<open>Free\<close>, no dispatch, no \<open>literal\<close> wrapper), matching
the frontend's witness-precedence for a bound name in call position. \<close>
urust_expr call_letbound \<open> let h = \<llangle>cf1\<rrangle>; h(\<llangle>4 :: 64 word\<rrangle>) \<close>
lemma \<open> call_letbound = \<lbrakk> let h = \<llangle>cf1\<rrangle>; h(\<llangle>4 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_letbound_def by (rule refl)

text\<open> Context-fixed callees (function-typed frees): stay a \<open>Free\<close> on both sides (the
\<open>Syntax.parse_term\<close> / \<open>lookup_free\<close> fallback). A \<open>64 word\<close> callee; and (Corpus PART I "Unit Literal")
callees applied to unit / boolean literal arguments. \<close>
context fixes g :: \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
begin
urust_expr call_ctx \<open> g(\<llangle>5 :: 64 word\<rrangle>) \<close>
lemma \<open> call_ctx = \<lbrakk> g(\<llangle>5 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_ctx_def by (rule refl)
end

context
  fixes uf :: \<open>unit \<Rightarrow> (unit, unit, unit, unit, unit) function_body\<close>
  fixes ug :: \<open>unit \<Rightarrow> bool \<Rightarrow> (unit, unit, unit, unit, unit) function_body\<close>
begin
urust_expr call_funit \<open> uf(()) \<close>
lemma \<open> call_funit = \<lbrakk> uf(()) \<rbrakk> \<close> unfolding call_funit_def by (rule refl)

urust_expr call_gunitbool \<open> ug((), True) \<close>
lemma \<open> call_gunitbool = \<lbrakk> ug((), True) \<rbrakk> \<close> unfolding call_gunitbool_def by (rule refl)
end


section\<open> Method calls (Corpus "Method-Style Calls") \<close>

text\<open> \<open>recv.m(args)\<close> desugars to a plain call to the method name \<open>m\<close> (NFunction context) with the
RECEIVER PREPENDED as the first argument (SE:380-381, 416-417): \<open>x.m(a) = funcall2 m \<up>x \<up>a\<close>,
\<open>x.m() = funcall1 m \<up>x\<close>. Reuses \<open>cf1\<close> / \<open>cf2\<close> as method backends. Method access binds tighter than
operators. Field access \<open>x.f\<close> (no parens) is a DIFFERENT construct (NField/lens), deferred (see D-6). \<close>

urust_expr mcall0 \<open> \<llangle>5 :: 64 word\<rrangle>.cf1() \<close>
lemma \<open> mcall0 = \<lbrakk> \<llangle>5 :: 64 word\<rrangle>.cf1() \<rbrakk> \<close> unfolding mcall0_def by (rule refl)

urust_expr mcall1 \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> mcall1 = \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding mcall1_def by (rule refl)

text\<open> Method on a call result (receiver is itself a call), a method chain \<open>x.m().n()\<close>, and precedence
(\<open>.\<close> binds tighter than \<open>+\<close>). \<close>
urust_expr mcall_on_call \<open> cf1(\<llangle>1 :: 64 word\<rrangle>).cf1() \<close>
lemma \<open> mcall_on_call = \<lbrakk> cf1(\<llangle>1 :: 64 word\<rrangle>).cf1() \<rbrakk> \<close> unfolding mcall_on_call_def by (rule refl)

urust_expr mcall_chain \<open> \<llangle>5 :: 64 word\<rrangle>.cf1().cf1() \<close>
lemma \<open> mcall_chain = \<lbrakk> \<llangle>5 :: 64 word\<rrangle>.cf1().cf1() \<rbrakk> \<close> unfolding mcall_chain_def by (rule refl)

urust_expr mcall_operand \<open> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> \<close>
lemma \<open> mcall_operand = \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding mcall_operand_def by (rule refl)

text\<open> Context-fixed method name + receiver (Corpus PART I "Equality"): arity-0 method, and a method call
in an \<open>if\<close> condition compared with \<open>==\<close>. \<close>
context fixes m n :: \<open>nat\<close> and h :: \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
begin
urust_expr mcall_ctx \<open> m.h() \<close>
lemma \<open> mcall_ctx = \<lbrakk> m.h() \<rbrakk> \<close> unfolding mcall_ctx_def by (rule refl)

urust_expr mcall_if \<open> if m.h() == n { m } else { n } \<close>
lemma \<open> mcall_if = \<lbrakk> if m.h() == n { m } else { n } \<rbrakk> \<close> unfolding mcall_if_def by (rule refl)
end


section\<open> Cross-feature robustness (calls / methods x operators / control-flow / binders) \<close>

text\<open> Deeper combinations of the implemented tiers, all \<open>refl\<close> against the frontend golden. These stress
the interaction points most likely to hide a bug: operator precedence with call/method operands (calls at
result-priority 999 / methods at 1000 ARE valid operator operands -- unlike \<open>if\<close>, D-1), binder CAPTURE
inside call/method arguments and receivers (the elaborator must thread \<open>ctxt env\<close> through every arg), and
deep argument nesting. Callees are the concrete \<open>cf0\<close> / \<open>cf1\<close> / \<open>cf2\<close> above; argument value types are
pinned (R1). \<close>

subsection\<open> Calls as / with operators (precedence) \<close>

urust_expr rc_arg_op \<open> cf1(\<llangle>1 :: 64 word\<rrangle> + \<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> rc_arg_op = \<lbrakk> cf1(\<llangle>1 :: 64 word\<rrangle> + \<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding rc_arg_op_def by (rule refl)

urust_expr rc_call_plus_call \<open> cf1(\<llangle>10 :: 64 word\<rrangle>) + cf1(\<llangle>20 :: 64 word\<rrangle>) \<close>
lemma \<open> rc_call_plus_call = \<lbrakk> cf1(\<llangle>10 :: 64 word\<rrangle>) + cf1(\<llangle>20 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding rc_call_plus_call_def by (rule refl)

urust_expr rc_call_times \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) * \<llangle>3 :: 64 word\<rrangle> \<close>
lemma \<open> rc_call_times = \<lbrakk> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) * \<llangle>3 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding rc_call_times_def by (rule refl)

urust_expr rc_bang_cmp \<open> !(cf1(\<llangle>1 :: 64 word\<rrangle>) == cf1(\<llangle>2 :: 64 word\<rrangle>)) \<close>
lemma \<open> rc_bang_cmp = \<lbrakk> !(cf1(\<llangle>1 :: 64 word\<rrangle>) == cf1(\<llangle>2 :: 64 word\<rrangle>)) \<rbrakk> \<close> unfolding rc_bang_cmp_def by (rule refl)

subsection\<open> Calls in control-flow and binder positions \<close>

urust_expr rc_call_let \<open> let r = cf1(\<llangle>7 :: 64 word\<rrangle>); r \<close>
lemma \<open> rc_call_let = \<lbrakk> let r = cf1(\<llangle>7 :: 64 word\<rrangle>); r \<rbrakk> \<close> unfolding rc_call_let_def by (rule refl)

urust_expr rc_call_if \<open> if \<llangle>True\<rrangle> { cf0() } else { cf1(\<llangle>1 :: 64 word\<rrangle>) } \<close>
lemma \<open> rc_call_if = \<lbrakk> if \<llangle>True\<rrangle> { cf0() } else { cf1(\<llangle>1 :: 64 word\<rrangle>) } \<rbrakk> \<close> unfolding rc_call_if_def by (rule refl)

urust_expr rc_call_block \<open> { cf0(); cf1(\<llangle>1 :: 64 word\<rrangle>) } \<close>
lemma \<open> rc_call_block = \<lbrakk> { cf0(); cf1(\<llangle>1 :: 64 word\<rrangle>) } \<rbrakk> \<close> unfolding rc_call_block_def by (rule refl)

urust_expr rc_if_arg \<open> cf1((if \<llangle>True\<rrangle> { \<llangle>1 :: 64 word\<rrangle> } else { \<llangle>2 :: 64 word\<rrangle> })) \<close>
lemma \<open> rc_if_arg = \<lbrakk> cf1((if \<llangle>True\<rrangle> { \<llangle>1 :: 64 word\<rrangle> } else { \<llangle>2 :: 64 word\<rrangle> })) \<rbrakk> \<close> unfolding rc_if_arg_def by (rule refl)

subsection\<open> Deep argument nesting \<close>

urust_expr rc_deep3 \<open> cf1(cf1(cf1(\<llangle>1 :: 64 word\<rrangle>))) \<close>
lemma \<open> rc_deep3 = \<lbrakk> cf1(cf1(cf1(\<llangle>1 :: 64 word\<rrangle>))) \<rbrakk> \<close> unfolding rc_deep3_def by (rule refl)

urust_expr rc_two_call_args \<open> cf2(cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>), cf1(\<llangle>3 :: 64 word\<rrangle>)) \<close>
lemma \<open> rc_two_call_args = \<lbrakk> cf2(cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>), cf1(\<llangle>3 :: 64 word\<rrangle>)) \<rbrakk> \<close> unfolding rc_two_call_args_def by (rule refl)

subsection\<open> Binder capture inside call / method arguments \<close>

urust_expr rc_cap_args \<open> let a = \<llangle>10 :: 64 word\<rrangle>; let b = \<llangle>20 :: 64 word\<rrangle>; cf2(\<llangle>a\<rrangle>, \<llangle>b\<rrangle>) \<close>
lemma \<open> rc_cap_args = \<lbrakk> let a = \<llangle>10 :: 64 word\<rrangle>; let b = \<llangle>20 :: 64 word\<rrangle>; cf2(\<llangle>a\<rrangle>, \<llangle>b\<rrangle>) \<rbrakk> \<close> unfolding rc_cap_args_def by (rule refl)

urust_expr rc_mcall_let_recv \<open> let x = \<llangle>5 :: 64 word\<rrangle>; x.cf1() \<close>
lemma \<open> rc_mcall_let_recv = \<lbrakk> let x = \<llangle>5 :: 64 word\<rrangle>; x.cf1() \<rbrakk> \<close> unfolding rc_mcall_let_recv_def by (rule refl)

subsection\<open> Method calls x nesting / precedence \<close>

urust_expr rc_mchain2 \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>).cf1() \<close>
lemma \<open> rc_mchain2 = \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>).cf1() \<rbrakk> \<close> unfolding rc_mchain2_def by (rule refl)

urust_expr rc_m_on_call \<open> cf1(\<llangle>1 :: 64 word\<rrangle>).cf2(\<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> rc_m_on_call = \<lbrakk> cf1(\<llangle>1 :: 64 word\<rrangle>).cf2(\<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding rc_m_on_call_def by (rule refl)

urust_expr rc_m_call_arg \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(cf1(\<llangle>2 :: 64 word\<rrangle>)) \<close>
lemma \<open> rc_m_call_arg = \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf2(cf1(\<llangle>2 :: 64 word\<rrangle>)) \<rbrakk> \<close> unfolding rc_m_call_arg_def by (rule refl)

urust_expr rc_m_prec \<open> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> * \<llangle>3 :: 64 word\<rrangle> \<close>
lemma \<open> rc_m_prec = \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> * \<llangle>3 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding rc_m_prec_def by (rule refl)


section\<open> Match \<open>match_switch\<close> (Corpus "Match Expressions" -- numeric/wildcard, first-order) \<close>

text\<open> \<open>match_switch scrut { k ⇒ e, …, _ ⇒ e }\<close> -> \<open>bind \<lbrakk>scrut\<rbrakk> (ncase_selector [(Some k, \<lbrakk>e\<rbrakk>), …,
(None, \<lbrakk>e\<rbrakk>)])\<close> (D26; SE:829-830, Core_Syntax.thy:655-685, Num_Case_Expression.thy). A numeral key ->
\<open>Some\<close>, \<open>_\<close> -> \<open>None\<close>; an or-pattern's alternatives each get their own pair with the same body. NO binders
(first-order). \<open>match_switch\<close> is a with-block form (joins \<open>uval\<close>, not a bare operand). Scope: the
\<open>match_switch\<close> keyword only + numeral/`_`/or-patterns; the bare \<open>match\<close> keyword (switch-vs-case
disambiguation), const-id/path keys, and \<open>match_case\<close> binding patterns are the next increment. \<close>

urust_expr msw_lit \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> msw_lit = \<lbrakk> match_switch \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding msw_lit_def by (rule refl)

context fixes n :: nat
begin

text\<open> Multiple numeral arms + wildcard fall-through (context-fixed scrutinee). \<close>
urust_expr msw_multi \<open> match_switch n { 0 \<Rightarrow> \<llangle>False\<rrangle>, 1 \<Rightarrow> \<llangle>True\<rrangle>, 2 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<close>
lemma \<open> msw_multi = \<lbrakk> match_switch n { 0 \<Rightarrow> \<llangle>False\<rrangle>, 1 \<Rightarrow> \<llangle>True\<rrangle>, 2 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<rbrakk> \<close>
  unfolding msw_multi_def by (rule refl)

text\<open> Or-pattern: \<open>1 | 2 | 3\<close> expands to three \<open>(Some _, body)\<close> pairs sharing the arm body. \<close>
urust_expr msw_or \<open> match_switch n { 1 | 2 | 3 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> msw_or = \<lbrakk> match_switch n { 1 | 2 | 3 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding msw_or_def by (rule refl)

text\<open> As a value (let-RHS) and as a `;`-terminated statement. (Unlike `{}`/`if`, the `match_switch`
keyword has NO no-`;` sequencing in the frontend, so a match_switch statement needs the `;`.) \<close>
urust_expr msw_let \<open> let r = match_switch n { 0 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }; r \<close>
lemma \<open> msw_let = \<lbrakk> let r = match_switch n { 0 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }; r \<rbrakk> \<close>
  unfolding msw_let_def by (rule refl)

urust_expr msw_stmt \<open> match_switch n { 0 \<Rightarrow> () , _ \<Rightarrow> () } ; () \<close>
lemma \<open> msw_stmt = \<lbrakk> match_switch n { 0 \<Rightarrow> () , _ \<Rightarrow> () } ; () \<rbrakk> \<close>
  unfolding msw_stmt_def by (rule refl)
end


section\<open> Known parser divergences (old frontend vs new parser) -- recorded, not proven \<close>

text\<open> Per \<open>urust-rules-and-conventions.md\<close> (C2): a divergence between the inner-syntax frontend and the
new parser is NEVER silently dropped -- it is kept here as a test case. Where a well-typed
\<open>NAME = \<lbrakk> src \<rbrakk>\<close> goal can be stated it is a \<open>sorry\<close>'d lemma; where it CANNOT (the frontend rejects
\<open>src\<close> so \<open>\<lbrakk> src \<rbrakk>\<close> does not parse / the parser rejects \<open>src\<close> so the command errors / the two terms have
incompatible types) the case is recorded via whichever of \<open>urust_expr\<close> (parser accepts) or a golden
\<open>undefined = \<lbrakk> src \<rbrakk>\<close> stub (frontend accepts) builds, plus a comment. Canonical tracker:
\<open>notes/claude/urust-old-new-divergences.md\<close>. \<close>

subsection\<open> D-1 (RESOLVED 2026-08-25): \<open>if\<close> as a binary-operator operand -- both now reject \<close>

text\<open> WAS a divergence: \<open>if \<llangle>True\<rrangle> { \<llangle>1::32 word\<rrangle> } else { \<llangle>2::32 word\<rrangle> } + \<llangle>3::32 word\<rrangle>\<close> --
the frontend REJECTS it (its \<open>if\<close> result-priority 21 < the \<open>+\<close> operand floor 49) but our flat parser
accepted it as \<open>(if...)+3\<close>. FIXED by the control-flow stratification (D25): \<open>if\<close> (a with-block form,
nonterminal \<open>uif\<close>) is no longer a bare operand (\<open>uexp\<close>), so the parser now ALSO rejects the unparenthesized
form with a parse error -- matching the frontend. This rejection is checked OUT-OF-BAND (a parse error, not
a refl row, like the \<open>a == b == c\<close> non-associativity case): running \<open>urust_expr\<close> on
\<open>if \<llangle>True\<rrangle> {\<llangle>1::32 word\<rrangle>} else {\<llangle>2::32 word\<rrangle>} + \<llangle>3::32 word\<rrangle>\<close> errors. Parenthesising
restores it (a paren-wrapped \<open>uval\<close> is a \<open>uexp\<close> operand), and that IS a passing row: \<close>
urust_expr d1_paren_operand
  \<open> (if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> }) + \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> d1_paren_operand = \<lbrakk> (if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> }) + \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding d1_paren_operand_def by (rule refl)

subsection\<open> D-2 (RESOLVED 2026-08-25): no-\<open>;\<close> sequencing of block-like expressions -- now accepted \<close>

text\<open> WAS a divergence: the frontend accepts a block-like expr in STATEMENT position without a trailing
\<open>;\<close> (Rust's optional semicolon; frontend \<open>_urust_sequence_scoping\<close> / \<open>_urust_sequence_if_*\<close>) but our
parser required the \<open>;\<close>. FIXED by the stratification (D25): \<open>ustmt\<close> gained no-\<open>;\<close> productions
\<open>ublock ustmt\<close> / \<open>uif ustmt\<close> that desugar to the same \<open>sequence\<close> an explicit \<open>;\<close> would. Now passing
rows: block-then-block, if-then-then-stmt, if-else-then-stmt (each = \<open>sequence \<lbrakk>block-like\<rbrakk> \<lbrakk>next\<rbrakk>\<close>). \<close>
urust_expr d2_blk_seq \<open> { () } { () } \<close>
lemma \<open> d2_blk_seq = \<lbrakk> { () } { () } \<rbrakk> \<close> unfolding d2_blk_seq_def by (rule refl)

urust_expr d2_if_seq \<open> if \<llangle>True\<rrangle> { () } () \<close>
lemma \<open> d2_if_seq = \<lbrakk> if \<llangle>True\<rrangle> { () } () \<rbrakk> \<close> unfolding d2_if_seq_def by (rule refl)

urust_expr d2_ifelse_seq \<open> if \<llangle>True\<rrangle> { () } else { () } () \<close>
lemma \<open> d2_ifelse_seq = \<lbrakk> if \<llangle>True\<rrangle> { () } else { () } () \<rbrakk> \<close> unfolding d2_ifelse_seq_def by (rule refl)

subsection\<open> D-3 (RESOLVED 2026-08-24): a HOL-const-named binder IS captured in an antiquotation \<close>

text\<open> WAS a divergence: \<open>let id = \<llangle>5::nat\<rrangle>; \<llangle>id\<rrangle>\<close> (binder \<open>id\<close> = HOL \<open>Fun.id\<close>) elaborated to
\<open>bind (\<up>5) (\<lambda>id. \<up>Fun.id)\<close> -- \<open>id\<close> resolved to the CONSTANT, NOT captured. FIXED:
\<open>Parser_Utils.parse_antiq\<close> now \<open>Variable.add_fixes_direct\<close>es the enclosing binder names before
\<open>Syntax.parse_term\<close>, so a binder shadows a same-named HOL constant. The intended equalities now close by
\<open>refl\<close>. Only genuine HOL-CONSTANT binder names were affected: a registered \<open>micro_rust_notation\<close> SURFACE
name (e.g. \<open>myReg\<close>) is not a HOL const, so \<open>Syntax.parse_term\<close> already freed it -- \<open>cap_notation\<close> guards
this. See \<open>urust-old-new-divergences.md\<close> (D-3). \<close>
urust_expr div_binder_const \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id\<rrangle> \<close>
lemma \<open> div_binder_const = \<lbrakk> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id\<rrangle> \<rbrakk> \<close> unfolding div_binder_const_def by (rule refl)

urust_expr cap_const_fst \<open> let fst = \<llangle>5 :: nat\<rrangle>; \<llangle>fst\<rrangle> \<close>  \<comment>\<open> binder name = HOL \<open>Product_Type.fst\<close> \<close>
lemma \<open> cap_const_fst = \<lbrakk> let fst = \<llangle>5 :: nat\<rrangle>; \<llangle>fst\<rrangle> \<rbrakk> \<close> unfolding cap_const_fst_def by (rule refl)

urust_expr cap_const_deep \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id + 1\<rrangle> \<close>  \<comment>\<open> buried capture of a const-named binder \<close>
lemma \<open> cap_const_deep = \<lbrakk> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id + 1\<rrangle> \<rbrakk> \<close> unfolding cap_const_deep_def by (rule refl)

urust_expr cap_notation \<open> let myReg = \<llangle>5 :: nat\<rrangle>; \<llangle>myReg\<rrangle> \<close>  \<comment>\<open> binder name = a registered notation surface name (guard) \<close>
lemma \<open> cap_notation = \<lbrakk> let myReg = \<llangle>5 :: nat\<rrangle>; \<llangle>myReg\<rrangle> \<rbrakk> \<close> unfolding cap_notation_def by (rule refl)

subsection\<open> D-4: antiquotation start-states do not balance nested delimiters (LATENT) \<close>

text\<open> A \<open>\<epsilon>\<open> ... \<close>\<close> body containing an inner cartouche (or a \<open>\<llangle>...\<rrangle>\<close> body containing a nested
\<open>\<llangle>\<close>/\<open>\<rrangle>\<close>) closes on the FIRST closer and silently mis-parses the tail. No current row triggers it
(real HOL bodies here contain no nested cartouche), so it is recorded as a note; a runnable trigger + the
depth-counting fix belong with the nested-antiquotation tier. \<close>

subsection\<open> D-5: non-identifier / non-method call callees -- parser UNDER-accepts (frontend accepts) \<close>

text\<open> The call grammar accepts identifier callees \<open>f(args)\<close> AND method calls \<open>recv.m(args)\<close>. Of the
frontend's remaining \<open>urust_callable\<close> forms (Micro_Rust_Syntax.thy:221-258) the following are still
deferred: antiquotation callee \<open>\<epsilon>\<open>g\<close>(a)\<close>, function antiquotation \<open>\<llangle>f\<rrangle>\<^sub>N(a)\<close> (deferred by
decision -- an off-critical-path antiquotation form), turbofish \<open>f::\<open>N\<close>(a)\<close>, and macros \<open>m!(...)\<close>.
(\<open>f(a)(b)\<close> / \<open>(g)(x)\<close> are rejected by BOTH -- not divergences.) The directly expressible
antiquotation-callee form is kept as a \<open>sorry\<close>'d golden stub; the rest are notes (turbofish/paths need
\<open>::\<close>, macros need \<open>!\<close> -- unlexable). Canonical tracker: \<open>urust-old-new-divergences.md\<close> (D-5). \<close>
lemma \<open> undefined = \<lbrakk> \<epsilon>\<open>cf1\<close>(\<llangle>1 :: 64 word\<rrangle>) \<rbrakk> \<close> sorry
  \<comment> \<open>frontend: \<open>funcall1 cf1 (\<up>1)\<close>; parser rejects (callee must be an identifier or a method call).\<close>

subsection\<open> D-6: field access \<open>x.f\<close> (no parens) -- parser UNDER-accepts (frontend accepts) \<close>

text\<open> Distinct from the method call \<open>x.f()\<close>: the parser's \<open>.\<close> is only followed by a method call
(\<open>TDOT IDENT LPAR ...\<close>), so a bare \<open>x.f\<close> is a parse error. The frontend lowers it to a lens focus
(NField dispatch -> \<open>bindlift1 (focus_lens_const f) \<up>x\<close>, Core_Syntax.thy:439-440), NOT a funcall.
Deferred to the optics/lens tier; recorded as a note (a runnable golden needs a registered field notation
/ concrete lens types). \<close>

end
