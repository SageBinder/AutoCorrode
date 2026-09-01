(* Positive conformance against the inner-syntax frontend. Each `urust_expr` definition is unfolded and
   proved alpha-equal to `\<lbrakk> src \<rbrakk>` by `refl`. Type annotations avoid hidden type variables
   that `Local_Theory.define` cannot expose cleanly. *)

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

urust_expr lit_hex \<open> 0xff \<close>
lemma \<open> lit_hex = \<lbrakk> 0xff \<rbrakk> \<close> unfolding lit_hex_def by (rule refl)


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


section\<open> Boolean and string literals \<close>

urust_expr lit_bool_true \<open> true \<close>
lemma \<open> lit_bool_true = \<lbrakk> true \<rbrakk> \<close> unfolding lit_bool_true_def by (rule refl)

urust_expr lit_bool_false \<open> false \<close>
lemma \<open> lit_bool_false = \<lbrakk> false \<rbrakk> \<close> unfolding lit_bool_false_def by (rule refl)

urust_expr lit_string_empty \<open> "" \<close>
lemma \<open> lit_string_empty = \<lbrakk> "" \<rbrakk> \<close> unfolding lit_string_empty_def by (rule refl)

urust_expr lit_string_text \<open> "micro rust" \<close>
lemma \<open> lit_string_text = \<lbrakk> "micro rust" \<rbrakk> \<close> unfolding lit_string_text_def by (rule refl)

urust_expr lit_string_quote \<open> "say: \"hi\"" \<close>
lemma \<open> lit_string_quote = \<lbrakk> "say: \"hi\"" \<rbrakk> \<close>
  unfolding lit_string_quote_def by (rule refl)

urust_expr lit_string_backslash \<open> "a\\b" \<close>
lemma \<open> lit_string_backslash = \<lbrakk> "a\\b" \<rbrakk> \<close>
  unfolding lit_string_backslash_def by (rule refl)


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

urust_expr aq_nested_value
  \<open> \<llangle> \<lbrakk> \<llangle>1 :: nat\<rrangle> \<rbrakk> \<rrangle> \<close>
lemma \<open> aq_nested_value =
    \<lbrakk> \<llangle> \<lbrakk> \<llangle>1 :: nat\<rrangle> \<rbrakk> \<rrangle> \<rbrakk> \<close>
  unfolding aq_nested_value_def by (rule refl)

urust_expr aq_nested_expr
  \<open> \<epsilon>\<open> \<lbrakk> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<rbrakk> \<close> \<close>
lemma \<open> aq_nested_expr =
    \<lbrakk> \<epsilon>\<open> \<lbrakk> \<epsilon>\<open>\<up>(1 :: nat)\<close> \<rbrakk> \<close> \<rbrakk> \<close>
  unfolding aq_nested_expr_def by (rule refl)


section\<open> Bare identifiers at value position (dispatch reuse) \<close>

text\<open>
For unregistered HOL constants, \<open>check_term\<close> promotes the parser's bare
\<open>Free\<close> to the same \<open>Const\<close> as the frontend fallback.
\<close>

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

text\<open>
Registered names use the existing \<open>urust_dispatch\<close> term-check phase.
\<close>
definition my_backend :: nat where \<open> my_backend \<equiv> 7 \<close>
micro_rust_notation (literal) my_backend ("myReg")

urust_expr lit_reg \<open> myReg \<close>
lemma \<open> lit_reg = \<lbrakk> myReg \<rbrakk> \<close> unfolding lit_reg_def by (rule refl)


section\<open> Sequencing, `let` and `const` bindings \<close>

text\<open>
\<open>e1; e2\<close> lowers to \<open>sequence e1 e2\<close>; a trailing semicolon
sequences with \<open>skip = literal ()\<close>.
\<close>

urust_expr seq_unit \<open> (); () \<close>
lemma \<open> seq_unit = \<lbrakk> (); () \<rbrakk> \<close> unfolding seq_unit_def by (rule refl)

urust_expr seq_trailing \<open> (); (); \<close>
lemma \<open> seq_trailing = \<lbrakk> (); (); \<rbrakk> \<close> unfolding seq_trailing_def by (rule refl)

text\<open>
\<open>let x = e; k\<close> lowers to HOAS \<open>bind e (\<lambda>x. k)\<close>.
Unused binders need a type pin (R1).
\<close>

urust_expr let_use \<open> let x = 5; x \<close>
lemma \<open> let_use = \<lbrakk> let x = 5; x \<rbrakk> \<close> unfolding let_use_def by (rule refl)

urust_expr let_ab \<open> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<close>
lemma \<open> let_ab = \<lbrakk> let a = \<llangle>1 :: nat\<rrangle>; let b = \<llangle>2 :: nat\<rrangle>; a \<rbrakk> \<close> unfolding let_ab_def by (rule refl)

text\<open> \<open>const x = e; k\<close> desugars byte-for-byte as \<open>let\<close> (Corpus PART I "Const Bindings"). \<close>

urust_expr const_foo \<open> const FOO = \<llangle>5 :: nat\<rrangle>; () \<close>
lemma \<open> const_foo = \<lbrakk> const FOO = \<llangle>5 :: nat\<rrangle>; () \<rbrakk> \<close> unfolding const_foo_def by (rule refl)

text\<open>
An enclosing \<open>let\<close> captures \<open>x\<close> inside both direct and nested
antiquotations.
\<close>

urust_expr let_cap \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<close>
lemma \<open> let_cap = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x\<rrangle> \<rbrakk> \<close> unfolding let_cap_def by (rule refl)

urust_expr let_cap_deep \<open> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<close>
lemma \<open> let_cap_deep = \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<llangle>x + 1\<rrangle> \<rbrakk> \<close> unfolding let_cap_deep_def by (rule refl)

text\<open>
In the shared pattern grammar, \<open>let _\<close> creates an anonymous hygienic lambda,
not a variable named \<open>_\<close>.
\<close>

urust_expr let_wild \<open> let _ = \<llangle>5 :: nat\<rrangle>; () \<close>
lemma \<open> let_wild = \<lbrakk> let _ = \<llangle>5 :: nat\<rrangle>; () \<rbrakk> \<close> unfolding let_wild_def by (rule refl)

text\<open> Its \<open>Abs\<close>/\<open>Bound\<close> representation cannot capture an outer binder. \<close>
urust_expr let_wild_hyg \<open> let uu = \<llangle>5 :: nat\<rrangle>; let _ = \<llangle>7 :: nat\<rrangle>; uu \<close>
lemma \<open> let_wild_hyg = \<lbrakk> let uu = \<llangle>5 :: nat\<rrangle>; let _ = \<llangle>7 :: nat\<rrangle>; uu \<rbrakk> \<close>
  unfolding let_wild_hyg_def by (rule refl)

text\<open> Refutable \<open>let\<close> patterns and patterns unsupported by a selected match lowering have positioned
rows in \<open>Micro_Rust_Parser_Negative_Conformance.thy\<close>. \<close>

section\<open> Tuple values and irrefutable tuple binders \<close>

text\<open>
Tuple values lower to the frontend's right-nested product ending in \<open>TNil\<close>.
Tuple binders recursively admit names, wildcards, and nested tuples.
\<close>

urust_expr tuple_value_two
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>) \<close>
lemma \<open> tuple_value_two =
    \<lbrakk> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>) \<rbrakk> \<close>
  unfolding tuple_value_two_def by (rule refl)

urust_expr tuple_value_four
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>False\<rrangle>) \<close>
lemma \<open> tuple_value_four =
    \<lbrakk> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>False\<rrangle>) \<rbrakk> \<close>
  unfolding tuple_value_four_def by (rule refl)

urust_expr tuple_value_nested
  \<open> ((\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>), \<llangle>False\<rrangle>) \<close>
lemma \<open> tuple_value_nested =
    \<lbrakk> ((\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>), \<llangle>False\<rrangle>) \<rbrakk> \<close>
  unfolding tuple_value_nested_def by (rule refl)

urust_expr tuple_let_two
  \<open> let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>); x \<close>
lemma \<open> tuple_let_two =
    \<lbrakk> let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>); x \<rbrakk> \<close>
  unfolding tuple_let_two_def by (rule refl)

urust_expr tuple_let_three
  \<open> let (x, y, z) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); z \<close>
lemma \<open> tuple_let_three =
    \<lbrakk> let (x, y, z) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); z \<rbrakk> \<close>
  unfolding tuple_let_three_def by (rule refl)

urust_expr tuple_const_three
  \<open> const (x, y, z) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<close>
lemma \<open> tuple_const_three =
    \<lbrakk> const (x, y, z) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<rbrakk> \<close>
  unfolding tuple_const_three_def by (rule refl)

urust_expr tuple_let_nested
  \<open> let (x, (y, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>)); y \<close>
lemma \<open> tuple_let_nested =
    \<lbrakk> let (x, (y, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>)); y \<rbrakk> \<close>
  unfolding tuple_let_nested_def by (rule refl)

urust_expr tuple_const_nested
  \<open> const (x, (_, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>True\<rrangle>, \<llangle>3 :: nat\<rrangle>)); z \<close>
lemma \<open> tuple_const_nested =
    \<lbrakk> const (x, (_, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>True\<rrangle>, \<llangle>3 :: nat\<rrangle>)); z \<rbrakk> \<close>
  unfolding tuple_const_nested_def by (rule refl)

urust_expr tuple_let_wildcards
  \<open> let (_, y, _) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); y \<close>
lemma \<open> tuple_let_wildcards =
    \<lbrakk> let (_, y, _) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>, \<llangle>2 :: nat\<rrangle>); y \<rbrakk> \<close>
  unfolding tuple_let_wildcards_def by (rule refl)

urust_expr tuple_let_shadow
  \<open> let x = \<llangle>0 :: nat\<rrangle>; let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<close>
lemma \<open> tuple_let_shadow =
    \<lbrakk> let x = \<llangle>0 :: nat\<rrangle>; let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<rbrakk> \<close>
  unfolding tuple_let_shadow_def by (rule refl)

urust_expr tuple_let_antiquotation
  \<open> let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); \<llangle>x + y\<rrangle> \<close>
lemma \<open> tuple_let_antiquotation =
    \<lbrakk> let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); \<llangle>x + y\<rrangle> \<rbrakk> \<close>
  unfolding tuple_let_antiquotation_def by (rule refl)


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

urust_expr mut_scalar
  \<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; x \<close>
lemma \<open> mut_scalar = \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; x \<rbrakk> \<close>
  unfolding mut_scalar_def by (rule refl)

urust_expr mut_capture
  \<open> let mut x = \<llangle>0 :: 32 word\<rrangle>; \<llangle>x\<rrangle> \<close>
lemma \<open> mut_capture =
    \<lbrakk> let mut x = \<llangle>0 :: 32 word\<rrangle>; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding mut_capture_def by (rule refl)

urust_expr mut_shadow
  \<open> let x = \<llangle>1 :: 32 word\<rrangle>; let mut x = \<llangle>2 :: 32 word\<rrangle>; x \<close>
lemma \<open> mut_shadow =
    \<lbrakk> let x = \<llangle>1 :: 32 word\<rrangle>; let mut x = \<llangle>2 :: 32 word\<rrangle>; x \<rbrakk> \<close>
  unfolding mut_shadow_def by (rule refl)

urust_expr mut_tuple
  \<open> let mut (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<close>
lemma \<open> mut_tuple =
    \<lbrakk> let mut (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); x \<rbrakk> \<close>
  unfolding mut_tuple_def by (rule refl)

urust_expr mut_tuple_nested
  \<open> let mut (x, (_, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>True\<rrangle>, \<llangle>3 :: nat\<rrangle>)); z \<close>
lemma \<open> mut_tuple_nested =
    \<lbrakk> let mut (x, (_, z)) = (\<llangle>1 :: nat\<rrangle>, (\<llangle>True\<rrangle>, \<llangle>3 :: nat\<rrangle>)); z \<rbrakk> \<close>
  unfolding mut_tuple_nested_def by (rule refl)

urust_expr mut_borrow_chain
  \<open>
    let mut x = \<llangle>0 :: 32 word\<rrangle>;
    let xr = &x;
    let xw = & mut x;
    xw
  \<close>
lemma \<open> mut_borrow_chain =
    \<lbrakk>
      let mut x = \<llangle>0 :: 32 word\<rrangle>;
      let xr = &x;
      let xw = & mut x;
      xw
    \<rbrakk> \<close>
  unfolding mut_borrow_chain_def by (rule refl)

subsection\<open> Borrow, dereference, and precedence \<close>

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rr :: \<open>(unit, unit, (unit, unit, 32 word) Global_Store.ref) Global_Store.ref\<close>
    and rb :: \<open>(unit, unit, bool) Global_Store.ref\<close>
    and ropt :: \<open>(unit, unit, 32 word) Global_Store.ref option\<close>
    and rhs :: \<open>32 word\<close>
begin

urust_expr ref_borrow \<open> &r \<close>
lemma \<open> ref_borrow = \<lbrakk> &r \<rbrakk> \<close>
  unfolding ref_borrow_def by (rule refl)

urust_expr ref_borrow_mut \<open> & mut r \<close>
lemma \<open> ref_borrow_mut = \<lbrakk> & mut r \<rbrakk> \<close>
  unfolding ref_borrow_mut_def by (rule refl)

urust_expr ref_borrow_group \<open> &(r) \<close>
lemma \<open> ref_borrow_group = \<lbrakk> &(r) \<rbrakk> \<close>
  unfolding ref_borrow_group_def by (rule refl)

urust_expr ref_borrow_block \<open> &{ r } \<close>
lemma \<open> ref_borrow_block = \<lbrakk> &{ r } \<rbrakk> \<close>
  unfolding ref_borrow_block_def by (rule refl)

urust_expr ref_borrow_if \<open> &(if true { r } else { r }) \<close>
lemma \<open> ref_borrow_if = \<lbrakk> &(if true { r } else { r }) \<rbrakk> \<close>
  unfolding ref_borrow_if_def by (rule refl)

urust_expr ref_deref \<open> *r \<close>
lemma \<open> ref_deref = \<lbrakk> *r \<rbrakk> \<close>
  unfolding ref_deref_def by (rule refl)

urust_expr ref_double_deref \<open> **rr \<close>
lemma \<open> ref_double_deref = \<lbrakk> **rr \<rbrakk> \<close>
  unfolding ref_double_deref_def by (rule refl)

urust_expr ref_deref_group \<open> *(r) \<close>
lemma \<open> ref_deref_group = \<lbrakk> *(r) \<rbrakk> \<close>
  unfolding ref_deref_group_def by (rule refl)

urust_expr ref_deref_block \<open> *{ r } \<close>
lemma \<open> ref_deref_block = \<lbrakk> *{ r } \<rbrakk> \<close>
  unfolding ref_deref_block_def by (rule refl)

urust_expr ref_deref_if \<open> *(if true { r } else { r }) \<close>
lemma \<open> ref_deref_if = \<lbrakk> *(if true { r } else { r }) \<rbrakk> \<close>
  unfolding ref_deref_if_def by (rule refl)

urust_expr ref_deref_postfix \<open> *ropt? \<close>
lemma \<open> ref_deref_postfix = \<lbrakk> *ropt? \<rbrakk> \<close>
  unfolding ref_deref_postfix_def by (rule refl)

urust_expr ref_deref_add \<open> *r + rhs \<close>
lemma \<open> ref_deref_add = \<lbrakk> *r + rhs \<rbrakk> \<close>
  unfolding ref_deref_add_def by (rule refl)

urust_expr ref_deref_mul \<open> *r * rhs \<close>
lemma \<open> ref_deref_mul = \<lbrakk> *r * rhs \<rbrakk> \<close>
  unfolding ref_deref_mul_def by (rule refl)

urust_expr ref_deref_mul2 \<open> rhs * *r \<close>
lemma \<open> ref_deref_mul2 = \<lbrakk> rhs * *r \<rbrakk> \<close>
  unfolding ref_deref_mul2_def by (rule refl)

urust_expr ref_deref_band \<open> *r & rhs \<close>
lemma \<open> ref_deref_band = \<lbrakk> *r & rhs \<rbrakk> \<close>
  unfolding ref_deref_band_def by (rule refl)

urust_expr ref_not_grouped_deref \<open> !(*rb) \<close>
lemma \<open> ref_not_grouped_deref = \<lbrakk> !(*rb) \<rbrakk> \<close>
  unfolding ref_not_grouped_deref_def by (rule refl)

urust_expr ref_match_scrutinee
  \<open> match_switch *r { 0 \<Rightarrow> true, _ \<Rightarrow> false } \<close>
lemma \<open> ref_match_scrutinee =
    \<lbrakk> match_switch *r { 0 \<Rightarrow> true, _ \<Rightarrow> false } \<rbrakk> \<close>
  unfolding ref_match_scrutinee_def by (rule refl)

end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open> Pure-value operators (Corpus PART I: Arithmetic / Bitwise / Comparison / Boolean) \<close>

text\<open>
Binary operators lower to the frontend constants; value antiquotations pin word types.
\<close>

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

subsection\<open> Precedence and associativity \<close>

text\<open>
Rows cover every adjacent frontend precedence tier, from \<open>||\<close> (42) through
\<open>* / %\<close> (50); prefix \<open>!\<close> is tightest. The negative harness covers
non-associative comparisons.
\<close>

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

text\<open>
Because frontend \<open>_urust_scoping\<close> is the identity (SE:360-362), blocks
erase without a \<open>scoped\<close> wrapper. Their statements sequence with semicolons,
and blocks may be operator operands.
\<close>

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

text\<open>
Two-armed \<open>if\<close> lowers to \<open>two_armed_conditional\<close>. A missing else becomes
\<open>skip\<close>, so the then-branch must be unit-typed. Else-if nests another
\<open>if\<close> (SE:364-365; SYN:661-662).
\<close>

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

text\<open>
Rows cover compound conditions, nested branches, deep blocks, let RHSs, and sequencing.
\<close>

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

context
  fixes cf14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin
urust_expr call14 \<open> cf14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<close>
lemma \<open> call14 = \<lbrakk> cf14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<rbrakk> \<close>
  unfolding call14_def by (rule refl)
end

text\<open> Nested call \<open>f(g(c), b)\<close>: the inner call is an ordinary argument expression. \<close>
urust_expr call_nested \<open> cf2(cf1(\<llangle>1 :: 64 word\<rrangle>), \<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> call_nested = \<lbrakk> cf2(cf1(\<llangle>1 :: 64 word\<rrangle>), \<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_nested_def by (rule refl)

text\<open>
Registered callees use NFunction dispatch. Rows cover a local notation and the
\<open>Some\<close>, \<open>Ok\<close>, and \<open>Err\<close> call notations.
\<close>
micro_rust_notation (call) cf1 ("regCall")
urust_expr call_reg \<open> regCall(\<llangle>3 :: 64 word\<rrangle>) \<close>
lemma \<open> call_reg = \<lbrakk> regCall(\<llangle>3 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_reg_def by (rule refl)

urust_expr call_some \<open> Some(\<llangle>42 :: nat\<rrangle>) \<close>
lemma \<open> call_some = \<lbrakk> Some(\<llangle>42 :: nat\<rrangle>) \<rbrakk> \<close> unfolding call_some_def by (rule refl)

urust_expr call_ok \<open> Ok(\<llangle>42 :: nat\<rrangle>) \<close>
lemma \<open> call_ok = \<lbrakk> Ok(\<llangle>42 :: nat\<rrangle>) \<rbrakk> \<close> unfolding call_ok_def by (rule refl)

urust_expr call_err \<open> Err(\<llangle>42 :: nat\<rrangle>) \<close>
lemma \<open> call_err = \<lbrakk> Err(\<llangle>42 :: nat\<rrangle>) \<rbrakk> \<close> unfolding call_err_def by (rule refl)

text\<open>
A let-bound callee uses lexical scope without dispatch or a \<open>literal\<close> wrapper.
\<close>
urust_expr call_letbound \<open> let h = \<llangle>cf1\<rrangle>; h(\<llangle>4 :: 64 word\<rrangle>) \<close>
lemma \<open> call_letbound = \<lbrakk> let h = \<llangle>cf1\<rrangle>; h(\<llangle>4 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding call_letbound_def by (rule refl)

text\<open>
Context-fixed, function-typed callees remain \<open>Free\<close>. Rows cover word, unit,
and boolean arguments.
\<close>
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

text\<open>
Method syntax prepends the receiver to a plain NFunction call (SE:380-381,
416-417). It binds tighter than operators. Bare field access uses the composable
NField/lens postfix added below (D37).
\<close>

urust_expr mcall0 \<open> \<llangle>5 :: 64 word\<rrangle>.cf1() \<close>
lemma \<open> mcall0 = \<lbrakk> \<llangle>5 :: 64 word\<rrangle>.cf1() \<rbrakk> \<close> unfolding mcall0_def by (rule refl)

urust_expr mcall1 \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>) \<close>
lemma \<open> mcall1 = \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close> unfolding mcall1_def by (rule refl)

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
urust_expr mcall13 \<open> receiver.m14(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<close>
lemma \<open> mcall13 = \<lbrakk> receiver.m14(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13) \<rbrakk> \<close>
  unfolding mcall13_def by (rule refl)
end

text\<open> Rows cover call-result receivers, method chains, and operator precedence. \<close>
urust_expr mcall_on_call \<open> cf1(\<llangle>1 :: 64 word\<rrangle>).cf1() \<close>
lemma \<open> mcall_on_call = \<lbrakk> cf1(\<llangle>1 :: 64 word\<rrangle>).cf1() \<rbrakk> \<close> unfolding mcall_on_call_def by (rule refl)

urust_expr mcall_chain \<open> \<llangle>5 :: 64 word\<rrangle>.cf1().cf1() \<close>
lemma \<open> mcall_chain = \<lbrakk> \<llangle>5 :: 64 word\<rrangle>.cf1().cf1() \<rbrakk> \<close> unfolding mcall_chain_def by (rule refl)

urust_expr mcall_operand \<open> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> \<close>
lemma \<open> mcall_operand = \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf1() + \<llangle>2 :: 64 word\<rrangle> \<rbrakk> \<close> unfolding mcall_operand_def by (rule refl)

text\<open> Context-fixed methods are tested alone and in an equality condition. \<close>
context fixes m n :: \<open>nat\<close> and h :: \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
begin
urust_expr mcall_ctx \<open> m.h() \<close>
lemma \<open> mcall_ctx = \<lbrakk> m.h() \<rbrakk> \<close> unfolding mcall_ctx_def by (rule refl)

urust_expr mcall_if \<open> if m.h() == n { m } else { n } \<close>
lemma \<open> mcall_if = \<lbrakk> if m.h() == n { m } else { n } \<rbrakk> \<close> unfolding mcall_if_def by (rule refl)
end


section\<open> Postfix propagation and field access \<close>

subsection\<open> Error propagation \<close>

context
  fixes opt :: \<open>nat option\<close>
  fixes res :: \<open>(nat, bool) result\<close>
begin
urust_expr postfix_option \<open> opt? \<close>
lemma \<open> postfix_option = \<lbrakk> opt? \<rbrakk> \<close>
  unfolding postfix_option_def by (rule refl)

urust_expr postfix_result \<open> res? \<close>
lemma \<open> postfix_result = \<lbrakk> res? \<rbrakk> \<close>
  unfolding postfix_result_def by (rule refl)

urust_expr postfix_block \<open> { opt }? \<close>
lemma \<open> postfix_block = \<lbrakk> { opt }? \<rbrakk> \<close>
  unfolding postfix_block_def by (rule refl)

urust_expr postfix_parenthesized_if \<open> (if true { opt } else { opt })? \<close>
lemma \<open> postfix_parenthesized_if = \<lbrakk> (if true { opt } else { opt })? \<rbrakk> \<close>
  unfolding postfix_parenthesized_if_def by (rule refl)
end

context
  fixes next_opt :: \<open>(unit, nat option, unit, unit, unit) function_body\<close>
  fixes nested_opt :: \<open>nat option option\<close>
begin
urust_expr postfix_after_call \<open> next_opt()? \<close>
lemma \<open> postfix_after_call = \<lbrakk> next_opt()? \<rbrakk> \<close>
  unfolding postfix_after_call_def by (rule refl)

urust_expr postfix_repeated \<open> nested_opt?? \<close>
lemma \<open> postfix_repeated = \<lbrakk> nested_opt?? \<rbrakk> \<close>
  unfolding postfix_repeated_def by (rule refl)
end

context
  fixes flag :: \<open>bool option\<close>
  fixes lhs :: \<open>64 word option\<close>
  fixes rhs :: \<open>64 word\<close>
begin
urust_expr postfix_unary_precedence \<open> !flag? \<close>
lemma \<open> postfix_unary_precedence = \<lbrakk> !flag? \<rbrakk> \<close>
  unfolding postfix_unary_precedence_def by (rule refl)

urust_expr postfix_binary_precedence \<open> lhs? + rhs \<close>
lemma \<open> postfix_binary_precedence = \<lbrakk> lhs? + rhs \<rbrakk> \<close>
  unfolding postfix_binary_precedence_def by (rule refl)
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
urust_expr postfix_field_default \<open> d.postfix_default_value \<close>
lemma \<open> postfix_field_default = \<lbrakk> d.postfix_default_value \<rbrakk> \<close>
  unfolding postfix_field_default_def by (rule refl)

urust_expr postfix_field_renamed \<open> i.value \<close>
lemma \<open> postfix_field_renamed = \<lbrakk> i.value \<rbrakk> \<close>
  unfolding postfix_field_renamed_def by (rule refl)

urust_expr postfix_field_nested \<open> self.inner.value \<close>
lemma \<open> postfix_field_nested = \<lbrakk> self.inner.value \<rbrakk> \<close>
  unfolding postfix_field_nested_def by (rule refl)

urust_expr postfix_field_then_propagate \<open> self.optional? \<close>
lemma \<open> postfix_field_then_propagate = \<lbrakk> self.optional? \<rbrakk> \<close>
  unfolding postfix_field_then_propagate_def by (rule refl)

urust_expr postfix_propagate_then_field \<open> self.optional?.secondary \<close>
lemma \<open> postfix_propagate_then_field = \<lbrakk> self.optional?.secondary \<rbrakk> \<close>
  unfolding postfix_propagate_then_field_def by (rule refl)

urust_expr postfix_field_disambiguation \<open> dual.pick \<close>
lemma \<open> postfix_field_disambiguation = \<lbrakk> dual.pick \<rbrakk> \<close>
  unfolding postfix_field_disambiguation_def by (rule refl)

urust_expr postfix_method_disambiguation \<open> dual.pick() \<close>
lemma \<open> postfix_method_disambiguation = \<lbrakk> dual.pick() \<rbrakk> \<close>
  unfolding postfix_method_disambiguation_def by (rule refl)
end

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context fixes rp :: \<open>(unit, unit, postfix_inner) Global_Store.ref\<close>
begin
urust_expr ref_deref_field_postfix \<open> *rp.value \<close>
lemma \<open> ref_deref_field_postfix = \<lbrakk> *rp.value \<rbrakk> \<close>
  unfolding ref_deref_field_postfix_def by (rule refl)
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

urust_expr assign_identifier \<open> r = rhs \<close>
lemma \<open> assign_identifier = \<lbrakk> r = rhs \<rbrakk> \<close>
  unfolding assign_identifier_def by (rule refl)

urust_expr assign_grouped \<open> (r) = rhs \<close>
lemma \<open> assign_grouped = \<lbrakk> (r) = rhs \<rbrakk> \<close>
  unfolding assign_grouped_def by (rule refl)

urust_expr assign_nested_groups \<open> (((r))) = rhs \<close>
lemma \<open> assign_nested_groups = \<lbrakk> (((r))) = rhs \<rbrakk> \<close>
  unfolding assign_nested_groups_def by (rule refl)

urust_expr assign_deref \<open> *r = rhs \<close>
lemma \<open> assign_deref = \<lbrakk> *r = rhs \<rbrakk> \<close>
  unfolding assign_deref_def by (rule refl)

urust_expr assign_grouped_deref \<open> (*r) = rhs \<close>
lemma \<open> assign_grouped_deref = \<lbrakk> (*r) = rhs \<rbrakk> \<close>
  unfolding assign_grouped_deref_def by (rule refl)

urust_expr assign_deref_group \<open> *(r) = rhs \<close>
lemma \<open> assign_deref_group = \<lbrakk> *(r) = rhs \<rbrakk> \<close>
  unfolding assign_deref_group_def by (rule refl)

urust_expr assign_rhs_operator \<open> r = rhs + other \<close>
lemma \<open> assign_rhs_operator = \<lbrakk> r = rhs + other \<rbrakk> \<close>
  unfolding assign_rhs_operator_def by (rule refl)

urust_expr assign_block_rhs \<open> r = { rhs } \<close>
lemma \<open> assign_block_rhs = \<lbrakk> r = { rhs } \<rbrakk> \<close>
  unfolding assign_block_rhs_def by (rule refl)

urust_expr assign_sequence \<open> r = rhs; *r \<close>
lemma \<open> assign_sequence = \<lbrakk> r = rhs; *r \<rbrakk> \<close>
  unfolding assign_sequence_def by (rule refl)

urust_expr assign_block \<open> { r = rhs; *r } \<close>
lemma \<open> assign_block = \<lbrakk> { r = rhs; *r } \<rbrakk> \<close>
  unfolding assign_block_def by (rule refl)

urust_expr assign_call_argument \<open> assignment_sink(r = rhs) \<close>
lemma \<open> assign_call_argument = \<lbrakk> assignment_sink(r = rhs) \<rbrakk> \<close>
  unfolding assign_call_argument_def by (rule refl)

urust_expr assign_lexical_shadow
  \<open> let assignmentPlace = \<llangle>r\<rrangle>; assignmentPlace = rhs \<close>
lemma \<open> assign_lexical_shadow =
    \<lbrakk> let assignmentPlace = \<llangle>r\<rrangle>; assignmentPlace = rhs \<rbrakk> \<close>
  unfolding assign_lexical_shadow_def by (rule refl)

end

urust_expr assign_notation_target \<open> assignmentPlace = \<llangle>7 :: 32 word\<rrangle> \<close>
lemma \<open> assign_notation_target =
    \<lbrakk> assignmentPlace = \<llangle>7 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding assign_notation_target_def by (rule refl)

subsection\<open> Associativity and composition \<close>

context
  fixes outer :: \<open>(unit, unit, unit) Global_Store.ref\<close>
    and inner :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rhs :: \<open>32 word\<close>
begin

urust_expr assign_right_associative \<open> outer = inner = rhs \<close>
lemma \<open> assign_right_associative = \<lbrakk> outer = inner = rhs \<rbrakk> \<close>
  unfolding assign_right_associative_def by (rule refl)

end

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and lhs rhs :: \<open>32 word\<close>
    and flag :: bool
begin

urust_expr assign_if_branches
  \<open> if flag { r = lhs } else { r = rhs } \<close>
lemma \<open> assign_if_branches =
    \<lbrakk> if flag { r = lhs } else { r = rhs } \<rbrakk> \<close>
  unfolding assign_if_branches_def by (rule refl)

urust_expr assign_match_arms
  \<open> match flag { true \<Rightarrow> r = lhs, false \<Rightarrow> r = rhs } \<close>
lemma \<open> assign_match_arms =
    \<lbrakk> match flag { true \<Rightarrow> r = lhs, false \<Rightarrow> r = rhs } \<rbrakk> \<close>
  unfolding assign_match_arms_def by (rule refl)

urust_expr assign_control_rhs
  \<open> r = (if flag { lhs } else { rhs }) \<close>
lemma \<open> assign_control_rhs =
    \<lbrakk> r = (if flag { lhs } else { rhs }) \<rbrakk> \<close>
  unfolding assign_control_rhs_def by (rule refl)

urust_expr assign_mutable_binding
  \<open> let mut x = lhs; *x = rhs; *x \<close>
lemma \<open> assign_mutable_binding =
    \<lbrakk> let mut x = lhs; *x = rhs; *x \<rbrakk> \<close>
  unfolding assign_mutable_binding_def by (rule refl)

end

subsection\<open> Field places \<close>

context
  fixes rp :: \<open>(unit, unit, postfix_outer) Global_Store.ref\<close>
    and field_value :: \<open>64 word\<close>
begin

urust_expr assign_field \<open> rp.inner = \<llangle>undefined :: postfix_inner\<rrangle> \<close>
lemma \<open> assign_field =
    \<lbrakk> rp.inner = \<llangle>undefined :: postfix_inner\<rrangle> \<rbrakk> \<close>
  unfolding assign_field_def by (rule refl)

urust_expr assign_field_chain \<open> rp.inner.value = field_value \<close>
lemma \<open> assign_field_chain = \<lbrakk> rp.inner.value = field_value \<rbrakk> \<close>
  unfolding assign_field_chain_def by (rule refl)

urust_expr assign_grouped_deref_field \<open> (*rp.inner.value) = field_value \<close>
lemma \<open> assign_grouped_deref_field = \<lbrakk> (*rp.inner.value) = field_value \<rbrakk> \<close>
  unfolding assign_grouped_deref_field_def by (rule refl)

urust_expr assign_deref_field_chain \<open> *rp.inner.value = field_value \<close>
lemma \<open> assign_deref_field_chain = \<lbrakk> *rp.inner.value = field_value \<rbrakk> \<close>
  unfolding assign_deref_field_chain_def by (rule refl)

end

section\<open> Compound assignment \<close>

subsection\<open> Supported operators and places \<close>

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rhs other :: \<open>32 word\<close>
begin

urust_expr compound_add_identifier \<open> r += rhs \<close>
lemma \<open> compound_add_identifier = \<lbrakk> r += rhs \<rbrakk> \<close>
  unfolding compound_add_identifier_def by (rule refl)

urust_expr compound_sub_grouped \<open> (r) -= rhs \<close>
lemma \<open> compound_sub_grouped = \<lbrakk> (r) -= rhs \<rbrakk> \<close>
  unfolding compound_sub_grouped_def by (rule refl)

urust_expr compound_mul_deref \<open> *r *= rhs \<close>
lemma \<open> compound_mul_deref = \<lbrakk> *r *= rhs \<rbrakk> \<close>
  unfolding compound_mul_deref_def by (rule refl)

urust_expr compound_mod_identifier \<open> r %= rhs \<close>
lemma \<open> compound_mod_identifier = \<lbrakk> r %= rhs \<rbrakk> \<close>
  unfolding compound_mod_identifier_def by (rule refl)

urust_expr compound_and_identifier \<open> r &= rhs \<close>
lemma \<open> compound_and_identifier = \<lbrakk> r &= rhs \<rbrakk> \<close>
  unfolding compound_and_identifier_def by (rule refl)

urust_expr compound_or_identifier \<open> r |= rhs \<close>
lemma \<open> compound_or_identifier = \<lbrakk> r |= rhs \<rbrakk> \<close>
  unfolding compound_or_identifier_def by (rule refl)

urust_expr compound_xor_identifier \<open> r ^= rhs \<close>
lemma \<open> compound_xor_identifier = \<lbrakk> r ^= rhs \<rbrakk> \<close>
  unfolding compound_xor_identifier_def by (rule refl)

urust_expr compound_rhs_precedence \<open> r -= rhs * other \<close>
lemma \<open> compound_rhs_precedence = \<lbrakk> r -= rhs * other \<rbrakk> \<close>
  unfolding compound_rhs_precedence_def by (rule refl)

urust_expr compound_block_rhs \<open> r ^= { rhs } \<close>
lemma \<open> compound_block_rhs = \<lbrakk> r ^= { rhs } \<rbrakk> \<close>
  unfolding compound_block_rhs_def by (rule refl)

end

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and shift :: \<open>64 word\<close>
begin

urust_expr compound_shift_left \<open> r <<= shift \<close>
lemma \<open> compound_shift_left = \<lbrakk> r <<= shift \<rbrakk> \<close>
  unfolding compound_shift_left_def by (rule refl)

urust_expr compound_shift_right \<open> r >>= shift \<close>
lemma \<open> compound_shift_right = \<lbrakk> r >>= shift \<rbrakk> \<close>
  unfolding compound_shift_right_def by (rule refl)

end

context
  fixes rp :: \<open>(unit, unit, postfix_outer) Global_Store.ref\<close>
    and field_value :: \<open>64 word\<close>
begin

urust_expr compound_field_chain \<open> rp.inner.value %= field_value \<close>
lemma \<open> compound_field_chain = \<lbrakk> rp.inner.value %= field_value \<rbrakk> \<close>
  unfolding compound_field_chain_def by (rule refl)

end

subsection\<open> Mutable locals, associativity, and control-flow boundaries \<close>

context
  fixes a b :: \<open>32 word\<close>
begin

urust_expr compound_mutable_local
  \<open> let mut x = a; x += b; *x \<close>
lemma \<open> compound_mutable_local =
    \<lbrakk> let mut x = a; x += b; *x \<rbrakk> \<close>
  unfolding compound_mutable_local_def by (rule refl)

end

context
  fixes outer :: \<open>(unit, unit, unit) Global_Store.ref\<close>
    and inner :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and rhs :: \<open>32 word\<close>
begin

urust_expr compound_simple_then_compound \<open> outer = inner -= rhs \<close>
lemma \<open> compound_simple_then_compound = \<lbrakk> outer = inner -= rhs \<rbrakk> \<close>
  unfolding compound_simple_then_compound_def by (rule refl)

urust_expr compound_then_simple \<open> outer += inner = rhs \<close>
lemma \<open> compound_then_simple = \<lbrakk> outer += inner = rhs \<rbrakk> \<close>
  unfolding compound_then_simple_def by (rule refl)

urust_expr compound_right_associative \<open> outer += inner += rhs \<close>
lemma \<open> compound_right_associative = \<lbrakk> outer += inner += rhs \<rbrakk> \<close>
  unfolding compound_right_associative_def by (rule refl)

end

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and lhs rhs :: \<open>32 word\<close>
    and flag :: bool
begin

urust_expr compound_grouped_control_rhs
  \<open> r |= (if flag { lhs } else { rhs }) \<close>
lemma \<open> compound_grouped_control_rhs =
    \<lbrakk> r |= (if flag { lhs } else { rhs }) \<rbrakk> \<close>
  unfolding compound_grouped_control_rhs_def by (rule refl)

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

text\<open>
\<open>match_switch\<close> binds the scrutinee into \<open>ncase_selector\<close> (D26).
Numerals become \<open>Some\<close> keys, wildcard becomes \<open>None\<close>, and or-patterns
duplicate the key/body pair. It is first-order; constant and path keys remain deferred.
\<close>

urust_expr msw_lit \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> msw_lit = \<lbrakk> match_switch \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding msw_lit_def by (rule refl)

context fixes n :: nat
begin

text\<open> Multiple numeral arms + wildcard fall-through (context-fixed scrutinee). \<close>
urust_expr msw_multi \<open> match_switch n { 0 \<Rightarrow> \<llangle>False\<rrangle>, 1 \<Rightarrow> \<llangle>True\<rrangle>, 2 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<close>
lemma \<open> msw_multi = \<lbrakk> match_switch n { 0 \<Rightarrow> \<llangle>False\<rrangle>, 1 \<Rightarrow> \<llangle>True\<rrangle>, 2 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<rbrakk> \<close>
  unfolding msw_multi_def by (rule refl)

urust_expr msw_hex \<open> match_switch n { 0xff \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> msw_hex = \<lbrakk> match_switch n { 0xff \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding msw_hex_def by (rule refl)

text\<open> Or-pattern: \<open>1 | 2 | 3\<close> expands to three \<open>(Some _, body)\<close> pairs sharing the arm body. \<close>
urust_expr msw_or \<open> match_switch n { 1 | 2 | 3 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> msw_or = \<lbrakk> match_switch n { 1 | 2 | 3 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding msw_or_def by (rule refl)

text\<open>
Rows cover a let RHS and statement position, where explicit \<open>match_switch\<close>
requires a semicolon.
\<close>
urust_expr msw_let \<open> let r = match_switch n { 0 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }; r \<close>
lemma \<open> msw_let = \<lbrakk> let r = match_switch n { 0 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }; r \<rbrakk> \<close>
  unfolding msw_let_def by (rule refl)

urust_expr msw_stmt \<open> match_switch n { 0 \<Rightarrow> () , _ \<Rightarrow> () } ; () \<close>
lemma \<open> msw_stmt = \<lbrakk> match_switch n { 0 \<Rightarrow> () , _ \<Rightarrow> () } ; () \<rbrakk> \<close>
  unfolding msw_stmt_def by (rule refl)
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
urust_expr mc_opt \<open> match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 } \<close>
lemma \<open> mc_opt = \<lbrakk> match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding mc_opt_def by (rule refl)

text\<open> Result: two variable-binding constructors. \<close>
urust_expr mc_res \<open> match_case xr { Ok(v) \<Rightarrow> v, Err(e) \<Rightarrow> e } \<close>
lemma \<open> mc_res = \<lbrakk> match_case xr { Ok(v) \<Rightarrow> v, Err(e) \<Rightarrow> e } \<rbrakk> \<close>
  unfolding mc_res_def by (rule refl)

text\<open> Wildcard \<open>_\<close> arm. \<close>
urust_expr mc_wild \<open> match_case x { Some(y) \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>
lemma \<open> mc_wild = \<lbrakk> match_case x { Some(y) \<Rightarrow> y, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding mc_wild_def by (rule refl)

text\<open> Constructor with a wildcard argument \<open>Some(_)\<close>. \<close>
urust_expr mc_cwild \<open> match_case x { Some(_) \<Rightarrow> \<llangle>True\<rrangle>, None \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> mc_cwild = \<lbrakk> match_case x { Some(_) \<Rightarrow> \<llangle>True\<rrangle>, None \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding mc_cwild_def by (rule refl)

text\<open> Single-level 2-ary constructor: two binders (leftmost outermost). \<close>
urust_expr mc_pair \<open> match_case p { P2(a, b) \<Rightarrow> a } \<close>
lemma \<open> mc_pair = \<lbrakk> match_case p { P2(a, b) \<Rightarrow> a } \<rbrakk> \<close>
  unfolding mc_pair_def by (rule refl)

urust_expr mc_var \<open> match_case x { y \<Rightarrow> y } \<close>
lemma \<open> mc_var = \<lbrakk> match_case x { y \<Rightarrow> y } \<rbrakk> \<close>
  unfolding mc_var_def by (rule refl)

urust_expr mc_pair_left \<open> match_case p { P2(a, _) \<Rightarrow> a } \<close>
lemma \<open> mc_pair_left = \<lbrakk> match_case p { P2(a, _) \<Rightarrow> a } \<rbrakk> \<close>
  unfolding mc_pair_left_def by (rule refl)

urust_expr mc_pair_right \<open> match_case p { P2(_, b) \<Rightarrow> b } \<close>
lemma \<open> mc_pair_right = \<lbrakk> match_case p { P2(_, b) \<Rightarrow> b } \<rbrakk> \<close>
  unfolding mc_pair_right_def by (rule refl)

urust_expr mc_shadow
  \<open> let y = \<llangle>7 :: nat\<rrangle>; match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> y } \<close>
lemma \<open> mc_shadow =
    \<lbrakk> let y = \<llangle>7 :: nat\<rrangle>; match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> y } \<rbrakk> \<close>
  unfolding mc_shadow_def by (rule refl)

text\<open> As a value (let-RHS). \<close>
urust_expr mc_let \<open> let r = match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 }; r \<close>
lemma \<open> mc_let = \<lbrakk> let r = match_case x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 }; r \<rbrakk> \<close>
  unfolding mc_let_def by (rule refl)

text\<open> As a \<open>;\<close>-terminated statement (the \<open>match_case\<close> keyword has no no-\<open>;\<close> form, like \<open>match_switch\<close>). \<close>
urust_expr mc_stmt \<open> match_case x { Some(_) \<Rightarrow> () , None \<Rightarrow> () } ; () \<close>
lemma \<open> mc_stmt = \<lbrakk> match_case x { Some(_) \<Rightarrow> () , None \<Rightarrow> () } ; () \<rbrakk> \<close>
  unfolding mc_stmt_def by (rule refl)

subsection\<open> Anonymous-binder hygiene \<close>

text\<open>
Wildcards and desugaring binders use \<open>Abs\<close>/\<open>Bound\<close>, preventing name capture.
Rows cover wildcard arms, constructor slots, differing types, and sibling binders.
\<close>

urust_expr mc_hyg_wild \<open> let uu = \<llangle>Some 5 :: nat option\<rrangle>; match_case x { _ \<Rightarrow> uu } \<close>
lemma \<open> mc_hyg_wild = \<lbrakk> let uu = \<llangle>Some 5 :: nat option\<rrangle>; match_case x { _ \<Rightarrow> uu } \<rbrakk> \<close>
  unfolding mc_hyg_wild_def by (rule refl)

text\<open> Wildcard constructor argument. \<close>
urust_expr mc_hyg_ctor_arg \<open> let uu = \<llangle>7 :: nat\<rrangle>; match_case x { Some(_) \<Rightarrow> uu, None \<Rightarrow> uu } \<close>
lemma \<open> mc_hyg_ctor_arg = \<lbrakk> let uu = \<llangle>7 :: nat\<rrangle>; match_case x { Some(_) \<Rightarrow> uu, None \<Rightarrow> uu } \<rbrakk> \<close>
  unfolding mc_hyg_ctor_arg_def by (rule refl)

text\<open> Scrutinee and result types differ. \<close>
urust_expr mc_hyg_typed \<open> let uu = \<llangle>7 :: nat\<rrangle>; match_case x { _ \<Rightarrow> uu } \<close>
lemma \<open> mc_hyg_typed = \<lbrakk> let uu = \<llangle>7 :: nat\<rrangle>; match_case x { _ \<Rightarrow> uu } \<rbrakk> \<close>
  unfolding mc_hyg_typed_def by (rule refl)

text\<open> Source binder with the former scrutinee hint name. \<close>
urust_expr mc_hyg_scrut \<open> let anon_case = \<llangle>7 :: nat\<rrangle>; match_case x { Some(y) \<Rightarrow> anon_case, None \<Rightarrow> anon_case } \<close>
lemma \<open> mc_hyg_scrut = \<lbrakk> let anon_case = \<llangle>7 :: nat\<rrangle>; match_case x { Some(y) \<Rightarrow> anon_case, None \<Rightarrow> anon_case } \<rbrakk> \<close>
  unfolding mc_hyg_scrut_def by (rule refl)

text\<open> Named and anonymous sibling slots. \<close>
urust_expr mc_hyg_sibling \<open> match_case p { P2(uu, _) \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<close>
lemma \<open> mc_hyg_sibling = \<lbrakk> match_case p { P2(uu, _) \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<rbrakk> \<close>
  unfolding mc_hyg_sibling_def by (rule refl)

end


section\<open> Rich case-pattern lowering \<close>

text\<open>
Case arms are normalized in stages: recursive disjunction expansion, recursive
constructor compilation, and ordered guard fall-through. Case numerals remain
frontend-fidelity rejections. These rows replace the four former D-7 negative tests.
\<close>

subsection\<open> Former D-7 rejection rows \<close>

urust_expr rich_explicit_nested
  \<open> match_case \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
lemma \<open> rich_explicit_nested =
    \<lbrakk> match_case \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<rbrakk> \<close>
  unfolding rich_explicit_nested_def by (rule refl)

urust_expr rich_explicit_or
  \<open> match_case \<llangle>Some (0 :: nat)\<rrangle> { Some(_) | None \<Rightarrow> () } \<close>
lemma \<open> rich_explicit_or =
    \<lbrakk> match_case \<llangle>Some (0 :: nat)\<rrangle> { Some(_) | None \<Rightarrow> () } \<rbrakk> \<close>
  unfolding rich_explicit_or_def by (rule refl)

urust_expr rich_bare_nested
  \<open> match \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
lemma \<open> rich_bare_nested =
    \<lbrakk> match \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<rbrakk> \<close>
  unfolding rich_bare_nested_def by (rule refl)

urust_expr rich_bare_or
  \<open> match \<llangle>Some (0 :: nat)\<rrangle> { Some(_) | None \<Rightarrow> () } \<close>
lemma \<open> rich_bare_or =
    \<lbrakk> match \<llangle>Some (0 :: nat)\<rrangle> { Some(_) | None \<Rightarrow> () } \<rbrakk> \<close>
  unfolding rich_bare_or_def by (rule refl)

subsection\<open> Guards \<close>

context fixes x :: \<open>32 word option\<close>
begin

urust_expr rich_guard_scope
  \<open> let floor = \<llangle>0 :: 32 word\<rrangle>; match x { Some(y) if y > floor \<Rightarrow> y, _ \<Rightarrow> floor } \<close>
lemma \<open> rich_guard_scope =
    \<lbrakk> let floor = \<llangle>0 :: 32 word\<rrangle>; match x { Some(y) if y > floor \<Rightarrow> y, _ \<Rightarrow> floor } \<rbrakk> \<close>
  unfolding rich_guard_scope_def by (rule refl)

urust_expr rich_guard_fallthrough
  \<open> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_guard_fallthrough =
    \<lbrakk> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_guard_fallthrough_def by (rule refl)

urust_expr rich_guard_multi_fallthrough
  \<open> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) if False \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>, Some(y) if True \<Rightarrow> y, _ \<Rightarrow> \<llangle>3 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_guard_multi_fallthrough =
    \<lbrakk> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) if False \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>, Some(y) if True \<Rightarrow> y, _ \<Rightarrow> \<llangle>3 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_guard_multi_fallthrough_def by (rule refl)

urust_expr rich_guard_intervening_pattern
  \<open> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, None \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, _ \<Rightarrow> \<llangle>3 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_guard_intervening_pattern =
    \<lbrakk> match x { Some(y) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, None \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, _ \<Rightarrow> \<llangle>3 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_guard_intervening_pattern_def by (rule refl)

urust_expr rich_guard_wild_fallthrough
  \<open> match x { _ if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_guard_wild_fallthrough =
    \<lbrakk> match x { _ if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, Some(y) \<Rightarrow> y, None \<Rightarrow> \<llangle>2 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_guard_wild_fallthrough_def by (rule refl)

urust_expr rich_guard_if
  \<open> match x { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_guard_if =
    \<lbrakk> match x { Some(y) if (if True { True } else { False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_guard_if_def by (rule refl)

urust_expr rich_guard_match
  \<open> match x { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_guard_match =
    \<lbrakk> match x { Some(y) if (match Some(y) { Some(_) \<Rightarrow> True, None \<Rightarrow> False }) \<Rightarrow> y, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_guard_match_def by (rule refl)

end

subsection\<open> Disjunction expansion \<close>

datatype rich_case = RMA "32 word" | RMB "32 word" | RMD "32 word" | RMC
datatype rich_leaf = RLA | RLB | RLC
datatype rich_pair = RP rich_leaf rich_leaf

context fixes r :: rich_case and ro :: \<open>rich_case option\<close> and rp :: rich_pair
begin

urust_expr rich_or_top
  \<open> match_case r { RMA(x) | RMB(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_or_top =
    \<lbrakk> match_case r { RMA(x) | RMB(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_or_top_def by (rule refl)

urust_expr rich_or_three_top
  \<open> match_case r { RMA(x) | RMB(x) | RMD(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_or_three_top =
    \<lbrakk> match_case r { RMA(x) | RMB(x) | RMD(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_or_three_top_def by (rule refl)

urust_expr rich_or_nested
  \<open> match_case ro { Some(RMA(x) | RMB(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_or_nested =
    \<lbrakk> match_case ro { Some(RMA(x) | RMB(x)) \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_or_nested_def by (rule refl)

urust_expr rich_or_guarded
  \<open> match r { RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_or_guarded =
    \<lbrakk> match r { RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_or_guarded_def by (rule refl)

urust_expr rich_or_nested_slot
  \<open> match_case rp { RP(RLA, RLA | RLB) \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> rich_or_nested_slot =
    \<lbrakk> match_case rp { RP(RLA, RLA | RLB) \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding rich_or_nested_slot_def by (rule refl)

urust_expr rich_or_three_nested_slot
  \<open> match_case rp { RP(RLA, RLA | RLB | RLC) \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> rich_or_three_nested_slot =
    \<lbrakk> match_case rp { RP(RLA, RLA | RLB | RLC) \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding rich_or_three_nested_slot_def by (rule refl)

urust_expr rich_or_three_guard_fallthrough
  \<open> match r { RMA(x) | RMB(x) | RMD(x) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, RMA(x) | RMB(x) | RMD(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>
lemma \<open> rich_or_three_guard_fallthrough =
    \<lbrakk> match r { RMA(x) | RMB(x) | RMD(x) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, RMA(x) | RMB(x) | RMD(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<rbrakk> \<close>
  unfolding rich_or_three_guard_fallthrough_def by (rule refl)

end

context fixes outer :: nat and x :: \<open>nat option\<close>
begin
urust_expr rich_or_independent
  \<open> match_case x { Some(outer) | None \<Rightarrow> outer } \<close>
lemma \<open> rich_or_independent =
    \<lbrakk> match_case x { Some(outer) | None \<Rightarrow> outer } \<rbrakk> \<close>
  unfolding rich_or_independent_def by (rule refl)
end

subsection\<open> Recursive constructors and capture \<close>

context
  fixes deep2 :: \<open>nat option option\<close>
  fixes deep3 :: \<open>nat option option option\<close>
  fixes mixed :: \<open>pair2 option\<close>
begin

urust_expr rich_depth_two
  \<open> match_case deep2 { Some(Some(y)) \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>
lemma \<open> rich_depth_two =
    \<lbrakk> match_case deep2 { Some(Some(y)) \<Rightarrow> y, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding rich_depth_two_def by (rule refl)

urust_expr rich_depth_three
  \<open> match_case deep3 { Some(Some(Some(_))) \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> rich_depth_three =
    \<lbrakk> match_case deep3 { Some(Some(Some(_))) \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding rich_depth_three_def by (rule refl)

urust_expr rich_mixed_slots
  \<open> match_case mixed { Some(P2(_, y)) \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>
lemma \<open> rich_mixed_slots =
    \<lbrakk> match_case mixed { Some(P2(_, y)) \<Rightarrow> y, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding rich_mixed_slots_def by (rule refl)

urust_expr rich_antiquotation_capture
  \<open> match_case deep2 { Some(Some(y)) \<Rightarrow> \<llangle>y\<rrangle>, _ \<Rightarrow> 0 } \<close>
lemma \<open> rich_antiquotation_capture =
    \<lbrakk> match_case deep2 { Some(Some(y)) \<Rightarrow> \<llangle>y\<rrangle>, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding rich_antiquotation_capture_def by (rule refl)

urust_expr rich_shadow
  \<open> let y = \<llangle>7 :: nat\<rrangle>; match_case deep2 { Some(Some(y)) \<Rightarrow> \<llangle>y\<rrangle>, _ \<Rightarrow> y } \<close>
lemma \<open> rich_shadow =
    \<lbrakk> let y = \<llangle>7 :: nat\<rrangle>; match_case deep2 { Some(Some(y)) \<Rightarrow> \<llangle>y\<rrangle>, _ \<Rightarrow> y } \<rbrakk> \<close>
  unfolding rich_shadow_def by (rule refl)

end

subsection\<open> Numeric switch boundary \<close>

text\<open>
Bare numeric matches continue to select switch lowering. Explicit or constructor-nested
case numerals are pinned as frontend-fidelity rejections in the negative theory.
\<close>

context fixes n :: nat
begin

urust_expr rich_numeric_switch
  \<open> match n { 2 \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> rich_numeric_switch =
    \<lbrakk> match n { 2 \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding rich_numeric_switch_def by (rule refl)

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

urust_expr value_pat_bool
  \<open> match b { true \<Rightarrow> "yes", false \<Rightarrow> "no" } \<close>
lemma \<open> value_pat_bool =
    \<lbrakk> match b { true \<Rightarrow> "yes", false \<Rightarrow> "no" } \<rbrakk> \<close>
  unfolding value_pat_bool_def by (rule refl)

urust_expr value_pat_string_explicit
  \<open> match_case s { "ok" \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> value_pat_string_explicit =
    \<lbrakk> match_case s { "ok" \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding value_pat_string_explicit_def by (rule refl)

urust_expr value_pat_antiquotation
  \<open> match n { \<llangle>(2 :: nat)\<rrangle> \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> value_pat_antiquotation =
    \<lbrakk> match n { \<llangle>(2 :: nat)\<rrangle> \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding value_pat_antiquotation_def by (rule refl)

urust_expr value_pat_nested_constructor
  \<open> match ob { Some(true) \<Rightarrow> False, Some(false) \<Rightarrow> True, None \<Rightarrow> False } \<close>
lemma \<open> value_pat_nested_constructor =
    \<lbrakk> match ob { Some(true) \<Rightarrow> False, Some(false) \<Rightarrow> True, None \<Rightarrow> False } \<rbrakk> \<close>
  unfolding value_pat_nested_constructor_def by (rule refl)

urust_expr value_pat_disjunction
  \<open> match b { true | false \<Rightarrow> True } \<close>
lemma \<open> value_pat_disjunction =
    \<lbrakk> match b { true | false \<Rightarrow> True } \<rbrakk> \<close>
  unfolding value_pat_disjunction_def by (rule refl)

urust_expr value_pat_source_guard
  \<open> match b { true if False \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> value_pat_source_guard =
    \<lbrakk> match b { true if False \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding value_pat_source_guard_def by (rule refl)

urust_expr value_pat_capture
  \<open> let needle = \<llangle>2 :: nat\<rrangle>; match on { Some(\<llangle>needle\<rrangle>) \<Rightarrow> needle, _ \<Rightarrow> 0 } \<close>
lemma \<open> value_pat_capture =
    \<lbrakk> let needle = \<llangle>2 :: nat\<rrangle>; match on { Some(\<llangle>needle\<rrangle>) \<Rightarrow> needle, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding value_pat_capture_def by (rule refl)

end

urust_expr value_pat_nested_tuple
  \<open> match_case \<llangle>(True, (Some False, TNil))\<rrangle> {
      (true, Some(x)) \<Rightarrow> x, _ \<Rightarrow> False } \<close>
lemma \<open> value_pat_nested_tuple =
    \<lbrakk> match_case \<llangle>(True, (Some False, TNil))\<rrangle> {
      (true, Some(x)) \<Rightarrow> x, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding value_pat_nested_tuple_def by (rule refl)

urust_expr value_pat_guard_order
  \<open> match \<llangle>VPP True (String.implode ''ok'')\<rrangle> {
      VPP(true, "ok") if True \<Rightarrow> True, _ \<Rightarrow> False } \<close>
lemma \<open> value_pat_guard_order =
    \<lbrakk> match \<llangle>VPP True (String.implode ''ok'')\<rrangle> {
      VPP(true, "ok") if True \<Rightarrow> True, _ \<Rightarrow> False } \<rbrakk> \<close>
  unfolding value_pat_guard_order_def by (rule refl)

section\<open> Tuple case patterns \<close>

text\<open>
Tuple case patterns lower to generated \<open>Pair\<close>/\<open>TNil\<close> trees. They compose
recursively with constructors and disjunction expansion.
\<close>

urust_expr tuple_match_explicit
  \<open> match_case \<llangle>(1 :: nat, (True, TNil))\<rrangle> { (x, _) \<Rightarrow> x } \<close>
lemma \<open> tuple_match_explicit =
    \<lbrakk> match_case \<llangle>(1 :: nat, (True, TNil))\<rrangle> { (x, _) \<Rightarrow> x } \<rbrakk> \<close>
  unfolding tuple_match_explicit_def by (rule refl)

urust_expr tuple_match_bare
  \<open> match \<llangle>(1 :: nat, (True, TNil))\<rrangle> { (_, y) \<Rightarrow> y } \<close>
lemma \<open> tuple_match_bare =
    \<lbrakk> match \<llangle>(1 :: nat, (True, TNil))\<rrangle> { (_, y) \<Rightarrow> y } \<rbrakk> \<close>
  unfolding tuple_match_bare_def by (rule refl)

urust_expr tuple_match_three
  \<open> match_case \<llangle>(1 :: nat, (True, (2 :: nat, TNil)))\<rrangle> { (x, _, z) \<Rightarrow> z } \<close>
lemma \<open> tuple_match_three =
    \<lbrakk> match_case \<llangle>(1 :: nat, (True, (2 :: nat, TNil)))\<rrangle> { (x, _, z) \<Rightarrow> z } \<rbrakk> \<close>
  unfolding tuple_match_three_def by (rule refl)

urust_expr tuple_match_nested
  \<open> match_case \<llangle>(1 :: nat, ((True, (2 :: nat, TNil)), TNil))\<rrangle> { (x, (_, z)) \<Rightarrow> z } \<close>
lemma \<open> tuple_match_nested =
    \<lbrakk> match_case \<llangle>(1 :: nat, ((True, (2 :: nat, TNil)), TNil))\<rrangle> { (x, (_, z)) \<Rightarrow> z } \<rbrakk> \<close>
  unfolding tuple_match_nested_def by (rule refl)

urust_expr tuple_match_in_constructor
  \<open> match_case \<llangle>Some (1 :: nat, (True, TNil))\<rrangle> { Some((x, y)) \<Rightarrow> x, None \<Rightarrow> 0 } \<close>
lemma \<open> tuple_match_in_constructor =
    \<lbrakk> match_case \<llangle>Some (1 :: nat, (True, TNil))\<rrangle> { Some((x, y)) \<Rightarrow> x, None \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding tuple_match_in_constructor_def by (rule refl)

urust_expr tuple_match_constructor_inside
  \<open> match_case \<llangle>(Some (1 :: nat), (True, TNil))\<rrangle> { (Some(x), _) \<Rightarrow> x, (None, _) \<Rightarrow> 0 } \<close>
lemma \<open> tuple_match_constructor_inside =
    \<lbrakk> match_case \<llangle>(Some (1 :: nat), (True, TNil))\<rrangle> { (Some(x), _) \<Rightarrow> x, (None, _) \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding tuple_match_constructor_inside_def by (rule refl)

urust_expr tuple_match_or_inside
  \<open> match_case \<llangle>(Some (1 :: nat), (True, TNil))\<rrangle> { (Some(_) | None, y) \<Rightarrow> y } \<close>
lemma \<open> tuple_match_or_inside =
    \<lbrakk> match_case \<llangle>(Some (1 :: nat), (True, TNil))\<rrangle> { (Some(_) | None, y) \<Rightarrow> y } \<rbrakk> \<close>
  unfolding tuple_match_or_inside_def by (rule refl)


section\<open> Advanced pattern parity \<close>

subsection\<open> Grouped, borrow, alias, and range patterns \<close>

urust_expr adv_grouped
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { (Some(x)) \<Rightarrow> x, (_) \<Rightarrow> 0 } \<close>
lemma \<open> adv_grouped =
    \<lbrakk> match_case \<llangle>Some (7 :: nat)\<rrangle> { (Some(x)) \<Rightarrow> x, (_) \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_grouped_def by (rule refl)

urust_expr adv_grouped_let \<open> let (x) = \<llangle>7 :: nat\<rrangle>; x \<close>
lemma \<open> adv_grouped_let = \<lbrakk> let (x) = \<llangle>7 :: nat\<rrangle>; x \<rbrakk> \<close>
  unfolding adv_grouped_let_def by (rule refl)

urust_expr adv_grouped_switch
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { (1) \<Rightarrow> \<llangle>True\<rrangle>, (_) \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> adv_grouped_switch =
    \<lbrakk> match_switch \<llangle>1 :: nat\<rrangle> { (1) \<Rightarrow> \<llangle>True\<rrangle>, (_) \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding adv_grouped_switch_def by (rule refl)

urust_expr adv_borrow
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(&x) \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_borrow =
    \<lbrakk> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(&x) \<Rightarrow> x, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_borrow_def by (rule refl)

urust_expr adv_borrow_mut
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(& mut x) \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_borrow_mut =
    \<lbrakk> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(& mut x) \<Rightarrow> x, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_borrow_mut_def by (rule refl)

urust_expr adv_alias
  \<open> match \<llangle>Some (7 :: nat)\<rrangle> { whole @ Some(v) \<Rightarrow> whole, _ \<Rightarrow> None } \<close>
lemma \<open> adv_alias =
    \<lbrakk> match \<llangle>Some (7 :: nat)\<rrangle> { whole @ Some(v) \<Rightarrow> whole, _ \<Rightarrow> None } \<rbrakk> \<close>
  unfolding adv_alias_def by (rule refl)

urust_expr adv_alias_nested
  \<open> match \<llangle>Some (Some (7 :: nat))\<rrangle> { Some(whole @ Some(v)) \<Rightarrow> \<llangle>whole\<rrangle>, _ \<Rightarrow> \<llangle>None\<rrangle> } \<close>
lemma \<open> adv_alias_nested =
    \<lbrakk> match \<llangle>Some (Some (7 :: nat))\<rrangle> { Some(whole @ Some(v)) \<Rightarrow> \<llangle>whole\<rrangle>, _ \<Rightarrow> \<llangle>None\<rrangle> } \<rbrakk> \<close>
  unfolding adv_alias_nested_def by (rule refl)

urust_expr adv_alias_shadow
  \<open> let whole = \<llangle>None :: nat option\<rrangle>; match \<llangle>Some (7 :: nat)\<rrangle> { whole @ Some(v) \<Rightarrow> whole, _ \<Rightarrow> whole } \<close>
lemma \<open> adv_alias_shadow =
    \<lbrakk> let whole = \<llangle>None :: nat option\<rrangle>; match \<llangle>Some (7 :: nat)\<rrangle> { whole @ Some(v) \<Rightarrow> whole, _ \<Rightarrow> whole } \<rbrakk> \<close>
  unfolding adv_alias_shadow_def by (rule refl)

urust_expr adv_range_exclusive
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(5..7) \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<close>
lemma \<open> adv_range_exclusive =
    \<lbrakk> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(5..7) \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<rbrakk> \<close>
  unfolding adv_range_exclusive_def by (rule refl)

urust_expr adv_range_inclusive
  \<open> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(5..=7) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> adv_range_inclusive =
    \<lbrakk> match_case \<llangle>Some (7 :: nat)\<rrangle> { Some(5..=7) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding adv_range_inclusive_def by (rule refl)

urust_expr adv_range_guard
  \<open> match_case \<llangle>Some (6 :: nat)\<rrangle> { Some(5..=7) if True \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Some(5..=7) \<Rightarrow> \<llangle>2 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>3 :: nat\<rrangle> } \<close>
lemma \<open> adv_range_guard =
    \<lbrakk> match_case \<llangle>Some (6 :: nat)\<rrangle> { Some(5..=7) if True \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Some(5..=7) \<Rightarrow> \<llangle>2 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>3 :: nat\<rrangle> } \<rbrakk> \<close>
  unfolding adv_range_guard_def by (rule refl)

urust_expr adv_range_nested
  \<open> match \<llangle>Some (6 :: nat)\<rrangle> { Some(5..=7) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> adv_range_nested =
    \<lbrakk> match \<llangle>Some (6 :: nat)\<rrangle> { Some(5..=7) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding adv_range_nested_def by (rule refl)

subsection\<open> Slice patterns \<close>

urust_expr adv_slice_empty
  \<open> match \<llangle>([] :: nat list)\<rrangle> { [] \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> adv_slice_empty =
    \<lbrakk> match \<llangle>([] :: nat list)\<rrangle> { [] \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding adv_slice_empty_def by (rule refl)

urust_expr adv_slice_closed
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, y] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_slice_closed =
    \<lbrakk> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, y] \<Rightarrow> x, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_slice_closed_def by (rule refl)

urust_expr adv_slice_prefix
  \<open> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_slice_prefix =
    \<lbrakk> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [head, ..] \<Rightarrow> head, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_slice_prefix_def by (rule refl)

urust_expr adv_slice_suffix
  \<open> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_slice_suffix =
    \<lbrakk> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [.., y, z] \<Rightarrow> y, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_slice_suffix_def by (rule refl)

urust_expr adv_slice_middle
  \<open> match \<llangle>[1 :: nat, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> z, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_slice_middle =
    \<lbrakk> match \<llangle>[1 :: nat, 2, 3, 4]\<rrangle> { [a, b, .., y, z] \<Rightarrow> z, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_slice_middle_def by (rule refl)

urust_expr adv_slice_short
  \<open> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> adv_slice_short =
    \<lbrakk> match \<llangle>[1 :: nat, 2, 3]\<rrangle> { [a, b, .., y, z] \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding adv_slice_short_def by (rule refl)

urust_expr adv_slice_nested
  \<open> match \<llangle>Some [1 :: nat, 2, 3]\<rrangle> { Some([a, .., z]) \<Rightarrow> z, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_slice_nested =
    \<lbrakk> match \<llangle>Some [1 :: nat, 2, 3]\<rrangle> { Some([a, .., z]) \<Rightarrow> z, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_slice_nested_def by (rule refl)

urust_expr adv_slice_guard_or
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, ..] | [] if True \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
lemma \<open> adv_slice_guard_or =
    \<lbrakk> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, ..] | [] if True \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<rbrakk> \<close>
  unfolding adv_slice_guard_or_def by (rule refl)

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

urust_expr adv_struct_reordered
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_right: y, adv_left: x } \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_struct_reordered =
    \<lbrakk> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_right: y, adv_left: x } \<Rightarrow> x, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_struct_reordered_def by (rule refl)

urust_expr adv_struct_shorthand
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left, adv_right } \<Rightarrow> adv_right, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_struct_shorthand =
    \<lbrakk> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left, adv_right } \<Rightarrow> adv_right, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_struct_shorthand_def by (rule refl)

urust_expr adv_struct_rest
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left, .. } \<Rightarrow> adv_left, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_struct_rest =
    \<lbrakk> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left, .. } \<Rightarrow> adv_left, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_struct_rest_def by (rule refl)

urust_expr adv_struct_nested
  \<open> match \<llangle>AdvNested (Some (3 :: nat)) [4, 5]\<rrangle> { AdvNested { adv_option: Some(x), adv_values: [y, .., z] } if True \<Rightarrow> z, _ \<Rightarrow> 0 } \<close>
lemma \<open> adv_struct_nested =
    \<lbrakk> match \<llangle>AdvNested (Some (3 :: nat)) [4, 5]\<rrangle> { AdvNested { adv_option: Some(x), adv_values: [y, .., z] } if True \<Rightarrow> z, _ \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding adv_struct_nested_def by (rule refl)

urust_expr adv_struct_or
  \<open> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left: _, adv_right: _ } | AdvOther \<Rightarrow> \<llangle>True\<rrangle> } \<close>
lemma \<open> adv_struct_or =
    \<lbrakk> match \<llangle>AdvStruct 1 2\<rrangle> { AdvStruct { adv_left: _, adv_right: _ } | AdvOther \<Rightarrow> \<llangle>True\<rrangle> } \<rbrakk> \<close>
  unfolding adv_struct_or_def by (rule refl)

urust_expr adv_struct_datatype_record
  \<open> match \<llangle>make_adv_datatype_record 3 4\<rrangle> { adv_datatype_record { adv_dr_right: y, adv_dr_left: x } \<Rightarrow> y } \<close>
lemma \<open> adv_struct_datatype_record =
    \<lbrakk> match \<llangle>make_adv_datatype_record 3 4\<rrangle> { adv_datatype_record { adv_dr_right: y, adv_dr_left: x } \<Rightarrow> y } \<rbrakk> \<close>
  unfolding adv_struct_datatype_record_def by (rule refl)

section\<open> Bare \<open>match\<close> (automatic case/switch routing, D32) \<close>

text\<open>
Bare \<open>match\<close> routes constructor/disjunction heads to case and numerals to switch;
ambiguous identifier/wildcard heads default to case. It alone supports semicolon-free
statement sequencing.
\<close>

context fixes x :: \<open>nat option\<close> and n :: nat
begin

text\<open> Constructor and binding patterns route to the case lowering. \<close>
urust_expr ma_case \<open> match x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 } \<close>
lemma \<open> ma_case = \<lbrakk> match x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding ma_case_def by (rule refl)

text\<open> Numeral and wildcard patterns route to the switch lowering. \<close>
urust_expr ma_switch \<open> match n { 0 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<close>
lemma \<open> ma_switch = \<lbrakk> match n { 0 \<Rightarrow> \<llangle>False\<rrangle>, _ \<Rightarrow> \<llangle>True\<rrangle> } \<rbrakk> \<close>
  unfolding ma_switch_def by (rule refl)

text\<open> Identifier/wildcard arms are compatible with both lowerings and deliberately default to case. \<close>
urust_expr ma_ambiguous \<open> match x { None \<Rightarrow> 0, _ \<Rightarrow> 1 } \<close>
lemma \<open> ma_ambiguous = \<lbrakk> match x { None \<Rightarrow> 0, _ \<Rightarrow> 1 } \<rbrakk> \<close>
  unfolding ma_ambiguous_def by (rule refl)

text\<open> Bare \<open>match\<close> in a let RHS. \<close>
urust_expr ma_let \<open> let r = match x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 }; r \<close>
lemma \<open> ma_let = \<lbrakk> let r = match x { Some(y) \<Rightarrow> y, None \<Rightarrow> 0 }; r \<rbrakk> \<close>
  unfolding ma_let_def by (rule refl)

text\<open> Bare \<open>match\<close> is a semicolon-free block-like statement; the explicit forms remain unchanged. \<close>
urust_expr ma_stmt \<open> match x { Some(_) \<Rightarrow> (), None \<Rightarrow> () } () \<close>
lemma \<open> ma_stmt = \<lbrakk> match x { Some(_) \<Rightarrow> (), None \<Rightarrow> () } () \<rbrakk> \<close>
  unfolding ma_stmt_def by (rule refl)

text\<open> Nested bare matches re-enter \<open>uval\<close>; the outer arms route to case and the inner arms to switch. \<close>
urust_expr ma_nested
  \<open> match x { Some(y) \<Rightarrow> match y { 0 \<Rightarrow> 1, _ \<Rightarrow> 2 }, None \<Rightarrow> 0 } \<close>
lemma \<open> ma_nested =
    \<lbrakk> match x { Some(y) \<Rightarrow> match y { 0 \<Rightarrow> 1, _ \<Rightarrow> 2 }, None \<Rightarrow> 0 } \<rbrakk> \<close>
  unfolding ma_nested_def by (rule refl)

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

urust_expr bind_let_rhs_outer
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let x = x; x \<close>
lemma \<open> bind_let_rhs_outer =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; let x = x; x \<rbrakk> \<close>
  unfolding bind_let_rhs_outer_def by (rule refl)

urust_expr bind_let_three_deep
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let x = x; let x = x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_let_three_deep =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; let x = x; let x = x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_let_three_deep_def by (rule refl)

urust_expr bind_let_cross_names
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let y = x; let x = y; \<llangle>x + y\<rrangle> \<close>
lemma \<open> bind_let_cross_names =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; let y = x; let x = y; \<llangle>x + y\<rrangle> \<rbrakk> \<close>
  unfolding bind_let_cross_names_def by (rule refl)

urust_expr bind_const_then_let
  \<open> const x = \<llangle>1 :: nat\<rrangle>; let x = x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_const_then_let =
    \<lbrakk> const x = \<llangle>1 :: nat\<rrangle>; let x = x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_const_then_let_def by (rule refl)

urust_expr bind_let_then_const
  \<open> let x = \<llangle>1 :: nat\<rrangle>; const x = x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_let_then_const =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; const x = x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_let_then_const_def by (rule refl)

text\<open> A binder introduced inside a block or branch is absent from the enclosing continuation. \<close>

urust_expr bind_block_scope
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let result = { let x = \<llangle>2 :: nat\<rrangle>; x }; x \<close>
lemma \<open> bind_block_scope =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; let result = { let x = \<llangle>2 :: nat\<rrangle>; x }; x \<rbrakk> \<close>
  unfolding bind_block_scope_def by (rule refl)

urust_expr bind_if_branch_scope
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let result = if True { let x = x; x } else { let x = x; x }; x \<close>
lemma \<open> bind_if_branch_scope =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; let result = if True { let x = x; x } else { let x = x; x }; x \<rbrakk> \<close>
  unfolding bind_if_branch_scope_def by (rule refl)

text\<open> Expression antiquotations use the same lexical environment as value antiquotations. \<close>

urust_expr bind_expression_antiquotation
  \<open> let x = \<llangle>5 :: nat\<rrangle>; \<epsilon>\<open>\<up>x\<close> \<close>
lemma \<open> bind_expression_antiquotation =
    \<lbrakk> let x = \<llangle>5 :: nat\<rrangle>; \<epsilon>\<open>\<up>x\<close> \<rbrakk> \<close>
  unfolding bind_expression_antiquotation_def by (rule refl)

urust_expr bind_tuple_rhs_outer
  \<open>
    let x = \<llangle>1 :: nat\<rrangle>;
    let y = \<llangle>True\<rrangle>;
    let (x, y) = (x, y);
    \<llangle>(x, y)\<rrangle>
  \<close>
lemma \<open> bind_tuple_rhs_outer =
    \<lbrakk>
      let x = \<llangle>1 :: nat\<rrangle>;
      let y = \<llangle>True\<rrangle>;
      let (x, y) = (x, y);
      \<llangle>(x, y)\<rrangle>
    \<rbrakk> \<close>
  unfolding bind_tuple_rhs_outer_def by (rule refl)

urust_expr bind_tuple_nested_shadow
  \<open>
    let x = \<llangle>1 :: nat\<rrangle>;
    let y = \<llangle>2 :: nat\<rrangle>;
    let z = \<llangle>3 :: nat\<rrangle>;
    let (x, (y, z)) = (x, (y, z));
    \<llangle>x + y + z\<rrangle>
  \<close>
lemma \<open> bind_tuple_nested_shadow =
    \<lbrakk>
      let x = \<llangle>1 :: nat\<rrangle>;
      let y = \<llangle>2 :: nat\<rrangle>;
      let z = \<llangle>3 :: nat\<rrangle>;
      let (x, (y, z)) = (x, (y, z));
      \<llangle>x + y + z\<rrangle>
    \<rbrakk> \<close>
  unfolding bind_tuple_nested_shadow_def by (rule refl)

urust_expr bind_tuple_wildcard_preserves_outer
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let (_, y) = (x, \<llangle>True\<rrangle>); \<llangle>(x, y)\<rrangle> \<close>
lemma \<open> bind_tuple_wildcard_preserves_outer =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; let (_, y) = (x, \<llangle>True\<rrangle>); \<llangle>(x, y)\<rrangle> \<rbrakk> \<close>
  unfolding bind_tuple_wildcard_preserves_outer_def by (rule refl)

urust_expr bind_const_tuple_shadow
  \<open> let x = \<llangle>1 :: nat\<rrangle>; let y = \<llangle>2 :: nat\<rrangle>; const (x, y) = (y, x); \<llangle>x + y\<rrangle> \<close>
lemma \<open> bind_const_tuple_shadow =
    \<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; let y = \<llangle>2 :: nat\<rrangle>; const (x, y) = (y, x); \<llangle>x + y\<rrangle> \<rbrakk> \<close>
  unfolding bind_const_tuple_shadow_def by (rule refl)

urust_expr bind_tuple_successive_shadow
  \<open>
    let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>);
    let (x, y) = (y, x);
    \<llangle>x + y\<rrangle>
  \<close>
lemma \<open> bind_tuple_successive_shadow =
    \<lbrakk>
      let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>);
      let (x, y) = (y, x);
      \<llangle>x + y\<rrangle>
    \<rbrakk> \<close>
  unfolding bind_tuple_successive_shadow_def by (rule refl)


subsection\<open> Mutable and immutable transitions \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

urust_expr bind_immutable_to_mutable
  \<open> let x = \<llangle>1 :: 32 word\<rrangle>; let mut x = x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_immutable_to_mutable =
    \<lbrakk> let x = \<llangle>1 :: 32 word\<rrangle>; let mut x = x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_immutable_to_mutable_def by (rule refl)

urust_expr bind_mutable_to_immutable
  \<open> let mut x = \<llangle>1 :: 32 word\<rrangle>; let x = *x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_mutable_to_immutable =
    \<lbrakk> let mut x = \<llangle>1 :: 32 word\<rrangle>; let x = *x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_mutable_to_immutable_def by (rule refl)

urust_expr bind_mutable_to_mutable
  \<open> let mut x = \<llangle>1 :: 32 word\<rrangle>; let mut x = *x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_mutable_to_mutable =
    \<lbrakk> let mut x = \<llangle>1 :: 32 word\<rrangle>; let mut x = *x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_mutable_to_mutable_def by (rule refl)

urust_expr bind_mutable_block_scope
  \<open>
    let mut x = \<llangle>1 :: 32 word\<rrangle>;
    let inner = { let mut x = *x; *x };
    *x
  \<close>
lemma \<open> bind_mutable_block_scope =
    \<lbrakk>
      let mut x = \<llangle>1 :: 32 word\<rrangle>;
      let inner = { let mut x = *x; *x };
      *x
    \<rbrakk> \<close>
  unfolding bind_mutable_block_scope_def by (rule refl)

urust_expr bind_mutable_then_match
  \<open>
    let mut x = \<llangle>1 :: 32 word\<rrangle>;
    match Some(*x) { Some(x) \<Rightarrow> x, None \<Rightarrow> *x }
  \<close>
lemma \<open> bind_mutable_then_match =
    \<lbrakk>
      let mut x = \<llangle>1 :: 32 word\<rrangle>;
      match Some(*x) { Some(x) \<Rightarrow> x, None \<Rightarrow> *x }
    \<rbrakk> \<close>
  unfolding bind_mutable_then_match_def by (rule refl)

urust_expr bind_match_then_mutable
  \<open>
    match \<llangle>Some (1 :: 32 word)\<rrangle> {
      Some(x) \<Rightarrow> { let mut x = x; *x },
      None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
    }
  \<close>
lemma \<open> bind_match_then_mutable =
    \<lbrakk>
      match \<llangle>Some (1 :: 32 word)\<rrangle> {
        Some(x) \<Rightarrow> { let mut x = x; *x },
        None \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
      }
    \<rbrakk> \<close>
  unfolding bind_match_then_mutable_def by (rule refl)

urust_expr bind_mutable_tuple_shadow
  \<open>
    let x = \<llangle>1 :: nat\<rrangle>;
    let y = \<llangle>2 :: nat\<rrangle>;
    let mut (x, y) = (x, y);
    \<llangle>x + y\<rrangle>
  \<close>
lemma \<open> bind_mutable_tuple_shadow =
    \<lbrakk>
      let x = \<llangle>1 :: nat\<rrangle>;
      let y = \<llangle>2 :: nat\<rrangle>;
      let mut (x, y) = (x, y);
      \<llangle>x + y\<rrangle>
    \<rbrakk> \<close>
  unfolding bind_mutable_tuple_shadow_def by (rule refl)

context fixes x :: \<open>32 word\<close>
begin
urust_expr bind_hol_mutable_shadow
  \<open> let mut x = x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_hol_mutable_shadow =
    \<lbrakk> let mut x = x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_mutable_shadow_def by (rule refl)
end


subsection\<open> Match arms, guards, and recursive patterns \<close>

datatype binder_shadow_sum =
    BinderNat nat
  | BinderBool bool

urust_expr bind_match_arm_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x }
  \<close>
lemma \<open> bind_match_arm_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x }
    \<rbrakk> \<close>
  unfolding bind_match_arm_shadow_def by (rule refl)

urust_expr bind_match_case_arm_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x }
  \<close>
lemma \<open> bind_match_case_arm_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x }
    \<rbrakk> \<close>
  unfolding bind_match_case_arm_shadow_def by (rule refl)

urust_expr bind_match_scrutinee_outer
  \<open>
    let x = \<llangle>Some (1 :: nat)\<rrangle>;
    match x { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: nat\<rrangle> }
  \<close>
lemma \<open> bind_match_scrutinee_outer =
    \<lbrakk>
      let x = \<llangle>Some (1 :: nat)\<rrangle>;
      match x { Some(x) \<Rightarrow> x, None \<Rightarrow> \<llangle>0 :: nat\<rrangle> }
    \<rbrakk> \<close>
  unfolding bind_match_scrutinee_outer_def by (rule refl)

urust_expr bind_match_guard_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) if x > \<llangle>0 :: nat\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>
lemma \<open> bind_match_guard_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(x) if x > \<llangle>0 :: nat\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
        _ \<Rightarrow> x
      }
    \<rbrakk> \<close>
  unfolding bind_match_guard_shadow_def by (rule refl)

urust_expr bind_match_nested_let
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) \<Rightarrow> { let x = x; \<llangle>x\<rrangle> },
      None \<Rightarrow> x
    }
  \<close>
lemma \<open> bind_match_nested_let =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(x) \<Rightarrow> { let x = x; \<llangle>x\<rrangle> },
        None \<Rightarrow> x
      }
    \<rbrakk> \<close>
  unfolding bind_match_nested_let_def by (rule refl)

urust_expr bind_match_nested_match
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) \<Rightarrow> match Some(x) { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x },
      None \<Rightarrow> x
    }
  \<close>
lemma \<open> bind_match_nested_match =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(x) \<Rightarrow> match Some(x) { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x },
        None \<Rightarrow> x
      }
    \<rbrakk> \<close>
  unfolding bind_match_nested_match_def by (rule refl)

text\<open> The same source name may be independently typed in sibling alternatives. \<close>

urust_expr bind_match_sibling_types
  \<open>
    match \<llangle>BinderNat 1\<rrangle> {
      BinderNat(x) \<Rightarrow> { let _ = \<llangle>x\<rrangle>; () },
      BinderBool(x) \<Rightarrow> { let _ = \<llangle>x\<rrangle>; () }
    }
  \<close>
lemma \<open> bind_match_sibling_types =
    \<lbrakk>
      match \<llangle>BinderNat 1\<rrangle> {
        BinderNat(x) \<Rightarrow> { let _ = \<llangle>x\<rrangle>; () },
        BinderBool(x) \<Rightarrow> { let _ = \<llangle>x\<rrangle>; () }
      }
    \<rbrakk> \<close>
  unfolding bind_match_sibling_types_def by (rule refl)

urust_expr bind_match_sibling_same_name
  \<open>
    match \<llangle>Ok (1 :: nat) :: (nat, nat) result\<rrangle> {
      Ok(x) \<Rightarrow> \<llangle>x\<rrangle>,
      Err(x) \<Rightarrow> \<llangle>x\<rrangle>
    }
  \<close>
lemma \<open> bind_match_sibling_same_name =
    \<lbrakk>
      match \<llangle>Ok (1 :: nat) :: (nat, nat) result\<rrangle> {
        Ok(x) \<Rightarrow> \<llangle>x\<rrangle>,
        Err(x) \<Rightarrow> \<llangle>x\<rrangle>
      }
    \<rbrakk> \<close>
  unfolding bind_match_sibling_same_name_def by (rule refl)

urust_expr bind_match_tuple_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let y = \<llangle>True\<rrangle>;
    match \<llangle>(1 :: nat, (False, TNil))\<rrangle> { (x, y) \<Rightarrow> \<llangle>(x, y)\<rrangle> }
  \<close>
lemma \<open> bind_match_tuple_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      let y = \<llangle>True\<rrangle>;
      match \<llangle>(1 :: nat, (False, TNil))\<rrangle> { (x, y) \<Rightarrow> \<llangle>(x, y)\<rrangle> }
    \<rbrakk> \<close>
  unfolding bind_match_tuple_shadow_def by (rule refl)

urust_expr bind_match_nested_tuple_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let y = \<llangle>True\<rrangle>;
    match \<llangle>Some (1 :: nat, (False, TNil))\<rrangle> {
      Some((x, y)) \<Rightarrow> \<llangle>(x, y)\<rrangle>,
      None \<Rightarrow> \<llangle>(x, y)\<rrangle>
    }
  \<close>
lemma \<open> bind_match_nested_tuple_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      let y = \<llangle>True\<rrangle>;
      match \<llangle>Some (1 :: nat, (False, TNil))\<rrangle> {
        Some((x, y)) \<Rightarrow> \<llangle>(x, y)\<rrangle>,
        None \<Rightarrow> \<llangle>(x, y)\<rrangle>
      }
    \<rbrakk> \<close>
  unfolding bind_match_nested_tuple_shadow_def by (rule refl)

urust_expr bind_match_alias_shadow
  \<open>
    let whole = \<llangle>None :: nat option\<rrangle>;
    let value = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      whole @ Some(value) \<Rightarrow> { let _ = \<llangle>whole\<rrangle>; \<llangle>value\<rrangle> },
      _ \<Rightarrow> value
    }
  \<close>
lemma \<open> bind_match_alias_shadow =
    \<lbrakk>
      let whole = \<llangle>None :: nat option\<rrangle>;
      let value = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>Some (1 :: nat)\<rrangle> {
        whole @ Some(value) \<Rightarrow> { let _ = \<llangle>whole\<rrangle>; \<llangle>value\<rrangle> },
        _ \<Rightarrow> value
      }
    \<rbrakk> \<close>
  unfolding bind_match_alias_shadow_def by (rule refl)

urust_expr bind_match_slice_shadow
  \<open>
    let head = \<llangle>0 :: nat\<rrangle>;
    let tail = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>[1 :: nat, 2, 3]\<rrangle> {
      [head, .., tail] \<Rightarrow> { let _ = \<llangle>tail\<rrangle>; \<llangle>head\<rrangle> },
      _ \<Rightarrow> head
    }
  \<close>
lemma \<open> bind_match_slice_shadow =
    \<lbrakk>
      let head = \<llangle>0 :: nat\<rrangle>;
      let tail = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>[1 :: nat, 2, 3]\<rrangle> {
        [head, .., tail] \<Rightarrow> { let _ = \<llangle>tail\<rrangle>; \<llangle>head\<rrangle> },
        _ \<Rightarrow> head
      }
    \<rbrakk> \<close>
  unfolding bind_match_slice_shadow_def by (rule refl)

urust_expr bind_match_struct_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let y = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>AdvStruct 1 2\<rrangle> {
      AdvStruct { adv_left: x, adv_right: y } \<Rightarrow> \<llangle>x + y\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>
lemma \<open> bind_match_struct_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      let y = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>AdvStruct 1 2\<rrangle> {
        AdvStruct { adv_left: x, adv_right: y } \<Rightarrow> \<llangle>x + y\<rrangle>,
        _ \<Rightarrow> x
      }
    \<rbrakk> \<close>
  unfolding bind_match_struct_shadow_def by (rule refl)

text\<open> Struct shorthand binders also shadow their same-named HOL selector constants. \<close>

urust_expr bind_match_struct_shorthand_shadow
  \<open>
    let adv_left = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>AdvStruct 1 2\<rrangle> {
      AdvStruct { adv_left, adv_right } \<Rightarrow> \<llangle>adv_left + adv_right\<rrangle>,
      _ \<Rightarrow> adv_left
    }
  \<close>
lemma \<open> bind_match_struct_shorthand_shadow =
    \<lbrakk>
      let adv_left = \<llangle>0 :: nat\<rrangle>;
      match \<llangle>AdvStruct 1 2\<rrangle> {
        AdvStruct { adv_left, adv_right } \<Rightarrow> \<llangle>adv_left + adv_right\<rrangle>,
        _ \<Rightarrow> adv_left
      }
    \<rbrakk> \<close>
  unfolding bind_match_struct_shorthand_shadow_def by (rule refl)

urust_expr bind_match_or_shadow
  \<open>
    let x = \<llangle>0 :: 32 word\<rrangle>;
    match \<llangle>RMA (1 :: 32 word)\<rrangle> {
      RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>
lemma \<open> bind_match_or_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: 32 word\<rrangle>;
      match \<llangle>RMA (1 :: 32 word)\<rrangle> {
        RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
        _ \<Rightarrow> x
      }
    \<rbrakk> \<close>
  unfolding bind_match_or_shadow_def by (rule refl)

urust_expr bind_match_result_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    let x = match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> x, None \<Rightarrow> x };
    \<llangle>x\<rrangle>
  \<close>
lemma \<open> bind_match_result_shadow =
    \<lbrakk>
      let x = \<llangle>0 :: nat\<rrangle>;
      let x = match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> x, None \<Rightarrow> x };
      \<llangle>x\<rrangle>
    \<rbrakk> \<close>
  unfolding bind_match_result_shadow_def by (rule refl)

text\<open> Switch lowering has no source binder; its generated scrutinee binder remains hygienic. \<close>

urust_expr bind_match_switch_hygiene
  \<open>
    let anon_case = \<llangle>7 :: nat\<rrangle>;
    match_switch \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> anon_case, _ \<Rightarrow> anon_case }
  \<close>
lemma \<open> bind_match_switch_hygiene =
    \<lbrakk>
      let anon_case = \<llangle>7 :: nat\<rrangle>;
      match_switch \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> anon_case, _ \<Rightarrow> anon_case }
    \<rbrakk> \<close>
  unfolding bind_match_switch_hygiene_def by (rule refl)


subsection\<open> HOL context binders shadowed by micro-Rust binders \<close>

text\<open>
Here \<open>x\<close> and \<open>y\<close> are introduced by Isabelle's surrounding proof context. Each RHS or
scrutinee initially resolves to that HOL free; a same-named micro-Rust binder then takes precedence
only in its lexical continuation or arm.
\<close>

context fixes x :: nat and y :: bool
begin

urust_expr bind_hol_context_baseline \<open> \<llangle>(x, y)\<rrangle> \<close>
lemma \<open> bind_hol_context_baseline = \<lbrakk> \<llangle>(x, y)\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_context_baseline_def by (rule refl)

urust_expr bind_hol_let_shadow
  \<open> let x = x; x \<close>
lemma \<open> bind_hol_let_shadow = \<lbrakk> let x = x; x \<rbrakk> \<close>
  unfolding bind_hol_let_shadow_def by (rule refl)

urust_expr bind_hol_let_antiquotation
  \<open> let x = x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_hol_let_antiquotation = \<lbrakk> let x = x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_let_antiquotation_def by (rule refl)

urust_expr bind_hol_let_mixed_antiquotation
  \<open> let x = x; \<llangle>(x, y)\<rrangle> \<close>
lemma \<open> bind_hol_let_mixed_antiquotation =
    \<lbrakk> let x = x; \<llangle>(x, y)\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_let_mixed_antiquotation_def by (rule refl)

urust_expr bind_hol_let_chain
  \<open> let x = x; let x = x; \<llangle>x\<rrangle> \<close>
lemma \<open> bind_hol_let_chain = \<lbrakk> let x = x; let x = x; \<llangle>x\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_let_chain_def by (rule refl)

urust_expr bind_hol_tuple_shadow
  \<open> let (x, y) = (x, y); \<llangle>(x, y)\<rrangle> \<close>
lemma \<open> bind_hol_tuple_shadow =
    \<lbrakk> let (x, y) = (x, y); \<llangle>(x, y)\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_tuple_shadow_def by (rule refl)

urust_expr bind_hol_match_shadow
  \<open> match Some(x) { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x } \<close>
lemma \<open> bind_hol_match_shadow =
    \<lbrakk> match Some(x) { Some(x) \<Rightarrow> \<llangle>x\<rrangle>, None \<Rightarrow> x } \<rbrakk> \<close>
  unfolding bind_hol_match_shadow_def by (rule refl)

urust_expr bind_hol_match_guard_shadow
  \<open>
    match Some(x) {
      Some(x) if x == \<llangle>x\<rrangle> \<Rightarrow> x,
      None \<Rightarrow> x
    }
  \<close>
lemma \<open> bind_hol_match_guard_shadow =
    \<lbrakk>
      match Some(x) {
        Some(x) if x == \<llangle>x\<rrangle> \<Rightarrow> x,
        None \<Rightarrow> x
      }
    \<rbrakk> \<close>
  unfolding bind_hol_match_guard_shadow_def by (rule refl)

urust_expr bind_hol_branch_scope
  \<open> let result = if True { let x = x; x } else { x }; \<llangle>(x, y)\<rrangle> \<close>
lemma \<open> bind_hol_branch_scope =
    \<lbrakk> let result = if True { let x = x; x } else { x }; \<llangle>(x, y)\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_branch_scope_def by (rule refl)

end


subsection\<open> Binders named after HOL constants and registered notation \<close>

text\<open>
Direct identifier resolution and embedded HOL parsing must both prefer a lexical binder over a
same-named constant, constructor, selector, or registered notation. A sibling arm without that
binder must continue to resolve the outer meaning.
\<close>

urust_expr bind_constant_id_direct
  \<open> let id = \<llangle>1 :: nat\<rrangle>; id \<close>
lemma \<open> bind_constant_id_direct =
    \<lbrakk> let id = \<llangle>1 :: nat\<rrangle>; id \<rbrakk> \<close>
  unfolding bind_constant_id_direct_def by (rule refl)

urust_expr bind_constants_nested
  \<open> let id = \<llangle>1 :: nat\<rrangle>; let fst = id; \<llangle>id + fst\<rrangle> \<close>
lemma \<open> bind_constants_nested =
    \<lbrakk> let id = \<llangle>1 :: nat\<rrangle>; let fst = id; \<llangle>id + fst\<rrangle> \<rbrakk> \<close>
  unfolding bind_constants_nested_def by (rule refl)

urust_expr bind_constants_tuple
  \<open>
    let (id, fst) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>);
    \<llangle>id + fst\<rrangle>
  \<close>
lemma \<open> bind_constants_tuple =
    \<lbrakk>
      let (id, fst) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>);
      \<llangle>id + fst\<rrangle>
    \<rbrakk> \<close>
  unfolding bind_constants_tuple_def by (rule refl)

urust_expr bind_constant_match
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(id) \<Rightarrow> \<llangle>id\<rrangle>,
      None \<Rightarrow> \<llangle>0 :: nat\<rrangle>
    }
  \<close>
lemma \<open> bind_constant_match =
    \<lbrakk>
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(id) \<Rightarrow> \<llangle>id\<rrangle>,
        None \<Rightarrow> \<llangle>0 :: nat\<rrangle>
      }
    \<rbrakk> \<close>
  unfolding bind_constant_match_def by (rule refl)

urust_expr bind_constructor_names
  \<open>
    let Some = \<llangle>1 :: nat\<rrangle>;
    let None = Some;
    \<llangle>Some + None\<rrangle>
  \<close>
lemma \<open> bind_constructor_names =
    \<lbrakk>
      let Some = \<llangle>1 :: nat\<rrangle>;
      let None = Some;
      \<llangle>Some + None\<rrangle>
    \<rbrakk> \<close>
  unfolding bind_constructor_names_def by (rule refl)

urust_expr bind_notation_direct
  \<open> let myReg = \<llangle>1 :: nat\<rrangle>; myReg \<close>
lemma \<open> bind_notation_direct =
    \<lbrakk> let myReg = \<llangle>1 :: nat\<rrangle>; myReg \<rbrakk> \<close>
  unfolding bind_notation_direct_def by (rule refl)

urust_expr bind_notation_match_scope
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(myReg) \<Rightarrow> \<llangle>myReg\<rrangle>,
      None \<Rightarrow> myReg
    }
  \<close>
lemma \<open> bind_notation_match_scope =
    \<lbrakk>
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(myReg) \<Rightarrow> \<llangle>myReg\<rrangle>,
        None \<Rightarrow> myReg
      }
    \<rbrakk> \<close>
  unfolding bind_notation_match_scope_def by (rule refl)

urust_expr bind_constant_mutable
  \<open> let mut id = \<llangle>1 :: 32 word\<rrangle>; \<llangle>id\<rrangle> \<close>
lemma \<open> bind_constant_mutable =
    \<lbrakk> let mut id = \<llangle>1 :: 32 word\<rrangle>; \<llangle>id\<rrangle> \<rbrakk> \<close>
  unfolding bind_constant_mutable_def by (rule refl)

context fixes id :: nat
begin
urust_expr bind_hol_constant_triple_shadow
  \<open> let id = id; \<llangle>id\<rrangle> \<close>
lemma \<open> bind_hol_constant_triple_shadow =
    \<lbrakk> let id = id; \<llangle>id\<rrangle> \<rbrakk> \<close>
  unfolding bind_hol_constant_triple_shadow_def by (rule refl)
end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open> Regression and divergence cases \<close>

text\<open>
Resolved divergences stay positive; current rejections use the negative harness or
frontend-only golden stubs.
\<close>

subsection\<open> D-1 (RESOLVED 2026-08-25): \<open>if\<close> as a binary-operator operand -- both now reject \<close>

text\<open> An unparenthesized \<open>if\<close> operand is rejected by both parsers; parentheses make it an operand. \<close>
urust_expr d1_paren_operand
  \<open> (if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> }) + \<llangle>3 :: 32 word\<rrangle> \<close>
lemma \<open> d1_paren_operand = \<lbrakk> (if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> }) + \<llangle>3 :: 32 word\<rrangle> \<rbrakk> \<close>
  unfolding d1_paren_operand_def by (rule refl)

subsection\<open> D-2 (RESOLVED 2026-08-25): no-\<open>;\<close> sequencing of block-like expressions -- now accepted \<close>

text\<open> Block-like statements sequence without a trailing \<open>;\<close>, matching the frontend. \<close>
urust_expr d2_blk_seq \<open> { () } { () } \<close>
lemma \<open> d2_blk_seq = \<lbrakk> { () } { () } \<rbrakk> \<close> unfolding d2_blk_seq_def by (rule refl)

urust_expr d2_if_seq \<open> if \<llangle>True\<rrangle> { () } () \<close>
lemma \<open> d2_if_seq = \<lbrakk> if \<llangle>True\<rrangle> { () } () \<rbrakk> \<close> unfolding d2_if_seq_def by (rule refl)

urust_expr d2_ifelse_seq \<open> if \<llangle>True\<rrangle> { () } else { () } () \<close>
lemma \<open> d2_ifelse_seq = \<lbrakk> if \<llangle>True\<rrangle> { () } else { () } () \<rbrakk> \<close> unfolding d2_ifelse_seq_def by (rule refl)

subsection\<open> D-3 (RESOLVED 2026-08-24): a HOL-const-named binder IS captured in an antiquotation \<close>

text\<open> Enclosing binders shadow same-named HOL constants and registered notation names in antiquotations. \<close>
urust_expr div_binder_const \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id\<rrangle> \<close>
lemma \<open> div_binder_const = \<lbrakk> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id\<rrangle> \<rbrakk> \<close> unfolding div_binder_const_def by (rule refl)

urust_expr cap_const_fst \<open> let fst = \<llangle>5 :: nat\<rrangle>; \<llangle>fst\<rrangle> \<close>  \<comment>\<open> binder name = HOL \<open>Product_Type.fst\<close> \<close>
lemma \<open> cap_const_fst = \<lbrakk> let fst = \<llangle>5 :: nat\<rrangle>; \<llangle>fst\<rrangle> \<rbrakk> \<close> unfolding cap_const_fst_def by (rule refl)

urust_expr cap_const_deep \<open> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id + 1\<rrangle> \<close>  \<comment>\<open> buried capture of a const-named binder \<close>
lemma \<open> cap_const_deep = \<lbrakk> let id = \<llangle>5 :: nat\<rrangle>; \<llangle>id + 1\<rrangle> \<rbrakk> \<close> unfolding cap_const_deep_def by (rule refl)

urust_expr cap_notation \<open> let myReg = \<llangle>5 :: nat\<rrangle>; \<llangle>myReg\<rrangle> \<close>  \<comment>\<open> binder name = a registered notation surface name (guard) \<close>
lemma \<open> cap_notation = \<lbrakk> let myReg = \<llangle>5 :: nat\<rrangle>; \<llangle>myReg\<rrangle> \<rbrakk> \<close> unfolding cap_notation_def by (rule refl)

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
