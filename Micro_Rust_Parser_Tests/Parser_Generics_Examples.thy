(* Readable examples of trait mappings and generic function items.
   The ML audits are in Parser_Generics_ML_Tests. *)

theory Parser_Generics_Examples
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Impl_Trait_Mappings
begin

chapter\<open> Trait mappings \<close>

declare [[urust_verbosity = 0]]

class trait_scale =
  fixes trait_ceiling :: \<open>'a itself \<Rightarrow> nat\<close>

class trait_flag =
  fixes trait_enabled :: \<open>'a itself \<Rightarrow> bool\<close>

instantiation nat :: trait_scale
begin

definition trait_ceiling_nat :: \<open>nat itself \<Rightarrow> nat\<close> where
  \<open>trait_ceiling_nat _ = 12\<close>

instance ..

end

urust_trait "Scale" = \<open> trait_scale \<close>
  urust_consts "CEILING" = \<open> trait_ceiling \<close>

urust_trait "Marker" = \<open> type \<close>

urust_trait "RedundantScale" = \<open> {trait_scale, type} \<close>
  urust_consts "HEIGHT" = \<open> trait_ceiling \<close>

urust_trait "demo::ScaleFlag" = \<open> {trait_scale, trait_flag} \<close>
  urust_consts "CEILING" = \<open> trait_ceiling \<close>
    and "ENABLED" = \<open> trait_enabled \<close>

text\<open> An identical declaration is accepted and retains the original mapping. \<close>

urust_trait "Scale" = \<open> trait_scale \<close>
  urust_consts "CEILING" = \<open> trait_ceiling \<close>

urust_trait "SlotOne" = \<open> type \<close>
  urust_consts "SLOT" = \<open> \<lambda>(_ :: 'a itself). (3 :: nat) \<close>

urust_trait "SlotTwo" = \<open> type \<close>
  urust_consts "SLOT" = \<open> \<lambda>(_ :: 'a itself). (4 :: nat) \<close>

text\<open>
Independent result types are polymorphic. Repeating the literal declaration or renaming its
type variables retains the same typed template.
\<close>

urust_trait "PolymorphicEmpty" = \<open> type \<close>
  urust_consts "POLY_EMPTY" = \<open> \<lambda>(_ :: 'a itself). ([] :: 'b list) \<close>

urust_trait "PolymorphicEmpty" = \<open> type \<close>
  urust_consts "POLY_EMPTY" = \<open> \<lambda>(_ :: 'a itself). ([] :: 'b list) \<close>

urust_trait "PolymorphicEmpty" = \<open> type \<close>
  urust_consts "POLY_EMPTY" = \<open> \<lambda>(_ :: 'x itself). ([] :: 'y list) \<close>

consts trait_fresh_pair :: \<open>'a itself \<Rightarrow> 'b::ord list \<times> 'b list\<close>

urust_trait "FreshPair" = \<open> type \<close>
  urust_consts "POLY_PAIR" = \<open> trait_fresh_pair \<close>

locale trait_offset =
  fixes offset :: nat
begin

definition offset_ceiling :: \<open>'a itself \<Rightarrow> nat\<close> where
  \<open>offset_ceiling _ = offset\<close>

urust_trait "OffsetScale" = \<open> type \<close>
  urust_consts "OFFSET" = \<open> offset_ceiling \<close>

end

interpretation seven_offset: trait_offset 7 .

lemma interpreted_offset_ceiling:
  \<open>seven_offset.offset_ceiling TYPE(bool) = 7\<close>
  unfolding trait_offset.offset_ceiling_def by (rule refl)

text\<open>
The registry is available independently of generic function syntax. Function bounds and
associated-constant expressions consume it in the later units.
\<close>

chapter\<open> Syntax \<close>

text\<open>
An authored empty generic list preserves its surface spelling and elaborates like an absent list.
The legacy empty-list source is retained here as a positive declaration. Lifetime-only lists keep
D160's behavior. A declared HOL signature still accepts retained literal Rust types such as
\<open>impl Trait\<close>; inferred signatures continue to reject them.
\<close>

urust_fn [verbosity = 1] syntax_empty
  \<open> fn SyntaxEmpty<>() {} \<close>

urust_fn [verbosity = 1] syntax_plain
  \<open> fn SyntaxPlain() {} \<close>

lemma syntax_empty_equivalent: \<open> syntax_empty = syntax_plain \<close>
  unfolding syntax_empty_def syntax_plain_def by (rule refl)

urust_fn [verbosity = 1] syntax_legacy_empty
  \<open> fn BadReference<>(value: u8) -> u8 { 0 } \<close>

urust_fn [verbosity = 1] syntax_legacy_plain
  \<open> fn BadReferencePlain(value: u8) -> u8 { 0 } \<close>

lemma syntax_legacy_empty_equivalent: \<open> syntax_legacy_empty = syntax_legacy_plain \<close>
  unfolding syntax_legacy_empty_def syntax_legacy_plain_def by (rule refl)

urust_fn [verbosity = 1] syntax_lifetime
  \<open> fn SyntaxBorrow<'a>(value: &'a mut u8) -> &'a mut u8 { value } \<close>

urust_fn [verbosity = 1] syntax_lifetime_plain
  \<open> fn SyntaxBorrowPlain(value: &mut u8) -> &mut u8 { value } \<close>

lemma syntax_lifetime_equivalent: \<open> syntax_lifetime = syntax_lifetime_plain \<close>
  unfolding syntax_lifetime_def syntax_lifetime_plain_def by (rule refl)

urust_fn [verbosity = 1] syntax_declared_literal
  :: \<open> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body \<close>
  \<open> fn SyntaxRetained(value: impl Marker) -> impl Marker { value } \<close>

urust_fn [verbosity = 1] syntax_declared_plain
  :: \<open> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body \<close>
  \<open> fn SyntaxDeclaredPlain(value: u64) -> u64 { value } \<close>

lemma syntax_declared_literal_equivalent: \<open> syntax_declared_literal = syntax_declared_plain \<close>
  unfolding syntax_declared_literal_def syntax_declared_plain_def by (rule refl)

chapter\<open> Signatures \<close>

text\<open> Reserved for U3 generic signature examples. \<close>

chapter\<open> Bodies \<close>

text\<open> Reserved for U4 generic body examples. \<close>

chapter\<open> Turbofish \<close>

text\<open> Reserved for U4 generic call examples. \<close>

end
