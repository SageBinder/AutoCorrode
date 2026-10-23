(* Readable examples of trait mappings and generic function items.
   The ML audits are in Parser_Generics_ML_Tests. *)

theory Parser_Generics_Examples
  imports Parser_Test_Utils
begin

chapter\<open> Trait mappings \<close>

text\<open> Reserved for U1 trait-mapping examples. \<close>

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
