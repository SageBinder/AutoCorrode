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

text\<open>
Generic headers introduce signature-named HOL variables. Each definition below has the same
checked HOL value as its explicit type-escape twin. Ordered Rust scheme metadata, including
unused parameters, is audited separately in the ML companion.
\<close>

urust_fn \<open> fn SignatureIdentity<T>(value: T) -> T { value } \<close>
urust_fn \<open>
fn SignatureIdentityTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_identity_twin: \<open> signature_identity = signature_identity_twin \<close>
  unfolding signature_identity_def signature_identity_twin_def by (rule refl)

urust_fn \<open>
fn SignatureArray<const N: usize>(value: [u8; N]) -> [u8; N] { value }
\<close>
urust_fn \<open>
fn SignatureArrayTwin(value: [u8; \<tau>\<open>'n::len\<close>]) -> [u8; \<tau>\<open>'n::len\<close>] { value }
\<close>
lemma signature_array_twin: \<open> signature_array = signature_array_twin \<close>
  unfolding signature_array_def signature_array_twin_def by (rule refl)

urust_fn \<open>
fn SignatureMixed<'a, T, const N: usize>(value: (T, [u8; N])) -> (T, [u8; N]) { value }
\<close>
urust_fn \<open>
fn SignatureMixedTwin(value: (\<tau>\<open>'t\<close>, [u8; \<tau>\<open>'n::len\<close>]))
  -> (\<tau>\<open>'t\<close>, [u8; \<tau>\<open>'n::len\<close>]) { value }
\<close>
lemma signature_mixed_twin: \<open> signature_mixed = signature_mixed_twin \<close>
  unfolding signature_mixed_def signature_mixed_twin_def by (rule refl)

urust_fn \<open> fn SignatureBorrow<'a, T>(value: &'a mut T) -> &'a mut T { value } \<close>
urust_fn \<open>
fn SignatureBorrowTwin<'a>(value: &'a mut \<tau>\<open>'t\<close>) -> &'a mut \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_borrow_twin: \<open> signature_borrow = signature_borrow_twin \<close>
  unfolding signature_borrow_def signature_borrow_twin_def by (rule refl)

urust_fn \<open> fn SignaturePointer<T>(value: *mut T) -> *mut T { value } \<close>
urust_fn \<open>
fn SignaturePointerTwin(value: *mut \<tau>\<open>'t\<close>) -> *mut \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_pointer_twin: \<open> signature_pointer = signature_pointer_twin \<close>
  unfolding signature_pointer_def signature_pointer_twin_def by (rule refl)

urust_type "SignatureBag<'t>" = \<open> 't list \<close>
urust_type_alias \<open> type SignatureAlias<T> = SignatureBag<T>; \<close>
urust_fn \<open>
fn SignatureMapped<T>(value: SignatureAlias<T>) -> SignatureBag<T> { value }
\<close>
urust_fn \<open>
fn SignatureMappedTwin(value: SignatureAlias<\<tau>\<open>'t\<close>>)
  -> SignatureBag<\<tau>\<open>'t\<close>> { value }
\<close>
lemma signature_mapped_twin: \<open> signature_mapped = signature_mapped_twin \<close>
  unfolding signature_mapped_def signature_mapped_twin_def by (rule refl)

urust_type "SignatureRoleSized<'t, const 'n>" = \<open> ('t, 'n::len) array \<close>
urust_fn \<open>
fn SignatureRoleMapped<T, const N: usize>(value: SignatureRoleSized<T, N>)
  -> SignatureRoleSized<T, N> { value }
\<close>
urust_fn \<open>
fn SignatureRoleMappedTwin(value: SignatureRoleSized<\<tau>\<open>'t\<close>, \<tau>\<open>'n::len\<close>>)
  -> SignatureRoleSized<\<tau>\<open>'t\<close>, \<tau>\<open>'n::len\<close>> { value }
\<close>
lemma signature_role_mapped_twin: \<open> signature_role_mapped = signature_role_mapped_twin \<close>
  unfolding signature_role_mapped_def signature_role_mapped_twin_def by (rule refl)

urust_fn \<open>
fn SignatureRoleGroupedLength<const N: usize>(value: SignatureRoleSized<u8, (N)>)
  -> SignatureRoleSized<u8, (N)> { value }
\<close>
lemma signature_role_grouped_length_twin:
  \<open> signature_role_grouped_length = signature_array_twin \<close>
  unfolding signature_role_grouped_length_def signature_array_twin_def by (rule refl)

urust_fn \<open>
fn SignatureRoleConstEscape<const N: usize>(value: [\<tau>\<open>'n::len0\<close>; 3])
  -> [\<tau>\<open>'n::len0\<close>; 3] { value }
\<close>
urust_fn \<open>
fn SignatureRoleConstEscapeTwin(value: [\<tau>\<open>'n::len0\<close>; 3])
  -> [\<tau>\<open>'n::len0\<close>; 3] { value }
\<close>
lemma signature_role_const_escape_twin:
  \<open> signature_role_const_escape = signature_role_const_escape_twin \<close>
  unfolding signature_role_const_escape_def signature_role_const_escape_twin_def by (rule refl)

urust_fn \<open>
fn SignatureRoleTypeEscape<T>(value: [u8; \<tau>\<open>'t\<close>]) -> [u8; \<tau>\<open>'t\<close>] { value }
\<close>
urust_fn [hol_type_parameters = ["T" \<rightarrow> \<open>'t::len\<close>]] \<open>
fn SignatureRoleExplicitEscape<T>(value: [u8; \<tau>\<open>'t::len\<close>])
  -> [u8; \<tau>\<open>'t::len\<close>] { value }
\<close>
urust_fn \<open>
fn SignatureRoleTypeEscapeTwin(value: [u8; \<tau>\<open>'t::len\<close>])
  -> [u8; \<tau>\<open>'t::len\<close>] { value }
\<close>
lemma signature_role_type_escape_twin:
  \<open> signature_role_type_escape = signature_role_type_escape_twin \<close>
  unfolding signature_role_type_escape_def signature_role_type_escape_twin_def by (rule refl)
lemma signature_role_explicit_escape_twin:
  \<open> signature_role_explicit_escape = signature_role_type_escape_twin \<close>
  unfolding signature_role_explicit_escape_def signature_role_type_escape_twin_def by (rule refl)

urust_fn \<open>
fn SignatureRoleSharedEscapes<T, const N: usize>(value: [\<tau>\<open>'t\<close>; \<tau>\<open>'n\<close>])
  -> [\<tau>\<open>'t\<close>; \<tau>\<open>'n\<close>] { value }
\<close>
urust_fn \<open>
fn SignatureRoleSharedEscapesTwin(value: [\<tau>\<open>'t\<close>; \<tau>\<open>'n::len\<close>])
  -> [\<tau>\<open>'t\<close>; \<tau>\<open>'n::len\<close>] { value }
\<close>
lemma signature_role_shared_escapes_twin:
  \<open> signature_role_shared_escapes = signature_role_shared_escapes_twin \<close>
  unfolding signature_role_shared_escapes_def signature_role_shared_escapes_twin_def by (rule refl)

urust_fn [hol_type_parameters =
  ["T" \<rightarrow> \<open>'element::len\<close>, "N" \<rightarrow> \<open>'length::len\<close>]] \<open>
fn SignatureRoleOrderedEscapes<T, const N: usize>(
  value: [\<tau>\<open>'element::len\<close>; \<tau>\<open>'length::len\<close>])
  -> [\<tau>\<open>'element::len\<close>; \<tau>\<open>'length::len\<close>] { value }
\<close>
urust_fn \<open>
fn SignatureRoleOrderedEscapesTwin(value: [\<tau>\<open>'element::len\<close>; \<tau>\<open>'length::len\<close>])
  -> [\<tau>\<open>'element::len\<close>; \<tau>\<open>'length::len\<close>] { value }
\<close>
lemma signature_role_ordered_escapes_twin:
  \<open> signature_role_ordered_escapes = signature_role_ordered_escapes_twin \<close>
  unfolding signature_role_ordered_escapes_def signature_role_ordered_escapes_twin_def by (rule refl)

urust_fn signature_role_declared_const
  :: \<open> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body \<close>
  \<open> fn SignatureRoleDeclaredConst<const N: usize>(value: [N; 3]) -> [N; 3] { value } \<close>
urust_fn signature_role_declared_type
  :: \<open> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body \<close>
  \<open> fn SignatureRoleDeclaredType<T>(value: [u8; T]) -> [u8; T] { value } \<close>
urust_fn signature_role_declared_twin
  :: \<open> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body \<close>
  \<open> fn SignatureRoleDeclaredTwin(value: u64) -> u64 { value } \<close>
lemma signature_role_declared_const_twin:
  \<open> signature_role_declared_const = signature_role_declared_twin \<close>
  unfolding signature_role_declared_const_def signature_role_declared_twin_def by (rule refl)
lemma signature_role_declared_type_twin:
  \<open> signature_role_declared_type = signature_role_declared_twin \<close>
  unfolding signature_role_declared_type_def signature_role_declared_twin_def by (rule refl)

urust_fn [state = \<open>'t\<close>, abort = \<open>bool\<close>,
  input = \<open>'t prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
fn SignatureChannels<T>(value: T) -> T { value }
\<close>
urust_fn [state = \<open>'t\<close>, abort = \<open>bool\<close>,
  input = \<open>'t prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
fn SignatureChannelsTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_channels_twin: \<open> signature_channels = signature_channels_twin \<close>
  unfolding signature_channels_def signature_channels_twin_def by (rule refl)

urust_trait "Ordered" = \<open> ord \<close>
urust_fn [hol_type_parameters = ["T" \<rightarrow> \<open>'element::type\<close>]] \<open>
fn SignatureBounds<T: Scale>(value: T) -> T where T: Ordered + Marker { value }
\<close>
urust_fn \<open>
fn SignatureBoundsTwin(value: \<tau>\<open>'element::{trait_scale, ord}\<close>)
  -> \<tau>\<open>'element::{trait_scale, ord}\<close> { value }
\<close>
lemma signature_bounds_twin: \<open> signature_bounds = signature_bounds_twin \<close>
  unfolding signature_bounds_def signature_bounds_twin_def by (rule refl)

urust_fn \<open> fn SignatureUnused<T: Ordered, const N: usize>(value: u8) -> u8 { value } \<close>
urust_fn \<open> fn SignatureUnusedTwin(value: u8) -> u8 { value } \<close>
lemma signature_unused_twin: \<open> signature_unused = signature_unused_twin \<close>
  unfolding signature_unused_def signature_unused_twin_def by (rule refl)

urust_fn [register_notation = false] \<open> fn SignatureDisabled<T>(value: T) -> T { value } \<close>
urust_fn [register_notation = false] \<open>
fn SignatureDisabledTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_disabled_twin: \<open> signature_disabled = signature_disabled_twin \<close>
  unfolding signature_disabled_def signature_disabled_twin_def by (rule refl)

urust_fn [abbrev] \<open> fn SignatureAbbrev<T>(value: T) -> T { value } \<close>
urust_fn [abbrev] \<open>
fn SignatureAbbrevTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_abbrev_twin: \<open> signature_abbrev = signature_abbrev_twin \<close> by (rule refl)

urust_fn [abbrev] \<open>
fn SignatureAbbrevOther<T, U: Ordered>(value: T) -> T { value }
\<close>
lemma signature_named_abbreviations: \<open> signature_abbrev = signature_abbrev_other \<close>
  by (rule refl)

urust_fn [abbrev, register_notation = false] \<open>
fn SignatureAbbrevDisabled<T, U: Ordered>(value: T) -> T { value }
\<close>
urust_fn [abbrev, register_notation = false] \<open>
fn SignatureAbbrevDisabledTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_abbrev_disabled_twin: \<open> signature_abbrev_disabled = signature_abbrev_disabled_twin \<close>
  by (rule refl)

urust_fn \<open>
fn SignatureAbbrevCaller(value: u8) -> u8 { SignatureAbbrev(value) }
\<close>
urust_fn \<open>
fn SignatureAbbrevOtherCaller(value: u8) -> u8 { SignatureAbbrevOther(value) }
\<close>
lemma signature_abbreviation_calls: \<open> signature_abbrev_caller = signature_abbrev_other_caller \<close>
  unfolding signature_abbrev_caller_def signature_abbrev_other_caller_def by (rule refl)

urust_fn [application_def] \<open> fn SignatureApplication<T>(value: T) -> T { value } \<close>
urust_fn [application_def] \<open>
fn SignatureApplicationTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { value }
\<close>
lemma signature_application_twin: \<open> signature_application = signature_application_twin \<close>
  unfolding signature_application_def signature_application_twin_def by (rule refl)

urust_fn \<open> fn SignatureCaller(value: u8) -> u8 { SignatureIdentity(value) } \<close>
urust_fn \<open> fn SignatureCallerTwin(value: u8) -> u8 { SignatureIdentityTwin(value) } \<close>
lemma signature_ordinary_call_twin: \<open> signature_caller = signature_caller_twin \<close>
  unfolding signature_caller_def signature_caller_twin_def
    signature_identity_def signature_identity_twin_def by (rule refl)

locale signature_seed =
  fixes seed :: 'ambient
begin
urust_fn \<open>
fn SignatureLocale<T>(value: T) -> T { let spare = seed; value }
\<close>
urust_fn \<open>
fn SignatureLocaleTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { let spare = seed; value }
\<close>
lemma signature_locale_twin: \<open> signature_locale = signature_locale_twin \<close>
  unfolding signature_locale_def signature_locale_twin_def by (rule refl)
end

interpretation signature_nat: signature_seed \<open>3 :: nat\<close> by unfold_locales

locale signature_abbrev_seed =
  fixes seed :: 'ambient
begin
urust_fn [abbrev] \<open>
fn SignatureAbbrevLocale<T, U: Ordered>(value: T) -> T { let spare = seed; value }
\<close>
urust_fn [abbrev] \<open>
fn SignatureAbbrevLocaleTwin(value: \<tau>\<open>'t\<close>) -> \<tau>\<open>'t\<close> { let spare = seed; value }
\<close>
lemma signature_abbrev_locale_twin: \<open> signature_abbrev_locale = signature_abbrev_locale_twin \<close>
  by (rule refl)
end

interpretation signature_abbrev_three: signature_abbrev_seed \<open>3 :: nat\<close> by unfold_locales
interpretation signature_abbrev_four: signature_abbrev_seed \<open>4 :: nat\<close> by unfold_locales
interpretation signature_abbrev_bool: signature_abbrev_seed True by unfold_locales

chapter\<open> Bodies \<close>

text\<open> Reserved for U4 generic body examples. \<close>

chapter\<open> Turbofish \<close>

text\<open> Reserved for U4 generic call examples. \<close>

end
