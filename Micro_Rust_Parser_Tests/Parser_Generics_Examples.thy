(* Readable examples of trait mappings and generic function items.
   The ML audits are in Parser_Generics_ML_Tests. *)

theory Parser_Generics_Examples
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Impl_Trait_Mappings
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
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
The registry is available independently of generic function syntax. The following chapters use
these mappings for function bounds and associated-constant expressions.
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

text\<open>
Scoped type and const names share the signature's finalized HOL variables. Associated constants
and const values use the ordinary literal lowering, including array repeat lengths. Entirely
unused parameters remain valid; actual body uses must occur in the complete final signature,
even when a mapped type or generated callee erases their witness.
\<close>

urust_fn \<open>
fn BodyCapacity<const N: usize>(value: [u8; N]) -> usize { N }
\<close>
urust_fn \<open>
fn BodyCapacityTwin(value: [u8; \<tau>\<open>'n::len\<close>]) -> usize {
  \<llangle>of_nat LENGTH('n) :: 64 word\<rrangle>
}
\<close>
lemma body_capacity_twin: \<open> body_capacity = body_capacity_twin \<close>
  unfolding body_capacity_def body_capacity_twin_def by (rule refl)

urust_fn \<open>
fn BodyCapacityAdd<const N: usize>(value: [u8; N]) -> usize { N + 1usize }
\<close>
urust_fn \<open>
fn BodyCapacityAddTwin(value: [u8; \<tau>\<open>'n::len\<close>]) -> usize {
  \<llangle>of_nat LENGTH('n) :: 64 word\<rrangle> + 1usize
}
\<close>
lemma body_capacity_add_twin: \<open> body_capacity_add = body_capacity_add_twin \<close>
  unfolding body_capacity_add_def body_capacity_add_twin_def by (rule refl)

urust_fn \<open>
fn BodyCapacityCompare<const N: usize>(value: [u8; N]) -> bool { N < 5usize }
\<close>
urust_fn \<open>
fn BodyCapacityCompareTwin(value: [u8; \<tau>\<open>'n::len\<close>]) -> bool {
  \<llangle>of_nat LENGTH('n) :: 64 word\<rrangle> < 5usize
}
\<close>
lemma body_capacity_compare_twin: \<open> body_capacity_compare = body_capacity_compare_twin \<close>
  unfolding body_capacity_compare_def body_capacity_compare_twin_def by (rule refl)

urust_fn \<open>
fn BodyBound<T: Scale>(value: T) -> \<tau>\<open>nat\<close> { T::CEILING }
\<close>
urust_fn \<open>
fn BodyBoundTwin(value: \<tau>\<open>'t::trait_scale\<close>) -> \<tau>\<open>nat\<close> {
  \<llangle>trait_ceiling TYPE('t)\<rrangle>
}
\<close>
lemma body_bound_twin: \<open> body_bound = body_bound_twin \<close>
  unfolding body_bound_def body_bound_twin_def by (rule refl)

urust_type "BodyNumber" = \<open> nat \<close>
urust_fn \<open> fn BodyConcrete() -> BodyNumber { BodyNumber::CEILING } \<close>
urust_fn \<open>
fn BodyConcreteTwin() -> BodyNumber { \<llangle>trait_ceiling TYPE(nat)\<rrangle> }
\<close>
lemma body_concrete_twin: \<open> body_concrete = body_concrete_twin \<close>
  unfolding body_concrete_def body_concrete_twin_def by (rule refl)

micro_rust_notation (literal) \<open> 7 :: nat \<close> ("BodyNumber::CEILING")
urust_fn \<open> fn BodyConcreteExplicit() -> BodyNumber { BodyNumber::CEILING } \<close>
urust_fn \<open>
fn BodyConcreteExplicitTwin() -> BodyNumber { \<llangle>7 :: nat\<rrangle> }
\<close>
lemma body_concrete_explicit_twin: \<open> body_concrete_explicit = body_concrete_explicit_twin \<close>
  unfolding body_concrete_explicit_def body_concrete_explicit_twin_def by (rule refl)

urust_datatype \<open> struct BodyParcel<T> { payload: T } \<close>
urust_datatype \<open> struct BodyPacket<T>(T); \<close>
urust_fn \<open>
fn BodyConstruct<T>(value: T) -> BodyParcel<T> { BodyParcel::<T> { payload: value } }
\<close>
urust_fn \<open>
fn BodyConstructTwin(value: \<tau>\<open>'t\<close>) -> BodyParcel<\<tau>\<open>'t\<close>> {
  BodyParcel::<\<tau>\<open>'t\<close>> { payload: value }
}
\<close>
lemma body_construct_twin: \<open> body_construct = body_construct_twin \<close>
  unfolding body_construct_def body_construct_twin_def by (rule refl)

urust_fn \<open>
fn BodyTupleConstruct<T>(value: T) -> BodyPacket<T> { BodyPacket::<T>(value) }
\<close>
urust_fn \<open>
fn BodyTupleConstructTwin(value: \<tau>\<open>'t\<close>) -> BodyPacket<\<tau>\<open>'t\<close>> {
  BodyPacket::<\<tau>\<open>'t\<close>>(value)
}
\<close>
lemma body_tuple_construct_twin: \<open> body_tuple_construct = body_tuple_construct_twin \<close>
  unfolding body_tuple_construct_def body_tuple_construct_twin_def by (rule refl)

urust_fn \<open>
fn BodyShadow<T>(value: T) -> BodyParcel<T> {
  let T = value;
  { BodyParcel::<T> { payload: T } }
}
\<close>
urust_fn \<open>
fn BodyShadowTwin(value: \<tau>\<open>'t\<close>) -> BodyParcel<\<tau>\<open>'t\<close>> {
  let T = value;
  { BodyParcel::<\<tau>\<open>'t\<close>> { payload: T } }
}
\<close>
lemma body_shadow_twin: \<open> body_shadow = body_shadow_twin \<close>
  unfolding body_shadow_def body_shadow_twin_def by (rule refl)

urust_fn \<open>
fn BodyRepeat<const N: usize>(value: [u8; N]) -> \<tau>\<open>8 word list\<close> { [0u8; N] }
\<close>
urust_fn \<open>
fn BodyRepeatTwin(value: [u8; \<tau>\<open>'n::len\<close>]) -> \<tau>\<open>8 word list\<close> {
  \<epsilon>\<open>bind (literal (of_nat LENGTH('n) :: 64 word))
    (\<lambda>count. bind (literal (0 :: 8 word))
      (\<lambda>value. literal (replicate (unsigned count) value)))\<close>
}
\<close>
lemma body_repeat_twin: \<open> body_repeat = body_repeat_twin \<close>
  unfolding body_repeat_def body_repeat_twin_def by (rule refl)
urust_fn \<open>
fn BodyInlineRepeat<const N: usize>(value: [u8; N]) -> \<tau>\<open>8 word list\<close> {
  [const { 0u8 }; N]
}
\<close>
urust_fn \<open>
fn BodyInlineRepeatTwin(value: [u8; \<tau>\<open>'n::len\<close>]) -> \<tau>\<open>8 word list\<close> {
  \<epsilon>\<open>bind (literal (of_nat LENGTH('n) :: 64 word))
    (\<lambda>count. list_sequence (replicate (unsigned count) (literal (0 :: 8 word))))\<close>
}
\<close>
lemma body_inline_repeat_twin: \<open> body_inline_repeat = body_inline_repeat_twin \<close>
  unfolding body_inline_repeat_def body_inline_repeat_twin_def by (rule refl)
urust_trait "BodyLength" = \<open> len0 \<close>
  urust_consts "COUNT" = \<open> \<lambda>(_ :: 'n::len0 itself). (of_nat LENGTH('n) :: 64 word) \<close>
urust_fn \<open>
fn BodyBoundRepeat<T: BodyLength>(value: T) -> \<tau>\<open>8 word list\<close> { [0u8; T::COUNT] }
\<close>
urust_fn \<open>
fn BodyBoundRepeatTwin(value: \<tau>\<open>'t::len0\<close>) -> \<tau>\<open>8 word list\<close> {
  \<epsilon>\<open>bind (literal (of_nat LENGTH('t) :: 64 word))
    (\<lambda>count. bind (literal (0 :: 8 word))
      (\<lambda>value. literal (replicate (unsigned count) value)))\<close>
}
\<close>
lemma body_bound_repeat_twin: \<open> body_bound_repeat = body_bound_repeat_twin \<close>
  unfolding body_bound_repeat_def body_bound_repeat_twin_def by (rule refl)
urust_fn \<open>
fn BodyBoundInlineRepeat<T: BodyLength>(value: T) -> \<tau>\<open>8 word list\<close> {
  [const { 0u8 }; T::COUNT]
}
\<close>
urust_fn \<open>
fn BodyBoundInlineRepeatTwin(value: \<tau>\<open>'t::len0\<close>) -> \<tau>\<open>8 word list\<close> {
  \<epsilon>\<open>bind (literal (of_nat LENGTH('t) :: 64 word))
    (\<lambda>count. list_sequence (replicate (unsigned count) (literal (0 :: 8 word))))\<close>
}
\<close>
lemma body_bound_inline_repeat_twin: \<open> body_bound_inline_repeat = body_bound_inline_repeat_twin \<close>
  unfolding body_bound_inline_repeat_def body_bound_inline_repeat_twin_def by (rule refl)
urust_type "BodyLengthThree" = \<open> 3 \<close>
urust_fn \<open>
fn BodyConcreteRepeat() -> \<tau>\<open>8 word list\<close> { [0u8; BodyLengthThree::COUNT] }
\<close>
urust_fn \<open>
fn BodyConcreteRepeatTwin() -> \<tau>\<open>8 word list\<close> {
  \<epsilon>\<open>bind (literal (of_nat LENGTH(3) :: 64 word))
    (\<lambda>count. bind (literal (0 :: 8 word))
      (\<lambda>value. literal (replicate (unsigned count) value)))\<close>
}
\<close>
lemma body_concrete_repeat_twin: \<open> body_concrete_repeat = body_concrete_repeat_twin \<close>
  unfolding body_concrete_repeat_def body_concrete_repeat_twin_def by (rule refl)

urust_datatype \<open> struct BodyPair<T, U> { first: T, second: U } \<close>
urust_type_alias \<open> type BodyAlias<T> = BodyParcel<T>; \<close>
urust_fn \<open>
fn BodyReordered<T, U>(left: T, right: U) -> BodyPair<T, U> {
  BodyPair::<T, U> { second: right, first: left }
}
\<close>
urust_fn \<open>
fn BodyReorderedTwin(left: \<tau>\<open>'t\<close>, right: \<tau>\<open>'u\<close>)
  -> BodyPair<\<tau>\<open>'t\<close>, \<tau>\<open>'u\<close>> {
  BodyPair::<\<tau>\<open>'t\<close>, \<tau>\<open>'u\<close>> { second: right, first: left }
}
\<close>
lemma body_reordered_twin: \<open> body_reordered = body_reordered_twin \<close>
  unfolding body_reordered_def body_reordered_twin_def by (rule refl)
urust_fn \<open>
fn BodyAliased<T>(value: T) -> BodyAlias<T> { BodyAlias::<T> { payload: value } }
\<close>
urust_fn \<open>
fn BodyAliasedTwin(value: \<tau>\<open>'t\<close>) -> BodyAlias<\<tau>\<open>'t\<close>> {
  BodyAlias::<\<tau>\<open>'t\<close>> { payload: value }
}
\<close>
lemma body_aliased_twin: \<open> body_aliased = body_aliased_twin \<close>
  unfolding body_aliased_def body_aliased_twin_def by (rule refl)
urust_fn \<open>
fn BodyImported<T>(value: T) -> BodyParcel<T> {
  use BodyParcel as Package;
  Package::<T> { payload: value }
}
\<close>
urust_fn \<open>
fn BodyImportedTwin(value: \<tau>\<open>'t\<close>) -> BodyParcel<\<tau>\<open>'t\<close>> {
  use BodyParcel as Package;
  Package::<\<tau>\<open>'t\<close>> { payload: value }
}
\<close>
lemma body_imported_twin: \<open> body_imported = body_imported_twin \<close>
  unfolding body_imported_def body_imported_twin_def by (rule refl)
urust_fn \<open>
fn BodyClosure<T>(value: T) -> BodyParcel<T> {
  let make = |input| { BodyParcel::<T> { payload: input } };
  make(value)
}
\<close>
urust_fn \<open>
fn BodyClosureTwin(value: \<tau>\<open>'t\<close>) -> BodyParcel<\<tau>\<open>'t\<close>> {
  let make = |input| { BodyParcel::<\<tau>\<open>'t\<close>> { payload: input } };
  make(value)
}
\<close>
lemma body_closure_twin: \<open> body_closure = body_closure_twin \<close>
  unfolding body_closure_def body_closure_twin_def by (rule refl)
urust_fn \<open>
fn BodyNamespaces<T>(T: T) -> BodyParcel<T> {
  let T = T;
  { BodyParcel::<T> { payload: T } }
}
\<close>
urust_fn \<open>
fn BodyNamespacesTwin(T: \<tau>\<open>'t\<close>) -> BodyParcel<\<tau>\<open>'t\<close>> {
  let T = T;
  { BodyParcel::<\<tau>\<open>'t\<close>> { payload: T } }
}
\<close>
lemma body_namespaces_twin: \<open> body_namespaces = body_namespaces_twin \<close>
  unfolding body_namespaces_def body_namespaces_twin_def by (rule refl)

urust_fn \<open>
fn BodyAssociatedShadow<T: Scale>(T: T) -> \<tau>\<open>nat\<close> {
  let T = T;
  T::CEILING
}
\<close>
urust_fn \<open>
fn BodyAssociatedShadowTwin(T: \<tau>\<open>'t::trait_scale\<close>) -> \<tau>\<open>nat\<close> {
  let T = T;
  \<llangle>trait_ceiling TYPE('t)\<rrangle>
}
\<close>
lemma body_associated_shadow_twin:
  \<open> body_associated_shadow = body_associated_shadow_twin \<close>
  unfolding body_associated_shadow_def body_associated_shadow_twin_def by (rule refl)
urust_type "BodyConcreteNat" = \<open> nat \<close>
urust_type_alias \<open> type BodyNumericAlias = BodyConcreteNat; \<close>
urust_fn \<open>
fn BodyConcreteAlias() -> BodyConcreteNat { BodyNumericAlias::CEILING }
\<close>
urust_fn \<open>
fn BodyConcreteImported() -> BodyConcreteNat {
  use BodyConcreteNat as Number;
  Number::CEILING
}
\<close>
urust_fn \<open>
fn BodyConcreteHeadTwin() -> BodyConcreteNat { \<llangle>trait_ceiling TYPE(nat)\<rrangle> }
\<close>
lemma body_concrete_alias_twin: \<open> body_concrete_alias = body_concrete_head_twin \<close>
  unfolding body_concrete_alias_def body_concrete_head_twin_def by (rule refl)
lemma body_concrete_imported_twin: \<open> body_concrete_imported = body_concrete_head_twin \<close>
  unfolding body_concrete_imported_def body_concrete_head_twin_def by (rule refl)
urust \<open>
impl BodyConcreteNat {
  fn capacity() -> BodyConcreteNat { Self::CEILING }
}
\<close>
lemma body_concrete_self_twin: \<open> body_concrete_nat_capacity = body_concrete_head_twin \<close>
  unfolding body_concrete_nat_capacity_def body_concrete_head_twin_def by (rule refl)

chapter\<open> Turbofish \<close>

text\<open>
Generated generic functions consume type and const arguments in source declaration order,
including unused parameters and omitting lifetimes. Concrete associated paths, selected type
instances, dot methods and Self calls use the same native dispatch. Explicit-only call notations
retain their leading value arguments; eligible generated-generic/explicit mixed keys reject
turbofish. Calls without turbofish keep ordinary native inference.
\<close>

urust_fn \<open>
fn CallIdentity(value: u8) -> u8 { SignatureIdentity::<u8>(value) }
\<close>
urust_fn \<open>
fn CallIdentityTwin(value: u8) -> u8 { \<epsilon>\<open>signature_identity\<close>(value) }
\<close>
lemma call_identity_twin: \<open> call_identity = call_identity_twin \<close>
  unfolding call_identity_def call_identity_twin_def by (rule refl)

urust_fn \<open>
fn CallArray(value: [u8; 3]) -> [u8; 3] { SignatureArray::<3>(value) }
\<close>
urust_fn \<open>
fn CallArrayTwin(value: [u8; 3]) -> [u8; 3] { \<epsilon>\<open>signature_array\<close>(value) }
\<close>
lemma call_array_twin: \<open> call_array = call_array_twin \<close>
  unfolding call_array_def call_array_twin_def by (rule refl)

urust_fn \<open>
fn CallMixed(value: (u8, [u8; 3])) -> (u8, [u8; 3]) { SignatureMixed::<u8, 3>(value) }
\<close>
urust_fn \<open>
fn CallMixedTwin(value: (u8, [u8; 3])) -> (u8, [u8; 3]) {
  \<epsilon>\<open>signature_mixed\<close>(value)
}
\<close>
lemma call_mixed_twin: \<open> call_mixed = call_mixed_twin \<close>
  unfolding call_mixed_def call_mixed_twin_def by (rule refl)

urust_fn \<open>
fn CallScoped<T, const N: usize>(value: (T, [u8; N])) -> (T, [u8; N]) {
  SignatureMixed::<T, N>(value)
}
\<close>
urust_fn \<open>
fn CallScopedTwin(value: (\<tau>\<open>'t\<close>, [u8; \<tau>\<open>'n::len\<close>]))
  -> (\<tau>\<open>'t\<close>, [u8; \<tau>\<open>'n::len\<close>]) {
  \<epsilon>\<open>signature_mixed\<close>(value)
}
\<close>
lemma call_scoped_twin: \<open> call_scoped = call_scoped_twin \<close>
  unfolding call_scoped_def call_scoped_twin_def by (rule refl)

urust_fn \<open>
fn CallEscapes(value: (u8, [u8; 3])) -> (u8, [u8; 3]) {
  SignatureMixed::<\<tau>\<open>8 word\<close>, \<tau>\<open>3\<close>>(value)
}
\<close>
lemma call_escapes_twin: \<open> call_escapes = call_mixed_twin \<close>
  unfolding call_escapes_def call_mixed_twin_def by (rule refl)

urust_datatype \<open> struct GenericGauge { measure: u8 } \<close>
urust \<open>
impl GenericGauge {
  fn preserve<U>(value: U) -> U { value }
  fn relay<U>(value: U) -> U { Self::preserve::<U>(value) }
  fn keep<U>(self, value: U) -> U { value }
}
\<close>
urust_fn \<open>
fn CallMember(value: u8) -> u8 { GenericGauge::preserve::<u8>(value) }
\<close>
urust_fn \<open>
fn CallMemberTwin(value: u8) -> u8 { \<epsilon>\<open>generic_gauge_preserve\<close>(value) }
\<close>
lemma call_member_twin: \<open> call_member = call_member_twin \<close>
  unfolding call_member_def call_member_twin_def by (rule refl)

urust_fn \<open>
fn CallSelfTwin<U>(value: U) -> U { \<epsilon>\<open>generic_gauge_preserve\<close>(value) }
\<close>
lemma call_self_twin: \<open> generic_gauge_relay = call_self_twin \<close>
  unfolding generic_gauge_relay_def call_self_twin_def by (rule refl)

urust_fn \<open>
fn CallMethod(owner: GenericGauge, value: u8) -> u8 { owner.keep::<u8>(value) }
\<close>
urust_fn \<open>
fn CallMethodTwin(owner: GenericGauge, value: u8) -> u8 {
  \<epsilon>\<open>generic_gauge_keep\<close>(owner, value)
}
\<close>
lemma call_method_twin: \<open> call_method = call_method_twin \<close>
  unfolding call_method_def call_method_twin_def by (rule refl)

urust_datatype \<open> struct GenericHolder<T> { payload: T } \<close>
urust \<open>
impl GenericHolder<u16> {
  fn preserve<U>(value: U) -> U { value }
}
\<close>
urust_fn \<open>
fn CallSelected(value: u8) -> u8 { GenericHolder::<u16>::preserve::<u8>(value) }
\<close>
urust_fn \<open>
fn CallSelectedTwin(value: u8) -> u8 { \<epsilon>\<open>generic_holder_preserve\<close>(value) }
\<close>
lemma call_selected_twin: \<open> call_selected = call_selected_twin \<close>
  unfolding call_selected_def call_selected_twin_def by (rule refl)

urust_fn \<open>
fn CallRepeated<T, const N: usize>(value: (T, [u8; N])) -> (T, [u8; N]) {
  let first = SignatureMixed::<T, N>(value);
  SignatureMixed::<T, N>(first)
}
\<close>
urust_fn \<open>
fn CallRepeatedTwin(value: (\<tau>\<open>'t\<close>, [u8; \<tau>\<open>'n::len\<close>]))
  -> (\<tau>\<open>'t\<close>, [u8; \<tau>\<open>'n::len\<close>]) {
  let first = \<epsilon>\<open>signature_mixed\<close>(value);
  \<epsilon>\<open>signature_mixed\<close>(first)
}
\<close>
lemma call_repeated_twin: \<open> call_repeated = call_repeated_twin \<close>
  unfolding call_repeated_def call_repeated_twin_def by (rule refl)
urust_fn \<open> fn CallTwo<T, U>(value: (T, U)) -> (T, U) { value } \<close>
urust_fn \<open>
fn CallShared<T>(value: (T, T)) -> (T, T) { CallTwo::<T, T>(value) }
\<close>
urust_fn \<open>
fn CallSharedTwin(value: (\<tau>\<open>'t\<close>, \<tau>\<open>'t\<close>))
  -> (\<tau>\<open>'t\<close>, \<tau>\<open>'t\<close>) { \<epsilon>\<open>call_two\<close>(value) }
\<close>
lemma call_shared_twin: \<open> call_shared = call_shared_twin \<close>
  unfolding call_shared_def call_shared_twin_def by (rule refl)
urust_fn [state = \<open>bool\<close>, abort = \<open>nat\<close>,
  input = \<open>unit prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
fn CallIndependent(value: u8) -> u8 { SignatureIdentity::<u8>(value) }
\<close>
urust_fn [state = \<open>bool\<close>, abort = \<open>nat\<close>,
  input = \<open>unit prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
fn CallIndependentTwin(value: u8) -> u8 { \<epsilon>\<open>signature_identity\<close>(value) }
\<close>
lemma call_independent_twin: \<open> call_independent = call_independent_twin \<close>
  unfolding call_independent_def call_independent_twin_def by (rule refl)
urust_fn [state = \<open>8 word\<close>, abort = \<open>bool\<close>,
  input = \<open>8 word prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
fn CallSharedChannel(value: u8) -> u8 { SignatureChannels::<u8>(value) }
\<close>
urust_fn [state = \<open>8 word\<close>, abort = \<open>bool\<close>,
  input = \<open>8 word prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
fn CallSharedChannelTwin(value: u8) -> u8 { \<epsilon>\<open>signature_channels\<close>(value) }
\<close>
lemma call_shared_channel_twin: \<open> call_shared_channel = call_shared_channel_twin \<close>
  unfolding call_shared_channel_def call_shared_channel_twin_def by (rule refl)
urust_fn \<open> fn CallAbbreviation(value: u8) -> u8 { SignatureAbbrev::<u8>(value) } \<close>
urust_fn \<open>
fn CallAbbreviationOther(value: u8) -> u8 { SignatureAbbrevOther::<u8, u16>(value) }
\<close>
lemma call_abbreviation_headers:
  \<open> call_abbreviation = call_abbreviation_other \<close>
  unfolding call_abbreviation_def call_abbreviation_other_def by (rule refl)

locale call_dispatch_seed =
  fixes seed :: 'ambient
begin
urust_fn [abbrev] \<open>
fn LocaleCall<T>(value: (\<tau>\<open>'ambient\<close>, T))
  -> (\<tau>\<open>'ambient\<close>, T) { let spare = seed; value }
\<close>
urust_fn [abbrev] \<open>
fn LocaleOther<T, U: Ordered>(value: (\<tau>\<open>'ambient\<close>, T))
  -> (\<tau>\<open>'ambient\<close>, T) { let spare = seed; value }
\<close>
end
interpretation call_nat_three: call_dispatch_seed \<open>3 :: nat\<close> by unfold_locales
interpretation call_nat_four: call_dispatch_seed \<open>4 :: nat\<close> by unfold_locales
interpretation call_bool: call_dispatch_seed True by unfold_locales
urust_fn \<open>
fn LocaleSelected(value: (bool, u8)) -> (bool, u8) { LocaleCall::<u8>(value) }
\<close>
urust_fn \<open>
fn LocaleSelectedTwin(value: (bool, u8)) -> (bool, u8) {
  \<epsilon>\<open>call_bool.locale_call\<close>(value)
}
\<close>
lemma locale_selected_twin: \<open> locale_selected = locale_selected_twin \<close>
  unfolding locale_selected_def locale_selected_twin_def by (rule refl)
urust_fn \<open>
fn LocaleOtherSelected(value: (bool, u8)) -> (bool, u8) { LocaleOther::<u8, u16>(value) }
\<close>
urust_fn \<open>
fn LocaleOtherSelectedTwin(value: (bool, u8)) -> (bool, u8) {
  \<epsilon>\<open>call_bool.locale_other\<close>(value)
}
\<close>
lemma locale_other_selected_twin: \<open> locale_other_selected = locale_other_selected_twin \<close>
  unfolding locale_other_selected_def locale_other_selected_twin_def by (rule refl)

urust_fn [register_notation = false] \<open>
fn ExplicitControlBackend(leading: usize, value: u8) -> u8 { let spare = leading; value }
\<close>
micro_rust_notation (call) explicit_control_backend ("ExplicitControl")
urust_fn \<open> fn CallExplicit(value: u8) -> u8 { ExplicitControl::<3>(value) } \<close>
urust_fn \<open>
fn CallExplicitTwin(value: u8) -> u8 { \<epsilon>\<open>explicit_control_backend (3 :: 64 word)\<close>(value) }
\<close>
lemma call_explicit_twin: \<open> call_explicit = call_explicit_twin \<close>
  unfolding call_explicit_def call_explicit_twin_def by (rule refl)
urust_fn [abbrev] \<open> fn CallUnusedScale<T: Scale>(value: u8) -> u8 { value } \<close>
urust_fn \<open>
fn CallUnusedBound(value: u8) -> u8 { CallUnusedScale::<\<tau>\<open>nat\<close>>(value) }
\<close>
urust_fn \<open> fn CallUnusedBoundTwin(value: u8) -> u8 { \<epsilon>\<open>call_unused_scale\<close>(value) } \<close>
lemma call_unused_bound_twin: \<open> call_unused_bound = call_unused_bound_twin \<close>
  unfolding call_unused_bound_def call_unused_bound_twin_def by (rule refl)
urust_fn \<open>
fn CallUnusedZero(value: u8) -> u8 { SignatureUnused::<u8, 0>(value) }
\<close>
urust_fn \<open>
fn CallUnusedZeroTwin(value: u8) -> u8 { \<epsilon>\<open>signature_unused\<close>(value) }
\<close>
lemma call_unused_zero_twin: \<open> call_unused_zero = call_unused_zero_twin \<close>
  unfolding call_unused_zero_def call_unused_zero_twin_def by (rule refl)
urust_fn \<open>
fn CallNumericTwin(value: [u8; 16]) -> [u8; 16] { \<epsilon>\<open>signature_array\<close>(value) }
\<close>
urust_fn \<open>
fn CallNumericDecimal(value: [u8; 16]) -> [u8; 16] { SignatureArray::<16>(value) }
\<close>
lemma call_numeric_decimal_twin: \<open> call_numeric_decimal = call_numeric_twin \<close>
  unfolding call_numeric_decimal_def call_numeric_twin_def by (rule refl)
urust_fn \<open>
fn CallNumericHex(value: [u8; 16]) -> [u8; 16] { SignatureArray::<0x_10>(value) }
\<close>
lemma call_numeric_hex_twin: \<open> call_numeric_hex = call_numeric_twin \<close>
  unfolding call_numeric_hex_def call_numeric_twin_def by (rule refl)
urust_fn \<open>
fn CallNumericBinary(value: [u8; 16]) -> [u8; 16] { SignatureArray::<0b_10000>(value) }
\<close>
lemma call_numeric_binary_twin: \<open> call_numeric_binary = call_numeric_twin \<close>
  unfolding call_numeric_binary_def call_numeric_twin_def by (rule refl)
urust_fn \<open>
fn CallNumericOctal(value: [u8; 16]) -> [u8; 16] { SignatureArray::<0o_20>(value) }
\<close>
lemma call_numeric_octal_twin: \<open> call_numeric_octal = call_numeric_twin \<close>
  unfolding call_numeric_octal_def call_numeric_twin_def by (rule refl)
urust_fn \<open>
fn CallNumericSeparator(value: [u8; 16]) -> [u8; 16] { SignatureArray::<1_6>(value) }
\<close>
lemma call_numeric_separator_twin: \<open> call_numeric_separator = call_numeric_twin \<close>
  unfolding call_numeric_separator_def call_numeric_twin_def by (rule refl)
urust_fn \<open>
fn CallNumericEscape(value: [u8; 16]) -> [u8; 16] { SignatureArray::<\<tau>\<open>16\<close>>(value) }
\<close>
lemma call_numeric_escape_twin: \<open> call_numeric_escape = call_numeric_twin \<close>
  unfolding call_numeric_escape_def call_numeric_twin_def by (rule refl)

chapter\<open> Source-only mapping parameters \<close>

text\<open>
Erased source parameters retain their type or const kind and their argument identity, but
contribute no HOL witness. Opaque tags and zero capacities can therefore be forwarded through
explicit turbofish. The mixed mapping retains only its payload witness.
\<close>

urust_type [erase = \<open> 'tag, 'capacity \<close>]
  "ErasureBox<'tag, const 'capacity>" = \<open> nat \<close>
urust_type [erase = \<open> 'tag, 'capacity \<close>]
  "ErasureMixed<'tag, 'payload, const 'capacity>" = \<open> 'payload option \<close>
urust_type_alias \<open> type ErasureAlias<T, const N: usize> = ErasureBox<T, N>; \<close>

urust_fn \<open>
fn ErasureIdentity<T, const N: usize>(value: ErasureAlias<T, N>) -> ErasureBox<T, N> {
  value
}
\<close>
urust_fn \<open>
fn ErasureIdentityTwin(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }
\<close>
lemma erasure_identity_twin: \<open> erasure_identity = erasure_identity_twin \<close>
  unfolding erasure_identity_def erasure_identity_twin_def by (rule refl)

urust_fn \<open>
fn ErasureSourceBody<T, const N: usize>(value: ErasureBox<T, N>) -> ErasureBox<T, N> {
  ErasureIdentity::<T, N>(value)
}
\<close>
urust_fn \<open>
fn ErasureConcrete(value: ErasureBox<foreign::Tag<u8, 0>, 0>)
  -> ErasureBox<foreign::Tag<u8, 0>, 0> {
  ErasureIdentity::<foreign::Tag<u8, 0>, 0>(value)
}
\<close>
urust_fn \<open>
fn ErasureMixedIdentity<Tag, P, const N: usize>(value: ErasureMixed<Tag, P, N>)
  -> ErasureMixed<Tag, P, N> { value }
\<close>
urust_fn \<open>
fn ErasureMixedCall(value: ErasureMixed<Foreign, u8, 0>)
  -> ErasureMixed<Foreign, u8, 0> {
  ErasureMixedIdentity::<Foreign, u8, 0>(value)
}
\<close>

urust_type [erase = \<open> 'tag \<close>]
  "ErasurePayload<'tag, 'payload>" = \<open> 'payload option \<close>
urust_type_alias \<open>
type ErasureArrayAlias<Tag, P, const N: usize> = ErasurePayload<Tag, [P; N]>;
\<close>

urust_type "ErasureBoundEvidence" = \<open> nat \<close>
urust_fn \<open>
fn ErasureBound<T: Scale>(value: ErasureBox<T, 0>) -> ErasureBox<T, 0> { value }
\<close>
urust_fn \<open>
fn ErasureBoundCall(value: ErasureBox<ErasureBoundEvidence, 0>)
  -> ErasureBox<ErasureBoundEvidence, 0> {
  ErasureBound::<ErasureBoundEvidence>(value)
}
\<close>

locale erasure_identity_transport =
  fixes seed :: 'ambient
begin

urust \<open>
  impl ErasurePayload<Alpha, \<tau>\<open>'ambient\<close>> {
    fn locale_identity(self) -> Self { let spare = seed; self }
  }
\<close>

end

interpretation erasure_identity_nat_one: erasure_identity_transport \<open>1 :: nat\<close> .
interpretation erasure_identity_nat_two: erasure_identity_transport \<open>2 :: nat\<close> .
interpretation erasure_identity_bool: erasure_identity_transport True .

chapter\<open> Combined sparse schemes and implicit roles \<close>

urust_type [implicit = \<open> address = 'addr, global = 'store \<close>,
  erase = \<open> 'tag, 'capacity \<close>]
  "GenericCombined<'payload, 'tag, const 'capacity>" =
    \<open> ('addr, 'store, 'payload) Global_Store.ref \<close>
urust_type_alias \<open>
  type GenericCombinedAlias<P, Tag, const N: usize> = GenericCombined<P, Tag, N>;
\<close>

urust_fn \<open>
  fn GenericCombinedIdentity<P, Tag, const N: usize>(value: Option<GenericCombinedAlias<P, Tag, N>>)
      -> Option<GenericCombined<P, Tag, N>> { value }
\<close>
urust_fn \<open>
  fn GenericCombinedEscape(value: \<tau>\<open> ('a, 'g, 'p) Global_Store.ref option \<close>)
      -> \<tau>\<open> ('a, 'g, 'p) Global_Store.ref option \<close> { value }
\<close>
urust_fn \<open>
  fn GenericCombinedForward<P, Tag, const N: usize>(value: Option<GenericCombined<P, Tag, N>>)
      -> Option<GenericCombined<P, Tag, N>> {
    GenericCombinedIdentity::<P, Tag, N>(value)
  }
\<close>
urust_fn \<open>
  fn GenericCombinedCall(value: Option<GenericCombined<u8, foreign::Policy<0>, 0>>)
      -> Option<GenericCombined<u8, foreign::Policy<0>, 0>> {
    GenericCombinedIdentity::<u8, foreign::Policy<0>, 0>(value)
  }
\<close>
urust_fn \<open>
  fn GenericCombinedCallTwin(value: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref option \<close>)
      -> \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref option \<close> {
    GenericCombinedEscape(value)
  }
\<close>

lemma generic_combined_twins:
  shows \<open> generic_combined_identity = generic_combined_escape \<close>
    and \<open> generic_combined_call = generic_combined_call_twin \<close>
  unfolding generic_combined_identity_def generic_combined_escape_def
    generic_combined_call_def generic_combined_call_twin_def by (rule refl)+

end
