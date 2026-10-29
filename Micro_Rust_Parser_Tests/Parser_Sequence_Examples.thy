(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Sequence_Examples
  imports Parser_Test_Fixtures Micro_Rust_Std_Lib.StdLib_References
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
begin

chapter\<open> Canonical slice and collection denotations \<close>

text\<open>
Slices and the qualified standard vector denote HOL lists. Source identity still distinguishes
them from each other and from fixed arrays. Borrowed slices retain the ordinary reference
structure: shared borrows use read-only references and mutable borrows use references.
\<close>

urust_type_alias \<open> type SequenceBytes = [u8]; \<close>
urust_type_alias \<open> type SequenceAlias<T> = [Option<T>]; \<close>
urust_type_alias \<open> type SequenceAliasAgain<T> = SequenceAlias<T>; \<close>
urust_type "Vec<'a, const 'n>" = \<open>('a, 'n::len) array\<close>

urust_fn sequence_value \<open> fn SequenceValue(value: [u8]) -> [u8] { value } \<close>
urust_fn sequence_value_escape \<open>
  fn SequenceValueEscape(value: \<tau>\<open>8 word list\<close>) -> \<tau>\<open>8 word list\<close> { value }
\<close>
urust_fn sequence_vector \<open>
  fn SequenceVector(value: std::vec::Vec<u8>) -> std::vec::Vec<u8> { value }
\<close>
urust_fn sequence_fixed \<open> fn SequenceFixed(value: [u8; 4]) -> [u8; 4] { value } \<close>
urust_fn sequence_nominal \<open> fn SequenceNominal(value: Vec<u8, 4>) -> Vec<u8, 4> { value } \<close>
urust_fn sequence_alias \<open>
  fn SequenceAliasValue(value: SequenceAliasAgain<u8>) -> [Option<u8>] { value }
\<close>
urust_fn sequence_alias_escape \<open>
  fn SequenceAliasValueEscape(value: \<tau>\<open>8 word option list\<close>)
    -> \<tau>\<open>8 word option list\<close> { value }
\<close>
urust_fn sequence_nested \<open>
  fn SequenceNested(value: [[u8; 4]]) -> [[u8; 4]] { value }
\<close>
urust_fn sequence_nested_escape \<open>
  fn SequenceNestedEscape(value: \<tau>\<open>(8 word, 4) array list\<close>)
    -> \<tau>\<open>(8 word, 4) array list\<close> { value }
\<close>
urust_fn sequence_generic \<open>
  fn SequenceGeneric<T>(value: [T]) -> [T] { value }
\<close>
urust_fn sequence_generic_escape \<open>
  fn SequenceGenericEscape<T>(value: \<tau>\<open>'T list\<close>) -> \<tau>\<open>'T list\<close> { value }
\<close>
urust_fn sequence_call \<open>
  fn SequenceCall(value: [u8]) -> [u8] { SequenceGeneric::<u8>(SequenceValue(value)) }
\<close>
urust_fn sequence_call_escape \<open>
  fn SequenceCallEscape(value: \<tau>\<open>8 word list\<close>) -> \<tau>\<open>8 word list\<close> {
    SequenceGeneric::<u8>(SequenceValue(value))
  }
\<close>
urust_fn sequence_recursive_generic_call \<open>
  fn SequenceRecursiveGenericCall(value: [[u8]]) -> [[u8]] { SequenceGeneric::<[u8]>(value) }
\<close>
urust_fn sequence_recursive_generic_call_escape \<open>
  fn SequenceRecursiveGenericCallEscape(value: \<tau>\<open>8 word list list\<close>)
    -> \<tau>\<open>8 word list list\<close> { SequenceGeneric::<[u8]>(value) }
\<close>
urust_fn sequence_array_element_call \<open>
  fn SequenceArrayElementCall(value: [[u8; 4]]) -> [[u8; 4]] {
    SequenceGeneric::<[u8; 4]>(value)
  }
\<close>
urust_fn sequence_array_element_call_escape \<open>
  fn SequenceArrayElementCallEscape(value: \<tau>\<open>(8 word, 4) array list\<close>)
    -> \<tau>\<open>(8 word, 4) array list\<close> { SequenceGeneric::<[u8; 4]>(value) }
\<close>

lemma sequence_value_twins:
  \<open> sequence_value = sequence_value_escape \<close>
  \<open> sequence_vector = sequence_value_escape \<close>
  \<open> sequence_fixed = sequence_nominal \<close>
  \<open> sequence_alias = sequence_alias_escape \<close>
  \<open> sequence_nested = sequence_nested_escape \<close>
  \<open> sequence_generic = sequence_generic_escape \<close>
  \<open> sequence_call = sequence_call_escape \<close>
  \<open> sequence_recursive_generic_call = sequence_recursive_generic_call_escape \<close>
  \<open> sequence_array_element_call = sequence_array_element_call_escape \<close>
unfolding sequence_value_def sequence_value_escape_def sequence_vector_def
  sequence_fixed_def sequence_nominal_def sequence_alias_def sequence_alias_escape_def
  sequence_nested_def sequence_nested_escape_def sequence_generic_def sequence_generic_escape_def
  sequence_call_def sequence_call_escape_def
  sequence_recursive_generic_call_def sequence_recursive_generic_call_escape_def
  sequence_array_element_call_def sequence_array_element_call_escape_def
by (rule refl)+

context notes [[urust_model_parameters = \<open>
  ["address" \<rightarrow> \<open>'address\<close>, "global" \<rightarrow> \<open>'global\<close>]
\<close>]]
begin
urust_fn sequence_shared \<open>
  fn SequenceShared(value: &[u8]) -> &[u8] { value }
\<close>
urust_fn sequence_shared_lifetime \<open>
  fn SequenceSharedLifetime<'a>(value: &'a [u8]) -> &'a [u8] { value }
\<close>
urust_fn sequence_shared_alias \<open>
  fn SequenceSharedAlias(value: &SequenceBytes) -> &SequenceBytes { value }
\<close>
urust_fn sequence_shared_escape \<open>
  fn SequenceSharedEscape(value: \<tau>\<open>('address, 'global, 8 word list) ro_ref\<close>)
    -> \<tau>\<open>('address, 'global, 8 word list) ro_ref\<close> { value }
\<close>
urust_fn sequence_optional_borrow \<open>
  fn SequenceOptionalBorrow(value: Option<&[u8]>) -> Option<&[u8]> { value }
\<close>
urust_fn sequence_optional_borrow_escape \<open>
  fn SequenceOptionalBorrowEscape(value: \<tau>\<open>('address, 'global, 8 word list) ro_ref option\<close>)
    -> \<tau>\<open>('address, 'global, 8 word list) ro_ref option\<close> { value }
\<close>
urust_fn sequence_mutable \<open>
  fn SequenceMutable(value: &mut [u8]) -> &mut [u8] { value }
\<close>
urust_fn sequence_mutable_lifetime \<open>
  fn SequenceMutableLifetime<'a>(value: &'a mut [u8]) -> &'a mut [u8] { value }
\<close>
urust_fn sequence_shared_static \<open>
  fn SequenceSharedStatic(value: &'static [u8]) -> &'static [u8] { value }
\<close>
urust_fn sequence_mutable_placeholder \<open>
  fn SequenceMutablePlaceholder(value: &'_ mut [u8]) -> &'_ mut [u8] { value }
\<close>
urust_fn sequence_mutable_escape \<open>
  fn SequenceMutableEscape(value: \<tau>\<open>('address, 'global, 8 word list) ref\<close>)
    -> \<tau>\<open>('address, 'global, 8 word list) ref\<close> { value }
\<close>
urust_fn sequence_nested_borrow \<open>
  fn SequenceNestedBorrow(value: &mut [&mut [u8]]) -> &mut [&mut [u8]] { value }
\<close>
urust_fn sequence_nested_borrow_escape \<open>
  fn SequenceNestedBorrowEscape(
    value: \<tau>\<open>('address, 'global, ('address, 'global, 8 word list) ref list) ref\<close>)
    -> \<tau>\<open>('address, 'global, ('address, 'global, 8 word list) ref list) ref\<close> { value }
\<close>
lemma sequence_borrow_twins:
  \<open> sequence_shared = sequence_shared_escape \<close>
  \<open> sequence_shared_lifetime = sequence_shared_escape \<close>
  \<open> sequence_shared_alias = sequence_shared_escape \<close>
  \<open> sequence_optional_borrow = sequence_optional_borrow_escape \<close>
  \<open> sequence_mutable = sequence_mutable_escape \<close>
  \<open> sequence_mutable_lifetime = sequence_mutable_escape \<close>
  \<open> sequence_shared_static = sequence_shared_escape \<close>
  \<open> sequence_mutable_placeholder = sequence_mutable_escape \<close>
  \<open> sequence_nested_borrow = sequence_nested_borrow_escape \<close>
unfolding sequence_shared_def sequence_shared_lifetime_def sequence_shared_alias_def
  sequence_shared_escape_def sequence_mutable_def sequence_mutable_lifetime_def
  sequence_optional_borrow_def sequence_optional_borrow_escape_def
  sequence_mutable_escape_def sequence_nested_borrow_def sequence_nested_borrow_escape_def
  sequence_shared_static_def sequence_mutable_placeholder_def
by (rule refl)+
end

urust_datatype \<open>
  struct SequencePacket<T> { entries: [T], optional: SequenceAlias<T>, vectors: std::vec::Vec<T> }
\<close>
urust_fn sequence_construct \<open>
  fn SequenceConstruct(value: [u8]) -> SequencePacket<u8> {
    SequencePacket { entries: value, optional: \<llangle>[]\<rrangle>, vectors: value }
  }
\<close>
urust_fn sequence_construct_escape \<open>
  fn SequenceConstructEscape(value: \<tau>\<open>8 word list\<close>) -> SequencePacket<u8> {
    SequencePacket { entries: value, optional: \<llangle>[]\<rrangle>, vectors: value }
  }
\<close>
lemma sequence_datatype_twin:
  \<open> sequence_construct = sequence_construct_escape \<close>
  unfolding sequence_construct_def sequence_construct_escape_def by (rule refl)

context reference
begin
context notes [[urust_model_parameters = \<open>
  ["address" \<rightarrow> \<open>'a\<close>, "global" \<rightarrow> \<open>'b\<close>]
\<close>]]
begin
urust_fn sequence_readonly_read \<open> fn SequenceReadonlyRead(value: &[u8]) -> [u8] { *value } \<close>
urust_fn sequence_readonly_read_escape \<open>
  fn SequenceReadonlyReadEscape(value: \<tau>\<open>('a, 'b, 8 word list) ro_ref\<close>)
    -> \<tau>\<open>8 word list\<close> { *value }
\<close>
urust_fn sequence_mutable_read \<open> fn SequenceMutableRead(value: &mut [u8]) -> [u8] { *value } \<close>
urust_fn sequence_mutable_read_escape \<open>
  fn SequenceMutableReadEscape(value: \<tau>\<open>('a, 'b, 8 word list) ref\<close>)
    -> \<tau>\<open>8 word list\<close> { *value }
\<close>
urust_fn sequence_update \<open>
  fn SequenceUpdate(target: &mut [u8], value: [u8]) { *target = value; }
\<close>
urust_fn sequence_update_escape \<open>
  fn SequenceUpdateEscape(target: \<tau>\<open>('a, 'b, 8 word list) ref\<close>,
    value: \<tau>\<open>8 word list\<close>) { *target = value; }
\<close>
lemma sequence_operation_twins:
  \<open> sequence_readonly_read = sequence_readonly_read_escape \<close>
  \<open> sequence_mutable_read = sequence_mutable_read_escape \<close>
  \<open> sequence_update = sequence_update_escape \<close>
unfolding sequence_readonly_read_def sequence_readonly_read_escape_def
  sequence_mutable_read_def sequence_mutable_read_escape_def
  sequence_update_def sequence_update_escape_def
by (rule refl)+
end
end

section\<open> Source identity, sparse generics and locale transport \<close>

urust_type [erase = \<open>'tag\<close>] "SequenceTag<'tag>" = \<open>nat\<close>
urust_type_alias \<open> type SequenceErasedAlias<T> = SequenceTag<[T]>; \<close>
urust_type [erase = \<open>'tag\<close>] "SequencePayload<'tag, 'payload>" = \<open>'payload option\<close>
urust_type_alias \<open> type SequencePayloadAlias<Tag, T> = SequencePayload<Tag, [T]>; \<close>
urust_type [implicit = \<open>address = 'addr, global = 'global\<close>]
  "SequenceElement<'a>" = \<open>('addr, 'global, 'a) ref\<close>

urust_fn sequence_erased_generic \<open>
  fn SequenceErasedGeneric<T>(value: SequenceTag<[T]>) -> SequenceTag<[T]> { value }
\<close>
urust_fn sequence_erased_generic_escape \<open>
  fn SequenceErasedGenericEscape(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }
\<close>
urust_fn sequence_erased_call \<open>
  fn SequenceErasedCall(value: SequenceTag<[u8]>) -> SequenceTag<[u8]> {
    SequenceErasedGeneric::<u8>(value)
  }
\<close>
urust_fn sequence_erased_call_escape \<open>
  fn SequenceErasedCallEscape(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    SequenceErasedGeneric::<u8>(value)
  }
\<close>
lemma sequence_erased_twins:
  \<open> sequence_erased_generic = sequence_erased_generic_escape \<close>
  \<open> sequence_erased_call = sequence_erased_call_escape \<close>
unfolding sequence_erased_generic_def sequence_erased_generic_escape_def
  sequence_erased_call_def sequence_erased_call_escape_def
by (rule refl)+

urust \<open>
  impl SequenceTag<[u8]> {
    \<omega>\<open>name = "sequence_slice_owner_impl"\<close>
    fn sequence_owner(self) -> Self { self }
  }
  impl SequenceTag<std::vec::Vec<u8>> {
    \<omega>\<open>name = "sequence_vector_owner_impl"\<close>
    fn sequence_owner(self) -> Self { self }
  }
  fn SequenceSliceOwner(value: SequenceTag<[u8]>) -> SequenceTag<[u8]> {
    SequenceTag::<[u8]>::sequence_owner(value)
  }
  fn SequenceVectorOwner(value: SequenceTag<std::vec::Vec<u8>>)
    -> SequenceTag<std::vec::Vec<u8>> {
    SequenceTag::<std::vec::Vec<u8>>::sequence_owner(value)
  }
\<close>

locale sequence_identity_transport =
  fixes seed :: 'ambient
begin
urust \<open>
  impl SequencePayload<Tag, [\<tau>\<open>'ambient\<close>]> {
    fn sequence_locale(self) -> Self { let spare = seed; self }
  }
\<close>
end

interpretation sequence_identity_nat: sequence_identity_transport \<open>1 :: nat\<close> .
interpretation sequence_identity_bool: sequence_identity_transport True .

end
