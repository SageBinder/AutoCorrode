(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Erasure_Field_View_Examples
  imports
    Parser_Field_View_Examples
    "Micro_Rust_Parser_Impl.Parser_Impl_Chunk"
begin

section\<open> Source parameters with selected list fields \<close>

datatype 'capacity composition_chain = CompositionChain

urust_type "composition::Buffer<'element, const 'capacity>" =
  \<open> ('element, 'capacity::len) vector \<close>
urust_type [representation = "list", erase = \<open> 'capacity \<close>]
  "composition::Buffer<'element, const 'capacity>" = \<open> 'element list \<close>
urust_type "composition::Chain<const 'block>" = \<open> 'block composition_chain \<close>
urust_type [representation = "list", erase = \<open> 'block \<close>]
  "composition::Chain<const 'block>" = \<open> 64 word list \<close>

urust_type_alias \<open>
  type CompositionBlocks<T, const N: usize> = composition::Buffer<T, N>;
\<close>

urust \<open>
  use composition::{Buffer as CompositionBuffer, Chain as CompositionChain};
  \<omega>\<open>erase_parameters = ["BLOCK"], pp_test, pretty\<close>
  struct CompositionBlock<const BLOCK: usize> { value: u64 }
  \<omega>\<open>erase_parameters = ["LIMIT", "BLOCK"], pp_test, pretty,
    field_representations = ["blocks" \<rightarrow> \<open>list\<close>,
      "available" \<rightarrow> \<open>list\<close>]\<close>
  struct CompositionStorage<const BLOCK: usize, const LIMIT: usize> {
    blocks: CompositionBuffer<CompositionBlock<BLOCK>, LIMIT>,
    available: CompositionChain<BLOCK>,
  }
  impl<const BLOCK: usize, const LIMIT: usize> CompositionStorage<BLOCK, LIMIT> {
    fn identity(self) -> Self { self }
    fn fetch_blocks(self) -> [CompositionBlock<BLOCK>] { self.blocks }
  }
  fn CompositionSelectedZero(value: CompositionStorage<0, 0>) -> CompositionStorage<0, 0> {
    CompositionStorage::<0, 0>::identity(value)
  }
  fn CompositionSelectedSeven(value: CompositionStorage<7, 4>) -> CompositionStorage<7, 4> {
    CompositionStorage::<7, 4>::identity(value)
  }
  fn CompositionSelectedTwin(value: CompositionStorage<0, 0>) -> CompositionStorage<0, 0> {
    \<epsilon>\<open>composition_storage_identity\<close>(value)
  }
\<close>

lemma composition_generic_impl_twins:
  shows \<open> composition_selected_zero = composition_selected_seven \<close>
    and \<open> composition_selected_zero = composition_selected_twin \<close>
  unfolding composition_selected_zero_def composition_selected_seven_def
    composition_selected_twin_def
  by (rule refl)+

urust_datatype [erase_parameters = ["N"], pp_test,
  field_representations = ["blocks" \<rightarrow> \<open>list\<close>]] \<open>
  struct CompositionAliasStorage<const N: usize> {
    blocks: CompositionBlocks<CompositionBlock<N>, N>,
  }
\<close>

urust_type_alias \<open>
  type CompositionStorageAlias<const N: usize> = CompositionStorage<N, 0>;
\<close>
urust_type_alias \<open>
  type CompositionStorageZero = CompositionStorageAlias<0>;
\<close>

urust_expr composition_construct (blocks, available) \<open>
  CompositionStorage::<0, 0> { blocks: blocks, available: available }
\<close>
urust_expr composition_construct_other (blocks, available) \<open>
  CompositionStorage::<7, 4> { blocks: blocks, available: available }
\<close>
lemma composition_constructor_twins:
  \<open> composition_construct = composition_construct_other \<close>
  unfolding composition_construct_def composition_construct_other_def by (rule refl)

urust_fn \<open>
  fn CompositionPattern(value: CompositionStorage<0, 0>) -> [CompositionBlock<0>] {
    match value {
      CompositionStorage::<0, 0> { blocks, available } => blocks
    }
  }
\<close>
urust_fn \<open>
  fn CompositionSelector(value: CompositionStorageZero) -> [CompositionBlock<0>] {
    value.blocks
  }
\<close>
urust_fn \<open>
  fn CompositionSelectorEscape(value: \<tau>\<open>composition_storage\<close>)
      -> [CompositionBlock<0>] {
    \<llangle>focus_lens_const composition_storage_composition_storage_blocks_lens value\<rrangle>
  }
\<close>
lemma composition_selector_twin:
  \<open> composition_selector = composition_selector_escape \<close>
  unfolding composition_selector_def composition_selector_escape_def
  by (simp add: micro_rust_simps)

urust_expr composition_pattern_value (packet) \<open>
  match packet { CompositionStorage::<0,0> { blocks, .. } => blocks }
\<close>
lemma composition_pattern_correct:
  \<open> composition_pattern_value packet = literal (composition_storage_blocks packet) \<close>
  by (cases packet) (simp add: composition_pattern_value_def micro_rust_simps)

urust \<open>
  impl CompositionStorage<0, 0> {
    \<omega>\<open>name = "composition_storage_zero_kind"\<close>
    fn kind(self) -> u8 { 0_u8 }
  }
  impl CompositionStorage<7, 4> {
    \<omega>\<open>name = "composition_storage_seven_kind"\<close>
    fn kind(self) -> u8 { 7_u8 }
  }
  fn CompositionZeroKind(value: CompositionStorageZero) -> u8 {
    CompositionStorageZero::kind(value)
  }
  fn CompositionSevenKind(value: CompositionStorage<7, 4>) -> u8 {
    CompositionStorage::<7, 4>::kind(value)
  }
  fn CompositionZeroKindTwin(value: CompositionStorageZero) -> u8 {
    \<epsilon>\<open>composition_storage_zero_kind\<close>(value)
  }
  fn CompositionSevenKindTwin(value: CompositionStorage<7, 4>) -> u8 {
    \<epsilon>\<open>composition_storage_seven_kind\<close>(value)
  }
\<close>

lemma composition_concrete_impl_twins:
  shows \<open> composition_zero_kind = composition_zero_kind_twin \<close>
    and \<open> composition_seven_kind = composition_seven_kind_twin \<close>
  unfolding composition_zero_kind_def composition_zero_kind_twin_def
    composition_seven_kind_def composition_seven_kind_twin_def
  by (rule refl)+

section\<open> Retained source witnesses and shared backend roles \<close>

text\<open>
The imported transport example binds its backend roles to concrete types.
This local context exercises fresh shared roles alongside the retained source witness.
\<close>
context notes [[urust_model_parameters = \<open>
  ["address" \<rightarrow> \<open>_\<close>, "global" \<rightarrow> \<open>_\<close>]
\<close>]]
begin

urust_datatype [erase_parameters = ["N"], pp_test,
  field_representations = ["blocks" \<rightarrow> \<open> list \<close>]] \<open>
  struct CompositionLinked<T, const N: usize> {
    blocks: composition::Buffer<*mut T, N>,
    head: *mut T,
  }
\<close>

urust_fn \<open>
  fn CompositionLinkedBuild<T, const N: usize>(blocks: [*mut T], head: *mut T)
      -> CompositionLinked<T, N> {
    CompositionLinked::<T, N> { blocks: blocks, head: head }
  }
\<close>
urust_fn \<open>
  fn CompositionLinkedBuildEscape<T, const N: usize>(blocks: [*mut T], head: *mut T)
      -> CompositionLinked<T, N> {
    \<epsilon>\<open>lift_fun2 make_composition_linked\<close>(blocks, head)
  }
\<close>
lemma composition_linked_constructor_twin:
  \<open> composition_linked_build = composition_linked_build_escape \<close>
  unfolding composition_linked_build_def composition_linked_build_escape_def
  by (rule refl)

end

locale composition_field_transport =
  fixes seed :: nat
begin

urust_datatype [erase_parameters = ["N"], pp_test,
  field_representations = ["blocks" \<rightarrow> \<open>list\<close>]] \<open>
  struct CompositionTransport<const N: usize> {
    blocks: CompositionBlocks<CompositionBlock<N>, N>,
  }
\<close>
urust_fn \<open>
  fn CompositionTransportIdentity<const N: usize>(value: CompositionTransport<N>)
      -> CompositionTransport<N> { let spare = seed; value }
\<close>

end

interpretation composition_field_one: composition_field_transport 1 .
interpretation composition_field_two: composition_field_transport 2 .

end
