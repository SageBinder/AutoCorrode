(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Field_View_Examples
  imports Parser_Test_Fixtures Micro_Rust_Parser_Impl.Parser_Impl_Chunk Misc.Vector
begin

chapter\<open> Scoped nominal field representations \<close>

text\<open>
The source buffer keeps its bounded-vector default and the source chain keeps its wrapper.
Explicit field policies select declared alternatives for the outer nominal occurrence.
Literal capacities make these examples independent of datatype parameter erasure.
\<close>

datatype 'block field_view_chain = Field_View_Chain \<open>64 word list\<close>

urust_type "view_demo::Buffer<'element, const 'capacity>" =
  \<open> ('element, 'capacity::len) vector \<close>
urust_type "view_demo::Chain<const 'block_size>" = \<open> 'block_size field_view_chain \<close>
urust_type [representation = "list", erase = \<open> 'capacity \<close>]
  "view_demo::Buffer<'element, const 'capacity>" = \<open> 'element list \<close>
urust_type [representation = "optional", erase = \<open> 'capacity \<close>]
  "view_demo::Buffer<'element, const 'capacity>" = \<open> 'element option \<close>
urust_type [representation = "list", erase = \<open> 'block_size \<close>]
  "view_demo::Chain<const 'block_size>" = \<open> 64 word list \<close>

urust_type_alias \<open>
  type FieldViewAlias<T, const N: usize> = view_demo::Buffer<T, N>;
\<close>
urust_type_alias \<open>
  type FieldViewAliasAgain<T, const N: usize> = FieldViewAlias<T, N>;
\<close>
urust_type_alias \<open> type FieldViewForward<T> = T; \<close>

urust_datatype [
  field_representations = [
    "blocks" \<rightarrow> \<open> list \<close>,
    "available" \<rightarrow> \<open> list \<close>,
    "nested" \<rightarrow> \<open> list \<close>,
    "optional" \<rightarrow> \<open> optional \<close>,
    "displayValue" \<rightarrow> \<open> list \<close>
  ],
  hol_names = [
    "blocks" \<rightarrow> \<open>view_blocks\<close>,
    "available" \<rightarrow> \<open>view_available\<close>,
    "wrapped" \<rightarrow> \<open>view_wrapped\<close>,
    "nested" \<rightarrow> \<open>view_nested\<close>,
    "optional" \<rightarrow> \<open>view_optional\<close>,
    "ordinary" \<rightarrow> \<open>view_ordinary\<close>,
    "displayValue" \<rightarrow> \<open>view_display\<close>
  ]
] \<open>
  struct FieldViewPacket {
    blocks: FieldViewAliasAgain<u8, 4>,
    available: view_demo::Chain<8>,
    wrapped: view_demo::Chain<8>,
    nested: view_demo::Buffer<view_demo::Buffer<u8, 3>, 4>,
    optional: view_demo::Buffer<bool, 4>,
    ordinary: view_demo::Buffer<u8, 4>,
    displayValue: view_demo::Buffer<u16, 4>,
  }
\<close>

urust_expr field_view_construct (bytes, addresses, chain, nested, flag, ordinary, display) \<open>
  FieldViewPacket {
    blocks: bytes, available: addresses, wrapped: chain,
    nested: nested, optional: flag, ordinary: ordinary, displayValue: display,
  }
\<close>

lemma field_view_constructor:
  \<open> field_view_construct bytes addresses chain nested flag ordinary display =
    literal (make_field_view_packet bytes addresses chain nested flag ordinary display) \<close>
  by (simp only: field_view_construct_def micro_rust_simps)

urust_expr field_view_pattern (packet) \<open>
  match packet { FieldViewPacket { blocks, .. } \<Rightarrow> blocks }
\<close>
urust_fn field_view_select \<open>
  fn FieldViewSelect(packet: FieldViewPacket) -> [u8] { packet.blocks }
\<close>
urust_fn field_view_select_escape \<open>
  fn FieldViewSelectEscape(packet: \<tau>\<open>field_view_packet\<close>) -> [u8] {
    \<llangle>focus_lens_const field_view_packet_view_blocks_lens packet\<rrangle>
  }
\<close>

lemma field_view_selector:
  \<open> view_blocks (make_field_view_packet bytes addresses chain nested flag ordinary display) =
    bytes \<close>
  by simp

lemma field_view_function:
  \<open> field_view_select = field_view_select_escape \<close>
  unfolding field_view_select_def field_view_select_escape_def
  by (simp add: micro_rust_simps)

lemma field_view_pattern_correct:
  \<open> field_view_pattern packet = literal (view_blocks packet) \<close>
  by (cases packet) (simp add: field_view_pattern_def micro_rust_simps)

urust \<open>
  use view_demo::Buffer as SelectedBuffer;
  \<omega>\<open>field_representations = ["payload" \<rightarrow> \<open> list \<close>]\<close>
  struct FieldViewImported { payload: SelectedBuffer<u8, 5> }
\<close>

urust_type [implicit = \<open> address = 'addr, global = 'store \<close>]
  "view_demo::ReferenceBuffer<'element, const 'capacity>" =
    \<open> ('addr, 'store, ('element, 'capacity::len) vector) Global_Store.ref \<close>
urust_type [representation = "list", implicit = \<open> address = 'addr, global = 'store \<close>,
  erase = \<open> 'capacity \<close>]
  "view_demo::ReferenceBuffer<'element, const 'capacity>" =
    \<open> ('addr, 'store, 'element) Global_Store.ref list \<close>
urust_datatype [
  field_representations = ["selected" \<rightarrow> \<open> list \<close>]
] \<open>
  struct FieldViewSharing<T> {
    selected: view_demo::ReferenceBuffer<T, 3>,
    direct: *mut T,
    nested: view_demo::Buffer<*mut T, 4>,
  }
\<close>

urust_datatype [field_representations = ["selected" \<rightarrow> \<open> list \<close>]] \<open>
  struct FieldViewAliasSharing<T> {
    selected: FieldViewForward<view_demo::Buffer<*mut T, 0>>,
    direct: *mut T,
  }
\<close>

urust_datatype [
  field_representations = ["payload" \<rightarrow> \<open> list \<close>]
] \<open>
  struct FieldViewCapacity<T, const N: usize> { payload: FieldViewAlias<T, N> }
\<close>

locale field_view_local_nat
begin
urust_type "FieldViewLocal" = \<open> nat \<close>
urust_type [representation = "list"] "FieldViewLocal" = \<open> nat list \<close>
urust_datatype [field_representations = ["localValue" \<rightarrow> \<open> list \<close>]] \<open>
  struct FieldViewLocalHolder { localValue: FieldViewLocal }
\<close>
end

locale field_view_local_bool
begin
urust_type "FieldViewLocal" = \<open> bool \<close>
urust_type [representation = "list"] "FieldViewLocal" = \<open> bool list \<close>
urust_datatype [field_representations = ["localValue" \<rightarrow> \<open> list \<close>]] \<open>
  struct FieldViewLocalHolder { localValue: FieldViewLocal }
\<close>
end

locale field_view_transport =
  fixes pointer :: \<open>('address, 'global, 8 word) Global_Store.ref\<close>
begin

declare [[urust_model_parameters = \<open>
  ["address" \<rightarrow> \<open>'address\<close>, "global" \<rightarrow> \<open>'global\<close>]
\<close>]]
urust_type_alias \<open>
  type FieldViewTransportAlias<T, const N: usize> = view_demo::ReferenceBuffer<T, N>;
\<close>
urust_type [representation = "transport",
  implicit = \<open> address = 'addr, global = 'store \<close>, erase = \<open> 'capacity \<close>]
  "view_demo::ReferenceBuffer<'element, const 'capacity>" =
    \<open> ('addr, 'store, 'element) Global_Store.ref list \<close>

end

interpretation field_view_transport_instance: field_view_transport
  \<open>undefined :: (nat, bool, 8 word) Global_Store.ref\<close> .

ML_val\<open>
local
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  fun parsed text = URust_Parser.parse_type_source ctxt
    (Parser_Lex_Util.positioned_content_source text Position.none)
  val ordinary = M.resolve ctxt (parsed "FieldViewTransportAlias<u8,3>")
  val selected = M.resolve_declaration_roles_with_representations ctxt [] []
    [(SOME ("transport", Position.none), parsed "FieldViewTransportAlias<u8,0>")]
  val policy = the_single (#representations selected) |> the
  val view = the (M.lookup_representation ctxt "view_demo::ReferenceBuffer" "transport")
  val _ =
    if ordinary = \<^typ>\<open>(nat, bool, (8 word, 3) vector) Global_Store.ref\<close> andalso
      #types selected = [\<^typ>\<open>(nat, bool, 8 word) Global_Store.ref list\<close>] andalso
      null (#backend_parameters selected) andalso
      #source_head policy = "view_demo::ReferenceBuffer" andalso
      #declaration_identity policy = M.entry_identity view
    then () else error "interpreted field representation lost its checked context or source identity"
in end
\<close>

urust_datatype [field_representations = ["linked" \<rightarrow> \<open> transport \<close>]] \<open>
  struct FieldViewTransport {
    linked: FieldViewTransportAlias<u8, 0>,
    direct: *mut u8,
  }
\<close>

end
