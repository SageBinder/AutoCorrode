(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Readable examples of Rust datatypes and types: urust_datatype, simple word enums,
   cast-target aliases, type aliases and raw pointers. The ML audits are in
   Parser_Datatype_ML_Tests. This theory and its audits do not import the chunk command. *)

theory Parser_Datatype_Examples
  imports
    Parser_Test_Fixtures
    Shallow_Micro_Rust.Simple_Word_Enum_uRust
begin

chapter\<open> Simple word enums \<close>

section\<open>Simple word enum path resolution\<close>

declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 0, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

urust_expr parser_message_kind_ping
  \<open> MessageKind::MK_Ping \<close>

urust_expr parser_message_kind_pong
  \<open> MessageKind::MK_Pong \<close>

urust_expr parser_message_kind_data
  \<open> MessageKind::MK_Data \<close>

lemma parser_message_kind_variant_paths:
  shows \<open>parser_message_kind_ping = literal MK_Ping\<close>
    and \<open>parser_message_kind_pong = literal MK_Pong\<close>
    and \<open>parser_message_kind_data = literal MK_Data\<close>
  by (simp_all only: parser_message_kind_ping_def parser_message_kind_pong_def
      parser_message_kind_data_def)

urust_expr parser_message_kind_to_u32
  (e)
  \<open> MessageKind::to_u32(e) \<close>

urust_expr parser_message_kind_try_from
  (w)
  \<open> MessageKind::try_from(w) \<close>

lemma parser_message_kind_function_paths:
  shows \<open>parser_message_kind_to_u32 e =
      funcall1 message_kind_to_u32 (literal e)\<close>
    and \<open>parser_message_kind_try_from w =
      funcall1 message_kind_try_from_u32 (literal w)\<close>
  by (simp_all only: parser_message_kind_to_u32_def parser_message_kind_try_from_def)

urust_expr parser_message_kind_unreduced_call
  \<open> MessageKind::to_u32(MessageKind::MK_Data) \<close>

lemma parser_message_kind_call_stays_unreduced:
  shows \<open>parser_message_kind_unreduced_call =
    funcall1 message_kind_to_u32 (literal MK_Data)\<close>
  by (simp only: parser_message_kind_unreduced_call_def)

urust_expr parser_message_kind_round_trip
  \<open> MessageKind::try_from(MessageKind::to_u32(MessageKind::MK_Data)) \<close>

lemma parser_message_kind_round_trip_value:
  shows \<open>parser_message_kind_round_trip = literal (Ok MK_Data)\<close>
  by (simp add: parser_message_kind_round_trip_def micro_rust_simps
      message_kind_to_u32_def message_kind_try_from_u32_def
      message_kind_to_u32_pure_then_try_from)

urust_expr parser_path_kind_first
  \<open> Outer::Inner::PathKind::PK_First \<close>

urust_expr parser_path_kind_to_u8
  (e)
  \<open> Outer::Inner::PathKind::to_u8(e) \<close>

urust_expr parser_path_kind_try_from
  (w)
  \<open> Outer::Inner::PathKind::try_from(w) \<close>

lemma parser_path_kind_paths:
  shows \<open>parser_path_kind_first = literal PK_First\<close>
    and \<open>parser_path_kind_to_u8 e =
      funcall1 path_kind_to_u8 (literal e)\<close>
    and \<open>parser_path_kind_try_from w =
      funcall1 path_kind_try_from_u8 (literal w)\<close>
  by (simp_all only: parser_path_kind_first_def parser_path_kind_to_u8_def
      parser_path_kind_try_from_def)

urust_expr parser_path_kind_nested_bare_match
  (x, y)
  \<open>
    match (x, y) {
      (PK_First, PK_Second) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr parser_convs_only_try_from
  (w)
  \<open> ConvsOnly::try_from(w) \<close>

lemma parser_convs_only_function_path:
  shows \<open>parser_convs_only_try_from w =
    funcall1 convs_only_try_from_u8 (literal w)\<close>
  by (simp only: parser_convs_only_try_from_def)

chapter\<open> Simple word enum clauses \<close>

section\<open> Clause registrations without the chunk command \<close>

text\<open>
This theory imports the single-item parser commands but not the opt-in chunk theory, as generated
register theories do. A \<open>simple_word_enum\<close> declaration with a \<open>urust_name: "Name"\<close> clause
registers its source paths for later parser commands.
\<close>

simple_word_enum (8) clause_kind urust_name: "ClauseKind" =
    CLK_First = 1
  | CLK_Second = 2

urust_fn clause_kind_first \<open> fn ClauseKindFirst() { let first = ClauseKind::CLK_First; () } \<close>

chapter\<open> Rust datatypes \<close>

section\<open> Rust datatype declarations \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2]]

urust_datatype [renames = ["renameSampleValue" \<rightarrow> "sample"]] \<open>
  struct RenamedPacket { renameSampleValue: u32, valid: bool }
\<close>

urust_datatype [backend = hol, renames = [
  "Ready" \<rightarrow> "ModelReady",
  "Data" \<rightarrow> "ModelData",
  "Empty" \<rightarrow> "ModelEmpty"
]] renamed_choice_hol \<open>
  enum RenamedChoice { Empty, Data(u32, bool), Ready { value: u32, active: bool } }
\<close>

urust_datatype [renames = ["fooBar" \<rightarrow> "distinct_field"]] \<open>
  struct RenameCollision { fooBar: u32, foo_bar: bool }
\<close>

lemma renamed_record_selector:
  \<open>sample (make_renamed_packet n b) = n\<close>
  by simp

lemma renamed_record_update:
  \<open>update_sample h (make_renamed_packet n b) = make_renamed_packet (h n) b\<close>
  by (rule renamed_packet_sample_update_explicit)

lemma renamed_record_lens:
  \<open>lens_view renamed_packet_sample_lens (make_renamed_packet n b) = n\<close>
  by (simp add: renamed_packet_sample_lens_view_update_modify)

urust_expr renamed_packet_construction \<open>
  RenamedPacket { renameSampleValue: 7u32, valid: true }
\<close>

lemma renamed_packet_construction_eq:
  \<open>renamed_packet_construction =
    funcall2 (lift_fun2 make_renamed_packet) (ascribeu32 7) true\<close>
  unfolding renamed_packet_construction_def by (rule refl)

urust_expr renamed_packet_pattern \<open>
  match (RenamedPacket { renameSampleValue: 7u32, valid: true }) {
    RenamedPacket { renameSampleValue, valid: _ } \<Rightarrow> renameSampleValue,
  }
\<close>

urust_expr renamed_packet_field \<open>
  (RenamedPacket { renameSampleValue: 7u32, valid: true }).renameSampleValue
\<close>

urust_expr renamed_unit_variant \<open> RenamedChoice::Empty \<close>

urust_expr renamed_tuple_variant \<open> RenamedChoice::Data(7u32, true) \<close>

urust_expr renamed_named_variant \<open> \<llangle>ModelReady 7 True\<rrangle> \<close>

urust_expr renamed_variant_pattern \<open>
  match RenamedChoice::Data(7u32, true) {
    RenamedChoice::Empty \<Rightarrow> 0u32,
    RenamedChoice::Data(n, _) \<Rightarrow> n,
    RenamedChoice::Ready { value, active: _ } \<Rightarrow> value,
  }
\<close>

lemma renamed_variants_eq:
  \<open>renamed_unit_variant = literal ModelEmpty\<close>
  \<open>renamed_tuple_variant = funcall2 (lift_fun2 ModelData) (ascribeu32 7) true\<close>
  \<open>renamed_named_variant = literal (ModelReady 7 True)\<close>
  unfolding renamed_unit_variant_def renamed_tuple_variant_def renamed_named_variant_def
  by (rule refl)+

locale renamed_locale
begin

urust_datatype [renames = ["value" \<rightarrow> "LocaleSample"],
  register_notation = false] \<open> struct LocaleRename { value: u32 } \<close>
thm locale_rename_LocaleSample_lens_valid locale_rename_LocaleSample_update_explicit

end

urust_datatype [register_notation = false] notation_packet \<open>
  struct NotationPacket { sampleValue: u32, HTTP2Code: bool }
\<close>

urust_datatype [register_notation = false] \<open>
  struct NotationEnvelope(NotationPacket);
\<close>

urust_expr notation_packet_construction \<open>
  NotationPacket { sampleValue: 7u32, HTTP2Code: true }
\<close>

urust_expr notation_packet_pattern \<open>
  match (NotationPacket { sampleValue: 7u32, HTTP2Code: true }) {
    NotationPacket { sampleValue, HTTP2Code: _ } \<Rightarrow> sampleValue,
  }
\<close>

urust_datatype \<open> struct NotationRestoredOn { restoredAlias: u32 } \<close>

urust_datatype parser_point \<open>
  struct ParserPoint {
    x: u32,
    history: \<tau>\<open>32 word list\<close>,
  }
\<close>

urust_datatype \<open>
  struct ParserTuple(u32, bool, \<tau>\<open>nat option\<close>,);
\<close>

urust_datatype \<open>
  struct ParserMarker;
\<close>

urust_datatype \<open>
  struct HTTPServerStatus;
\<close>

urust_datatype \<open>
  struct ParserPrimitives(
    u8, u16, u32, u64, usize, i32, i64, bool, (),
  );
\<close>

urust_datatype [backend = hol] \<open>
  enum ParserMessage {
    Empty,
    Data(u32, \<tau>\<open>nat option\<close>,),
    Named {
      code: u32,
      payload: \<tau>\<open>8 word list\<close>,
    },
  }
\<close>

urust_datatype wire_packet_hol \<open>
  struct WirePacket {
    sequence: u64,
    valid: bool,
  }
\<close>

urust_datatype \<open>
  struct ParserNumberBox {
    value: u32,
  }
\<close>

urust_datatype \<open>
  struct ParserFlagBox {
    value: bool,
  }
\<close>

urust_datatype [backend = hol] \<open>
  enum FirstSharedChoice {
    SharedIdle,
    SharedPayload(u32),
    SharedNamed {
      value: u32,
    },
  }
\<close>

urust_datatype [backend = hol] \<open>
  enum SecondSharedChoice {
    SharedIdle,
    SharedPayload(bool),
    SharedNamed {
      value: bool,
    },
  }
\<close>

urust_datatype \<open>
  struct ParserComposite(
    \<tau>\<open>parser_point\<close>,
    \<tau>\<open>parser_message list\<close>,
    \<tau>\<open>nat \<times> bool option\<close>,
  );
\<close>

urust_datatype \<open>
  struct ParserArity14(
    u32, u32, u32, u32, u32, u32, u32,
    u32, u32, u32, u32, u32, u32, u32,
  );
\<close>

urust_datatype \<open>
  /* leading /* nested */ block comment */
  struct ParserCommented(
    u32, // first field
    bool, /* second field */
  );
\<close>

urust_datatype \<open>
  struct HTTP2ServerState;
\<close>

urust_datatype \<open>
  struct XMLHttpRequest;
\<close>

urust_expr parser_point_value \<open>
  ParserPoint {
    x: 7u32,
    history: \<llangle>[] :: 32 word list\<rrangle>,
  }
\<close>

urust_expr parser_tuple_value \<open>
  ParserTuple(8u32, true, None)
\<close>

urust_expr parser_marker_value \<open>
  ParserMarker
\<close>

urust_expr parser_empty_value \<open>
  ParserMessage::Empty
\<close>

urust_expr parser_data_value \<open>
  ParserMessage::Data(9u32, None)
\<close>

urust_expr parser_tuple_pattern \<open>
  match ParserTuple(10u32, false, None) {
    ParserTuple(value, _, _) \<Rightarrow> value,
  }
\<close>

urust_expr parser_named_variant_pattern \<open>
  match \<llangle>parser_message.Named 11 []\<rrangle> {
    ParserMessage::Named { code, payload: _ } \<Rightarrow> code,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr parser_named_struct_pattern \<open>
  match (ParserPoint {
    x: 12u32,
    history: \<llangle>[] :: 32 word list\<rrangle>,
  }) {
    ParserPoint { x, history: _ } \<Rightarrow> x,
  }
\<close>

urust_expr parser_named_struct_rest_pattern \<open>
  match (ParserPoint {
    x: 24u32,
    history: \<llangle>[] :: 32 word list\<rrangle>,
  }) {
    ParserPoint { x, .. } \<Rightarrow> x,
  }
\<close>

urust_expr parser_named_variant_rest_pattern \<open>
  match \<llangle>undefined :: parser_message\<rrangle> {
    ParserMessage::Named { code, .. } \<Rightarrow> code,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr parser_named_struct_field (point) \<open>
  point.x + 0u32
\<close>

urust_expr parser_named_struct_assignment (point) \<open>
  point.x = 13u32
\<close>

urust_expr wire_packet_value \<open>
  WirePacket {
    sequence: 14u64,
    valid: true,
  }
\<close>

urust_expr wire_packet_field \<open>
  (WirePacket {
    sequence: 15u64,
    valid: false,
  }).sequence
\<close>

urust_expr parser_number_box_field \<open>
  (ParserNumberBox { value: 16u32 }).value
\<close>

urust_expr parser_flag_box_field \<open>
  (ParserFlagBox { value: true }).value
\<close>

urust_expr first_shared_unit \<open>
  FirstSharedChoice::SharedIdle
\<close>

urust_expr second_shared_unit \<open>
  SecondSharedChoice::SharedIdle
\<close>

urust_expr first_shared_payload \<open>
  FirstSharedChoice::SharedPayload(17u32)
\<close>

urust_expr second_shared_payload \<open>
  SecondSharedChoice::SharedPayload(false)
\<close>

urust_expr first_shared_pattern \<open>
  match FirstSharedChoice::SharedPayload(18u32) {
    FirstSharedChoice::SharedPayload(value) \<Rightarrow> value,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr second_shared_pattern \<open>
  match \<llangle>undefined :: second_shared_choice\<rrangle> {
    SecondSharedChoice::SharedNamed { value } \<Rightarrow> value,
    _ \<Rightarrow> false,
  }
\<close>

urust_expr parser_composite_value \<open>
  ParserComposite(
    ParserPoint {
      x: 19u32,
      history: \<llangle>[] :: 32 word list\<rrangle>,
    },
    \<llangle>[] :: parser_message list\<rrangle>,
    \<llangle>(20, None) :: nat \<times> bool option\<rrangle>
  )
\<close>

urust_expr parser_arity14_pattern \<open>
  match ParserArity14(
    1u32, 2u32, 3u32, 4u32, 5u32, 6u32, 7u32,
    8u32, 9u32, 10u32, 11u32, 12u32, 13u32, 14u32
  ) {
    ParserArity14(first, _, _, _, _, _, _, _, _, _, _, _, _, _) \<Rightarrow> first,
  }
\<close>

urust_expr parser_commented_value \<open>
  ParserCommented(21u32, true)
\<close>

urust_expr parser_marker_pattern \<open>
  match ParserMarker {
    ParserMarker \<Rightarrow> (),
  }
\<close>

urust_expr parser_empty_pattern \<open>
  match ParserMessage::Empty {
    ParserMessage::Empty \<Rightarrow> 22u32,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr_rejects \<open>
  ParserPoint {
    ignored_first: 7u32,
    ignored_second: \<llangle>[] :: 32 word list\<rrangle>,
  }
\<close> \<open>unknown field "ignored_first"\<close>

section\<open> Datatype selector naming \<close>

text\<open>
Enum payload rename keys use the source variant name. \<open>"Variant.field"\<close> chooses a named
payload selector, and \<open>"Variant.N"\<close> adds a selector for the 0-based tuple field \<open>N\<close>. A
plain variant key still renames only the constructor, so a payload key keeps the source variant
name after a constructor rename.
\<close>

urust_datatype [backend = hol, renames = [
  "Flagged" \<rightarrow> "SelectorNameFlagged",
  "Flagged.value" \<rightarrow> "selector_name_flag_value",
  "Paired.1" \<rightarrow> "selector_name_pair_flag"
]] \<open>
  enum SelectorNameHolChoice { Vacant, Paired(u32, bool), Flagged { value: u32, active: bool } }
\<close>

lemma selector_name_hol_payloads:
  \<open>selector_name_flag_value (SelectorNameFlagged n b) = n\<close>
  \<open>selector_name_hol_choice_flagged_active (SelectorNameFlagged n b) = b\<close>
  \<open>selector_name_pair_flag (Paired n b) = b\<close>
  \<open>un_Paired1 (Paired n b) = n\<close>
  by simp_all

urust_expr selector_name_hol_pattern \<open>
  match SelectorNameHolChoice::Paired(7u32, true) {
    SelectorNameHolChoice::Vacant \<Rightarrow> 0u32,
    SelectorNameHolChoice::Paired(n, _) \<Rightarrow> n,
    SelectorNameHolChoice::Flagged { value, active: _ } \<Rightarrow> value,
  }
\<close>

urust_datatype [renames = [
  "Marked.value" \<rightarrow> "selector_name_mark_value",
  "Packed.1" \<rightarrow> "selector_name_pack_flag"
]] \<open>
  enum SelectorNameCustomChoice { Unset, Packed(u32, bool), Marked { value: u32, active: bool } }
\<close>

lemma selector_name_custom_payloads:
  \<open>selector_name_mark_value (Marked n b) = n\<close>
  \<open>selector_name_custom_choice_marked_active (Marked n b) = b\<close>
  \<open>selector_name_pack_flag (Packed n b) = b\<close>
  by (simp_all only: selector_name_mark_value_simps selector_name_pack_flag_simps
    selector_name_custom_choice_marked_active_simps)

lemma selector_name_custom_payload_simp:
  \<open>selector_name_pack_flag (Packed n b) \<longleftrightarrow> b\<close>
  by simp

text\<open>
A positional key on the \<open>hol\<close> backend generates exactly the selector of the native datatype
declaration that names that field: the same constant type, definition and \<open>sel\<close> facts, which
are simplification rules. The other positional field keeps Ctr_Sugar's default selector.
\<close>

datatype selector_name_native_parity =
  NativeBoxed (selector_name_native_boxed: "32 word") | NativeSpared "64 word"

urust_datatype [backend = hol, renames = ["Boxed.0" \<rightarrow> "selector_name_parity_boxed"]] \<open>
  enum SelectorNameParity { Boxed(u32), Spared(u64) }
\<close>

lemma selector_name_positional_parity:
  \<open>selector_name_parity_boxed (Boxed n) = n\<close>
  \<open>un_Spared (Spared m) = m\<close>
  \<open>selector_name_native_boxed (NativeBoxed n) = n\<close>
  \<open>un_NativeSpared (NativeSpared m) = m\<close>
  by (simp_all only: selector_name_parity.sel selector_name_native_parity.sel)

lemma selector_name_positional_parity_simp:
  \<open>selector_name_parity_boxed (Boxed n) = n\<close>
  \<open>selector_name_native_boxed (NativeBoxed n) = n\<close>
  by simp_all

lemma selector_name_positional_parity_definition:
  \<open>selector_name_parity_boxed x = (case x of Boxed n \<Rightarrow> n | Spared _ \<Rightarrow> undefined)\<close>
  \<open>selector_name_native_boxed y =
    (case y of NativeBoxed n \<Rightarrow> n | NativeSpared _ \<Rightarrow> undefined)\<close>
  by (simp_all add: selector_name_parity.selector_name_parity_boxed_def
    selector_name_native_parity.selector_name_native_boxed_def)

chapter\<open> Rust type aliases in cast targets \<close>

section\<open> Primitive equivalence and grammar composition \<close>

declare [[urust_verbosity = 0]]

context
  fixes cast_alias_word :: "64 word"
begin

urust_expr cast_alias_u8
  \<open> cast_alias_word as U8Alias \<close>

urust_expr cast_alias_u8_primitive
  \<open> cast_alias_word as u8 \<close>

lemma cast_alias_u8_equal:
  \<open> cast_alias_u8 = cast_alias_u8_primitive \<close>
  unfolding cast_alias_u8_def cast_alias_u8_primitive_def
  by (rule refl)

urust_expr cast_alias_u16
  \<open> cast_alias_word as types::U16Alias \<close>

urust_expr cast_alias_u16_primitive
  \<open> cast_alias_word as u16 \<close>

lemma cast_alias_u16_equal:
  \<open> cast_alias_u16 = cast_alias_u16_primitive \<close>
  unfolding cast_alias_u16_def cast_alias_u16_primitive_def
  by (rule refl)

urust_expr cast_alias_u32
  \<open> cast_alias_word as U32Alias \<close>

urust_expr cast_alias_u32_primitive
  \<open> cast_alias_word as u32 \<close>

lemma cast_alias_u32_equal:
  \<open> cast_alias_u32 = cast_alias_u32_primitive \<close>
  unfolding cast_alias_u32_def cast_alias_u32_primitive_def
  by (rule refl)

urust_expr cast_alias_u64
  \<open> cast_alias_word as U64Alias \<close>

urust_expr cast_alias_u64_primitive
  \<open> cast_alias_word as u64 \<close>

lemma cast_alias_u64_equal:
  \<open> cast_alias_u64 = cast_alias_u64_primitive \<close>
  unfolding cast_alias_u64_def cast_alias_u64_primitive_def
  by (rule refl)

urust_expr cast_alias_usize
  \<open> cast_alias_word as UsizeAlias \<close>

urust_expr cast_alias_usize_primitive
  \<open> cast_alias_word as usize \<close>

lemma cast_alias_usize_equal:
  \<open> cast_alias_usize = cast_alias_usize_primitive \<close>
  unfolding cast_alias_usize_def cast_alias_usize_primitive_def
  by (rule refl)

urust_expr cast_alias_i32
  \<open> cast_alias_word as I32Alias \<close>

urust_expr cast_alias_i32_primitive
  \<open> cast_alias_word as i32 \<close>

lemma cast_alias_i32_equal:
  \<open> cast_alias_i32 = cast_alias_i32_primitive \<close>
  unfolding cast_alias_i32_def cast_alias_i32_primitive_def
  by (rule refl)

urust_expr cast_alias_i64
  \<open> cast_alias_word as I64Alias \<close>

urust_expr cast_alias_i64_primitive
  \<open> cast_alias_word as i64 \<close>

lemma cast_alias_i64_equal:
  \<open> cast_alias_i64 = cast_alias_i64_primitive \<close>
  unfolding cast_alias_i64_def cast_alias_i64_primitive_def
  by (rule refl)

urust_expr cast_alias_chain
  \<open> cast_alias_word as U64Alias as U8Alias as I32Alias \<close>

urust_expr cast_alias_chain_primitive
  \<open> cast_alias_word as u64 as u8 as i32 \<close>

lemma cast_alias_chain_equal:
  \<open> cast_alias_chain = cast_alias_chain_primitive \<close>
  unfolding cast_alias_chain_def cast_alias_chain_primitive_def
  by (rule refl)

urust_expr cast_alias_precedence
  \<open> cast_alias_word as U32Alias + 1_u32 \<close>

urust_expr cast_alias_precedence_primitive
  \<open> cast_alias_word as u32 + 1_u32 \<close>

lemma cast_alias_precedence_equal:
  \<open> cast_alias_precedence = cast_alias_precedence_primitive \<close>
  unfolding cast_alias_precedence_def cast_alias_precedence_primitive_def
  by (rule refl)

urust_expr cast_alias_no_struct
  \<open>
    if cast_alias_word as U32Alias ==
        cast_alias_word as U32Alias {
      cast_alias_word as types::U16Alias
    } else {
      cast_alias_word as types::U16Alias
    }
  \<close>

urust_expr cast_alias_no_struct_primitive
  \<open>
      if cast_alias_word as u32 ==
          cast_alias_word as u32 {
        cast_alias_word as u16
      } else {
        cast_alias_word as u16
      }

  \<close>

lemma cast_alias_no_struct_equal:
  \<open> cast_alias_no_struct = cast_alias_no_struct_primitive \<close>
  unfolding cast_alias_no_struct_def cast_alias_no_struct_primitive_def
  by (rule refl)

end

context
  fixes cast_alias_word :: "64 word"
    and cast_alias_length :: "64 word"
begin

urust_expr cast_alias_repeats
  \<open>
    ([cast_alias_word as types::U16Alias; (1 + 1) as usize],
     [const { cast_alias_word as U8Alias }; 3 as usize],
     [cast_alias_word as U32Alias; cast_alias_length],
     [const { cast_alias_word as types::U16Alias }; cast_alias_length as usize])
  \<close>

urust_expr cast_alias_repeats_primitive
  \<open>
    ([cast_alias_word as u16; (1 + 1) as usize],
     [const { cast_alias_word as u8 }; 3 as usize],
     [cast_alias_word as u32; cast_alias_length],
     [const { cast_alias_word as u16 }; cast_alias_length as usize])
  \<close>

lemma cast_alias_repeats_equal:
  \<open> cast_alias_repeats = cast_alias_repeats_primitive \<close>
  unfolding cast_alias_repeats_def cast_alias_repeats_primitive_def
  by (rule refl)

end

urust_expr_rejects \<open> [0u64 as U8Alias; 2 as UsizeAlias] \<close>
  \<open> array repeat length supports only \<close>

urust_expr_rejects \<open> [const { 0u64 as U8Alias }; 2 as UsizeAlias] \<close>
  \<open> array repeat length supports only \<close>

context
  fixes cast_alias_raw :: "('address, 'global) gref"
begin

urust_expr cast_alias_const_u8_pointer
  \<open> cast_alias_raw as ConstU8Pointer \<close>

urust_expr cast_alias_const_u8_pointer_primitive
  \<open> cast_alias_raw as *const u8 \<close>

lemma cast_alias_const_u8_pointer_equal:
  \<open> cast_alias_const_u8_pointer = cast_alias_const_u8_pointer_primitive \<close>
  unfolding cast_alias_const_u8_pointer_def cast_alias_const_u8_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_u16_pointer
  \<open> cast_alias_raw as ConstU16Pointer \<close>

urust_expr cast_alias_const_u16_pointer_primitive
  \<open> cast_alias_raw as *const u16 \<close>

lemma cast_alias_const_u16_pointer_equal:
  \<open> cast_alias_const_u16_pointer = cast_alias_const_u16_pointer_primitive \<close>
  unfolding cast_alias_const_u16_pointer_def cast_alias_const_u16_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_u32_pointer
  \<open> cast_alias_raw as ConstU32Pointer \<close>

urust_expr cast_alias_const_u32_pointer_primitive
  \<open> cast_alias_raw as *const u32 \<close>

lemma cast_alias_const_u32_pointer_equal:
  \<open> cast_alias_const_u32_pointer = cast_alias_const_u32_pointer_primitive \<close>
  unfolding cast_alias_const_u32_pointer_def cast_alias_const_u32_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_u64_pointer
  \<open> cast_alias_raw as ConstU64Pointer \<close>

urust_expr cast_alias_const_u64_pointer_primitive
  \<open> cast_alias_raw as *const u64 \<close>

lemma cast_alias_const_u64_pointer_equal:
  \<open> cast_alias_const_u64_pointer = cast_alias_const_u64_pointer_primitive \<close>
  unfolding cast_alias_const_u64_pointer_def cast_alias_const_u64_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_usize_pointer
  \<open> cast_alias_raw as ConstUsizePointer \<close>

urust_expr cast_alias_const_usize_pointer_primitive
  \<open> cast_alias_raw as *const usize \<close>

lemma cast_alias_const_usize_pointer_equal:
  \<open> cast_alias_const_usize_pointer = cast_alias_const_usize_pointer_primitive \<close>
  unfolding cast_alias_const_usize_pointer_def cast_alias_const_usize_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u8_pointer
  \<open> cast_alias_raw as MutU8Pointer \<close>

urust_expr cast_alias_mut_u8_pointer_primitive
  \<open> cast_alias_raw as *mut u8 \<close>

lemma cast_alias_mut_u8_pointer_equal:
  \<open> cast_alias_mut_u8_pointer = cast_alias_mut_u8_pointer_primitive \<close>
  unfolding cast_alias_mut_u8_pointer_def cast_alias_mut_u8_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u16_pointer
  \<open> cast_alias_raw as MutU16Pointer \<close>

urust_expr cast_alias_mut_u16_pointer_primitive
  \<open> cast_alias_raw as *mut u16 \<close>

lemma cast_alias_mut_u16_pointer_equal:
  \<open> cast_alias_mut_u16_pointer = cast_alias_mut_u16_pointer_primitive \<close>
  unfolding cast_alias_mut_u16_pointer_def cast_alias_mut_u16_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u32_pointer
  \<open> cast_alias_raw as MutU32Pointer \<close>

urust_expr cast_alias_mut_u32_pointer_primitive
  \<open> cast_alias_raw as *mut u32 \<close>

lemma cast_alias_mut_u32_pointer_equal:
  \<open> cast_alias_mut_u32_pointer = cast_alias_mut_u32_pointer_primitive \<close>
  unfolding cast_alias_mut_u32_pointer_def cast_alias_mut_u32_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u64_pointer
  \<open> cast_alias_raw as MutU64Pointer \<close>

urust_expr cast_alias_mut_u64_pointer_primitive
  \<open> cast_alias_raw as *mut u64 \<close>

lemma cast_alias_mut_u64_pointer_equal:
  \<open> cast_alias_mut_u64_pointer = cast_alias_mut_u64_pointer_primitive \<close>
  unfolding cast_alias_mut_u64_pointer_def cast_alias_mut_u64_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_usize_pointer
  \<open> cast_alias_raw as MutUsizePointer \<close>

urust_expr cast_alias_mut_usize_pointer_primitive
  \<open> cast_alias_raw as *mut usize \<close>

lemma cast_alias_mut_usize_pointer_equal:
  \<open> cast_alias_mut_usize_pointer = cast_alias_mut_usize_pointer_primitive \<close>
  unfolding cast_alias_mut_usize_pointer_def cast_alias_mut_usize_pointer_primitive_def
  by (rule refl)

end

section\<open> Direct declarations and locale scope \<close>

experiment
begin

urust_type_alias \<open> type ExperimentWidth = u32; \<close>

urust_expr cast_alias_direct_activation
  \<open> 0_u64 as ExperimentWidth \<close>

urust_expr cast_alias_direct_activation_primitive
  \<open> 0_u64 as u32 \<close>

lemma cast_alias_direct_activation_equal:
  \<open> cast_alias_direct_activation = cast_alias_direct_activation_primitive \<close>
  unfolding cast_alias_direct_activation_def cast_alias_direct_activation_primitive_def
  by (rule refl)

end

context cast_alias_scope
begin

urust_expr cast_alias_locale_use
  \<open> scope_word as LocaleWidth \<close>

urust_expr cast_alias_locale_use_primitive
  \<open> scope_word as u16 \<close>

lemma cast_alias_locale_use_equal:
  \<open> cast_alias_locale_use = cast_alias_locale_use_primitive \<close>
  unfolding cast_alias_locale_use_def cast_alias_locale_use_primitive_def
  by (rule refl)

end

section\<open> Conflicts and idempotence \<close>

experiment
begin

urust_type_alias \<open> type SharedWidth = u8; \<close>

urust_expr cast_alias_conflict_left_alone
  \<open> 0_u64 as SharedWidth \<close>

urust_expr cast_alias_conflict_left_alone_primitive
  \<open> 0_u64 as u8 \<close>

lemma cast_alias_conflict_left_alone_equal:
  \<open> cast_alias_conflict_left_alone = cast_alias_conflict_left_alone_primitive \<close>
  unfolding cast_alias_conflict_left_alone_def cast_alias_conflict_left_alone_primitive_def
  by (rule refl)

end

experiment
begin

urust_type_alias \<open> type SharedWidth = u16; \<close>

urust_expr cast_alias_conflict_right_alone
  \<open> 0_u64 as SharedWidth \<close>

urust_expr cast_alias_conflict_right_alone_primitive
  \<open> 0_u64 as u16 \<close>

lemma cast_alias_conflict_right_alone_equal:
  \<open> cast_alias_conflict_right_alone = cast_alias_conflict_right_alone_primitive \<close>
  unfolding cast_alias_conflict_right_alone_def cast_alias_conflict_right_alone_primitive_def
  by (rule refl)

end

urust_expr cast_alias_idempotent_registration
  \<open> 0_u64 as StableWidth \<close>

urust_expr cast_alias_idempotent_registration_primitive
  \<open> 0_u64 as u16 \<close>

lemma cast_alias_idempotent_registration_equal:
  \<open> cast_alias_idempotent_registration = cast_alias_idempotent_registration_primitive \<close>
  unfolding cast_alias_idempotent_registration_def cast_alias_idempotent_registration_primitive_def
  by (rule refl)

chapter\<open> Rust type aliases \<close>

declare [[urust_verbosity = 2]]

urust_type_alias \<open> type CommandWidth = u16; \<close>

urust_type_alias \<open> type CommandChain = CommandWidth; \<close>

urust_type_alias "command_types::QualifiedWidth" \<open> type QualifiedWidth = CommandChain; \<close>

urust_type_alias \<open> type CommandIdentity<T> = T; \<close>

urust_type_alias \<open> type CommandPair<T> = (T, T); \<close>

urust_type_alias \<open> type CommandPtr<T> = *const T; \<close>

urust_type_alias \<open> type CommandSigned = i32; \<close>

urust_type "CommandMapped" = \<open> nat list \<close>

urust_type_alias \<open> type CommandMappedAlias = CommandMapped; \<close>

urust_fn \<open>
  fn CommandNarrow(value: u32) -> command_types::QualifiedWidth {
    value as CommandIdentity<CommandChain>
  }
\<close>

urust_fn \<open>
  fn CommandPairs(left: CommandIdentity<u8>, right: CommandIdentity<u16>) -> (u8, u16) {
    (left, right)
  }
\<close>

urust_fn \<open>
  fn CommandPairIdentity(value: CommandPair<u8>) -> (u8, u8) {
    value
  }
\<close>

urust_fn \<open>
  fn CommandMappedIdentity(value: CommandMappedAlias) -> CommandMapped {
    value
  }
\<close>

urust_fn \<open>
  fn CommandPointerIdentity(value: CommandPtr<u8>) -> *const u8 {
    value
  }
\<close>

urust_expr command_generic_cast \<open> 5u32 as CommandIdentity<u16> \<close>

urust_expr command_generic_cast_expanded \<open> 5u32 as u16 \<close>

urust_expr command_signed_cast \<open> 5u64 as CommandSigned \<close>

urust_expr command_signed_cast_expanded \<open> 5u64 as i32 \<close>

lemma command_generic_cast_equal:
  \<open> command_generic_cast = command_generic_cast_expanded \<close>
  unfolding command_generic_cast_def command_generic_cast_expanded_def by (rule refl)

lemma command_signed_cast_equal:
  \<open> command_signed_cast = command_signed_cast_expanded \<close>
  unfolding command_signed_cast_def command_signed_cast_expanded_def by (rule refl)

section\<open> Command failures, dependency capture and recovery \<close>

urust_type "CommandOrdered<'value>" = \<open> 'value::linorder list \<close>

urust_type_alias \<open> type CommandSorted<T> = CommandOrdered<T>; \<close>

urust_type_alias \<open> type CommandIdentity<Value> = Value; \<close>

section\<open> Definition-time capture across dependency scopes \<close>

bundle capture_dependency_left
begin
urust_type "CaptureDependency" = \<open> 16 word \<close>
end

bundle capture_dependency_right
begin
urust_type "CaptureDependency" = \<open> 8 word \<close>
end

context includes capture_dependency_left
begin
urust_type_alias \<open> type CapturedDependency = CaptureDependency; \<close>
end

chapter\<open> Raw pointer types \<close>

urust_type_alias \<open> type DatatypeWidth = u16; \<close>

urust_type_alias \<open> type DatatypePtr<T> = *const T; \<close>

urust_type_alias \<open> type DatatypeMut<T> = *mut T; \<close>

urust_type_alias \<open> type DatatypePtrChain<T> = DatatypePtr<T>; \<close>

urust_datatype \<open>
  struct PointerPacket {
    pointer: DatatypePtr<u8>,
    count: DatatypeWidth,
  }
\<close>

urust_datatype \<open>
  struct PointerFields {
    left: DatatypePtrChain<u8>,
    right: DatatypeMut<u16>,
    nested: *const DatatypePtr<u32>,
  }
\<close>

urust_datatype \<open>
  struct PointerTuple(DatatypePtr<u8>, *mut u16, PointerPacket);
\<close>

urust_datatype [backend = hol] \<open>
  enum PointerChoice {
    Empty,
    Packet(PointerPacket),
    Pair { left: DatatypePtr<u16>, right: PointerTuple },
  }
\<close>

urust_datatype \<open>
  struct PointerOuter {
    packet: PointerPacket,
    tuple: PointerTuple,
    choice: PointerChoice,
  }
\<close>

urust_type_alias \<open> type DatatypePacketAlias = PointerPacket; \<close>

urust_datatype \<open>
  struct PointerWrapped(DatatypePacketAlias, *const u8);
\<close>

urust_datatype \<open> struct PlainPacket { count: u16, ready: bool } \<close>

urust_datatype \<open> struct PlainTuple(u32, bool); \<close>

urust_datatype \<open> enum PlainChoice { EmptyPlain, ValuePlain(u32) } \<close>

lemma pointer_packet_selector:
  \<open> pointer_packet_pointer (make_pointer_packet p n) = p \<close>
  by simp

lemma pointer_packet_lens:
  \<open>
    lens_view pointer_packet_pointer_packet_pointer_lens
      (make_pointer_packet p n) = p
  \<close>
  by (simp add: pointer_packet_pointer_packet_pointer_lens_view_update_modify)

lemma pointer_packet_update:
  \<open>
    update_pointer_packet_pointer h (make_pointer_packet p n) =
      make_pointer_packet (h p) n
  \<close>
  by (simp add: datatype_record_update)

urust_fn \<open>
  fn BuildPointerPacket(pointer: DatatypePtr<u8>, count: DatatypeWidth) -> PointerPacket {
    PointerPacket { pointer: pointer, count: count }
  }
\<close>

urust_fn \<open>
  fn ReadPointerPacket(packet: DatatypePacketAlias) -> DatatypePtr<u8> {
    packet.pointer
  }
\<close>

urust_fn \<open>
  fn BuildPointerTuple(pointer: *const u8, mutable: *mut u16, packet: PointerPacket) -> PointerTuple {
    PointerTuple(pointer, mutable, packet)
  }
\<close>

urust_fn \<open>
  fn BuildPointerChoice(packet: PointerPacket) -> PointerChoice {
    PointerChoice::Packet(packet)
  }
\<close>

urust_fn \<open>
  fn MatchPointerChoice(choice: PointerChoice) -> *const u8 {
    match choice {
      PointerChoice::Empty => \<llangle>undefined\<rrangle>,
      PointerChoice::Packet(packet) => packet.pointer,
      PointerChoice::Pair { left: _, right: _ } => \<llangle>undefined\<rrangle>,
    }
  }
\<close>

section\<open> Signature constraints and independent instantiation \<close>

urust_fn \<open>
  fn PointerBodyConstraint(value: DatatypePtr<u8>) -> DatatypePtr<u8> {
    \<llangle>value :: (nat, bool, 8 word) Global_Store.ref\<rrangle>
  }
\<close>

urust_fn \<open>
  fn PointerResultConstraint(value: DatatypePtr<u8>)
      -> \<tau>\<open> (int, nat, 8 word) Global_Store.ref \<close> {
    value
  }
\<close>

urust_expr pointer_independent_calls \<open>
  (
    CommandPointerIdentity(\<llangle>undefined :: (nat, bool, 8 word) Global_Store.ref\<rrangle>),
    CommandPointerIdentity(\<llangle>undefined :: (int, nat, 8 word) Global_Store.ref\<rrangle>)
  )
\<close>

end
