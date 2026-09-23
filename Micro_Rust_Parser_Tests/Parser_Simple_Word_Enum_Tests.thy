(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Simple_Word_Enum_Tests
  imports
    Shallow_Micro_Rust.Simple_Word_Enum_uRust
    Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

declare [[urust_conformance = false]]
declare [[urust_verbosity = 0]]

section\<open>Simple word enum path resolution\<close>

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

urust_expr parser_convs_only_try_from
  (w)
  \<open> ConvsOnly::try_from(w) \<close>

lemma parser_convs_only_function_path:
  shows \<open>parser_convs_only_try_from w =
    funcall1 convs_only_try_from_u8 (literal w)\<close>
  by (simp only: parser_convs_only_try_from_def)

end
