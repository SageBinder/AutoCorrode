(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Combined showcase of the uRust parser commands, grammar and semantics. *)

theory Parser_Showcase_Examples
  imports
    Micro_Rust_Std_Lib.StdLib_Logging
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
    Misc.Simple_Word_Enums
    Shallow_Separation_Logic.Separation_Algebra
begin

section\<open> Showcase \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

text\<open>
These examples intentionally combine parser, lowering, matching, iterator, and
declaration features.
\<close>

subsection\<open> Rust datatype items \<close>

text\<open>
Named Rust field types are context-local declarations. Primitive spellings use the same registry,
and generated datatypes register their Rust names automatically for later declarations.
\<close>

urust_type "PacketId" = \<open>64 word\<close>

urust_type "Maybe<'value>" = \<open>'value option\<close>

urust_datatype [pretty, verbosity = 1] datatype_packet \<open>
  struct DatatypePacket {
    identifier: PacketId,
    tag: u32,
    state: Maybe<bool>,
    pair: (u8, bool),
    bytes: \<tau>\<open>8 word list\<close>,
  }
\<close>

urust_datatype \<open>
  enum DatatypeEvent {
    Idle,
    Packet(\<tau>\<open>datatype_packet\<close>),
  }
\<close>

text\<open>
Field-lens aliases are enabled by default. Disabling \<open>register_notation\<close> retains the
generated lenses, proofs, constructor paths, and type mapping. A manual declaration can install
selected aliases later. The scoped setting is \<open>urust_register_notation\<close>; inline options
override it for one declaration only.
\<close>

urust_datatype [register_notation = false, pp_test, pretty, verbosity = 1] \<open>
  struct DatatypeSample { sampleValue: u32 }
\<close>

thm datatype_sample_datatype_sample_sample_value_lens_valid

urust_notation (field) datatype_sample_datatype_sample_sample_value_lens ("sampleValue")

urust_expr showoff_manual_datatype_field \<open>
  (DatatypeSample { sampleValue: 9u32 }).sampleValue
\<close>

text\<open>
Declaration-local \<open>hol_names\<close> chooses HOL selector or enum constructor basenames.
Both sides are quoted; Rust paths and field spellings continue to come from the source.
The lens name follows the chosen selector.
\<close>

urust_datatype [hol_names = ["sampleValue" \<rightarrow> \<open>sample\<close>], pp_test, pretty] \<open>
  struct RenamedSample { sampleValue: u32 }
\<close>

thm renamed_sample_sample_lens_valid

urust_datatype [hol_names = ["Ready" \<rightarrow> \<open>ModelReady\<close>]] \<open>
  enum RenamedState { Ready(u32), Empty }
\<close>

urust_expr showoff_renamed_datatype \<open>
  match RenamedState::Ready((RenamedSample { sampleValue: 9u32 }).sampleValue) {
    RenamedState::Ready(value) \<Rightarrow> value,
    RenamedState::Empty \<Rightarrow> 0u32,
  }
\<close>

subsection\<open> Generic datatype declarations \<close>

text\<open>
Type and const parameters are inferred together, including unused parameters.
An explicit unsigned representation with no payload selects
the word backend; omitted discriminants increment the preceding value.
\<close>

urust_datatype \<open>
  struct FixedBuffer<T, const N: usize> { values: [T; N] }
\<close>

\<comment>\<open>RUST-CHANGE: this proof-source mirror explicitly omits a PhantomData field and its
pure initializer and pattern slot, while retaining the original generic parameter. Automatic
marker handling is deferred; nontrivial initializer effects need explicit source adaptation.\<close>

urust_datatype \<open>
  struct TypedAddress<T> { address: u64 }
\<close>

urust_datatype \<open>
  enum GenericEvent<T, P> { Waiting, Arrived { value: T } }
\<close>

urust_datatype \<open>
  #[repr(u8)]
  enum WireState<T> { WireIdle, WireReady = 7, WireBusy }
\<close>

urust_expr showoff_unused_parameter_construction \<open>
  TypedAddress::<u8> { address: 11u64 }
\<close>

urust_expr showoff_generic_match \<open>
  match (GenericEvent::<u32, u8>::Arrived { value: 9u32 }) {
    GenericEvent::Waiting => 0u32,
    GenericEvent::Arrived { value } => value,
  }
\<close>

urust_fn \<open>
  fn showoff_const_signature(buffer: FixedBuffer<u8, 4>) -> FixedBuffer<u8, 4> { buffer }
\<close>

urust_type_alias \<open>
  type FixedBufferAlias<T, const N: usize> = FixedBuffer<T, N>;
\<close>

text\<open>A typed receiver can use a generic alias while channel options retain the full computation type.\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  showoff_const_receiver \<open>
  fn FixedBufferReceiver(self: FixedBufferAlias<u8, 4>) -> FixedBuffer<u8, 4> { self }
\<close>

lemma showoff_const_receiver_equivalent:
  \<open>showoff_const_receiver = showoff_const_signature\<close>
  unfolding showoff_const_receiver_def showoff_const_signature_def by (rule refl)

urust_expr showoff_word_conversion \<open>
  WireState::to_u8(WireState::<u8>::WireBusy)
\<close>

subsection\<open> Mapped handles with source-only parameters \<close>

text\<open>
The payload supplies a HOL witness. The policy tag and capacity remain source arguments while
the address and global roles come from the signature or field batch. No tag mapping or length
type is needed for the opaque policy and zero capacity. Explicit source arguments let a generic
call forward this information without adding a TYPE or value argument.
\<close>

urust_type [implicit = \<open> address = 'addr, global = 'store \<close>,
  erase = \<open> 'policy, 'capacity \<close>]
  "ShowcaseHandle<'value, 'policy, const 'capacity>" =
    \<open> ('addr, 'store, 'value) Global_Store.ref \<close>
urust_type_alias \<open>
  type ShowcaseHandleAlias<Value, Policy, const N: usize> = ShowcaseHandle<Value, Policy, N>;
\<close>
urust_datatype \<open>
  struct ShowcaseHolder {
    handle: ShowcaseHandleAlias<u8, foreign::Policy<0>, 0>,
    next: *const u8,
  }
\<close>

urust_fn \<open>
  fn ShowoffHandleIdentity<Value, Policy, const N: usize>(handle: ShowcaseHandleAlias<Value, Policy, N>)
      -> ShowcaseHandle<Value, Policy, N> { handle }
\<close>
urust_fn \<open>
  fn ShowoffHandleEscape(handle: \<tau>\<open> ('a, 'g, 'v) Global_Store.ref \<close>)
      -> \<tau>\<open> ('a, 'g, 'v) Global_Store.ref \<close> { handle }
\<close>
urust_fn \<open>
  fn ShowoffHandleCall(handle: ShowcaseHandle<u8, foreign::Policy<0>, 0>)
      -> ShowcaseHandle<u8, foreign::Policy<0>, 0> {
    ShowoffHandleIdentity::<u8, foreign::Policy<0>, 0>(handle)
  }
\<close>
urust_fn \<open>
  fn ShowoffHandleCallEscape(handle: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close>)
      -> \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close> {
    ShowoffHandleEscape(handle)
  }
\<close>

lemma showoff_handle_twins:
  shows \<open> showoff_handle_identity = showoff_handle_escape \<close>
    and \<open> showoff_handle_call = showoff_handle_call_escape \<close>
  unfolding showoff_handle_identity_def showoff_handle_escape_def
    showoff_handle_call_def showoff_handle_call_escape_def by (rule refl)+

text\<open>
The model shares a HOL representation across different policies; source-sensitive selection
still distinguishes their identities. A HOL-only receiver cannot infer an erased policy, so
use an explicit associated path when selecting an identity-dependent impl member.
\<close>

ML_val\<open>
  let
    val ctxt = \<^context>
    fun principal name =
      let
        val typ = Sign.the_const_type \<^theory> (Proof_Context.intern_const ctxt name)
        val variables = Term.add_tvarsT typ [] |> rev
        val substitutions = variables |> map_index (fn (index, variable as (_, sort)) =>
          (variable, TVar (("showcase_type", index), sort))) |> TVars.make
      in Term_Subst.instantiateT substitutions typ end
    val _ = List.app (fn (native, escaped) =>
      if principal native = principal escaped then ()
      else error ("Showcase combined principal type/sorts/sharing/channels differ: " ^ native))
      [("showoff_handle_identity", "showoff_handle_escape"),
       ("showoff_handle_call", "showoff_handle_call_escape")]
  in () end
\<close>

subsection\<open> Rust-shaped function items \<close>

text\<open>
\<open>urust_fn\<close> parses a complete Rust-shaped function item. Its parameter and explicit
result types resolve through the shared Rust-to-HOL registry and control elaboration.
Omitting the HOL binding infers it from the Rust name.
\<close>

urust_fn [application_def]
  \<open>
    fn PacketLength(packet: u64) -> u64 {
      packet + 1_u64
    }
  \<close>

text\<open>HOL channel options supplement the Rust value types with the computation's state and effects.\<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>,
   application_def]
  \<open>
    fn StablePacketLength(packet: u64) -> u64 {
      PacketLength(packet)
    }
  \<close>

thm packet_length_def

text\<open>
Scoped channel defaults state the computation types once for a block. A function that omits a
channel inherits its default, and an inline option overrides one channel.
\<close>

context
  notes [[urust_state = \<open>'s::cancellative_sepalg\<close>, urust_abort = \<open>bool\<close>,
          urust_input = \<open>nat prompt\<close>, urust_output = \<open>unit prompt_output\<close>]]
begin

urust_fn [application_def]
  \<open> fn ScopedPacketLength(packet: u64) -> u64 { PacketLength(packet) } \<close>

urust_fn [abort = \<open>unit\<close>, application_def]
  \<open> fn ScopedUnitAbortPacketLength(packet: u64) -> u64 { PacketLength(packet) } \<close>

end

lemma scoped_packet_length_equivalent:
  \<open>scoped_packet_length packet = stable_packet_length packet\<close>
  unfolding scoped_packet_length_def stable_packet_length_def by (rule refl)

text\<open>
A declared \<open>:: TYPE\<close> states the complete HOL type instead. The Rust signature's types are then
ignored, so they may use Rust types without a mapping, such as the shared reference here.
\<close>

urust_fn [application_def]
  :: \<open>64 word \<Rightarrow> ('s::cancellative_sepalg, 64 word, bool, nat prompt, unit prompt_output) function_body\<close>
  \<open> fn DeclaredPacketLength(packet: &Packet) -> u64 { PacketLength(packet) } \<close>

lemma declared_packet_length_equivalent:
  \<open>declared_packet_length packet = stable_packet_length packet\<close>
  unfolding declared_packet_length_def stable_packet_length_def by (rule refl)

text\<open>
The same declared type also permits literal iterator lifetimes and function-pointer types,
even when the Rust types have no HOL mapping.
\<close>

urust_fn
  :: \<open>64 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  \<open>
    fn DeclaredLiteralSignature(value: slice::Iter<'_, fn(&Packet) -> bool>)
      -> impl Iterator<Item = Packet> {
      value
    }
  \<close>

lemma declared_literal_signature_shape:
  \<open>declared_literal_signature = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding declared_literal_signature_def by (rule refl)

text\<open>
An explicitly typed \<open>self\<close> uses the signature's receiver type and the ordinary
parameter binding, including inside HOL escapes.
\<close>

urust_fn \<open> fn SelfPacketLength(self: u64) -> u64 { self + 1_u64 } \<close>

lemma self_packet_length_equivalent:
  \<open>self_packet_length packet = packet_length packet\<close>
  unfolding self_packet_length_def packet_length_def by (rule refl)

subsection\<open> Generic functions and trait constants \<close>

text\<open>
A trait mapping supplies the HOL sort and its associated-constant template. Here words implement a
capacity scale with a ceiling of sixteen. Inline and \<open>where\<close> bounds combine on \<open>T\<close>;
\<open>FixedBuffer<T, N>\<close> anchors both parameters in the signature. The value \<open>N\<close> is the
length witness converted to \<open>usize\<close>. The escape twin has the same HOL type and definition.
\<close>

class showcase_scale =
  fixes showcase_ceiling :: \<open> 'a itself \<Rightarrow> 64 word \<close>

instantiation word :: (len0) showcase_scale
begin

definition showcase_ceiling_word :: \<open> 'a::len0 word itself \<Rightarrow> 64 word \<close> where
  \<open> showcase_ceiling_word _ = 16 \<close>

instance ..

end

urust_trait "CapacityScale" = \<open> showcase_scale \<close>
  urust_consts "CEILING" = \<open> showcase_ceiling \<close>

urust_fn \<open>
  fn BoundedCapacity<T: CapacityScale, const N: usize>(buffer: FixedBuffer<T, N>) -> usize
    where T: Ord {
    if N < T::CEILING { N } else { T::CEILING }
  }
\<close>

urust_fn \<open>
  fn BoundedCapacityTwin(buffer: FixedBuffer<\<tau>\<open>'t::{showcase_scale, ord}\<close>,
      \<tau>\<open>'n::len\<close>>) -> usize {
    if \<llangle>of_nat LENGTH('n) :: 64 word\<rrangle> < \<llangle>showcase_ceiling TYPE('t)\<rrangle> {
      \<llangle>of_nat LENGTH('n) :: 64 word\<rrangle>
    } else { \<llangle>showcase_ceiling TYPE('t)\<rrangle> }
  }
\<close>

lemma bounded_capacity_twin:
  \<open> bounded_capacity = bounded_capacity_twin \<close>
  unfolding bounded_capacity_def bounded_capacity_twin_def by (rule refl)

urust_fn \<open>
  fn FourByteCapacity(buffer: FixedBuffer<u8, 4>) -> usize {
    BoundedCapacity::<u8, 4>(buffer)
  }
\<close>

urust_fn \<open>
  fn FourByteCapacityTwin(buffer: FixedBuffer<u8, 4>) -> usize {
    \<epsilon>\<open>bounded_capacity\<close>(buffer)
  }
\<close>

lemma four_byte_capacity_twin:
  \<open> four_byte_capacity = four_byte_capacity_twin \<close>
  unfolding four_byte_capacity_def four_byte_capacity_twin_def by (rule refl)

text\<open>
The concrete call supplies type and const arguments in their declaration order. Calls without
\<open>::<...>\<close> retain ordinary HOL inference; lifetimes are omitted from this argument list.
Both declarations and their escape twins use the showcase's enabled parse-print roundtrip check.
\<close>

text\<open>
The item command generates the HOL datatype, field lenses, and exact Rust constructor paths in one
local-theory transaction. The parser then uses those identities consistently for construction,
field access, and patterns.
\<close>

urust_expr showoff_datatype_items
  \<open>
    match DatatypeEvent::Packet(
      DatatypePacket {
        identifier: 3u64,
        tag: 7u32,
        state: Some(true),
        pair: (1u8, true),
        bytes: \<llangle>[] :: 8 word list\<rrangle>,
      }
    ) {
      DatatypeEvent::Packet(packet) \<Rightarrow> packet.tag,
      DatatypeEvent::Idle \<Rightarrow> 0u32,
    }
  \<close>

subsection\<open> Source-ordered chunks \<close>

text\<open>
A plain \<open>urust\<close> chunk declares several complete items in source order through the same
operations as the single-item commands, so later items use earlier types, constructors, fields
and functions. An \<open>\<omega>\<close> annotation on the line before an item supplies that item's options,
including its HOL name; the outer list supplies defaults shared by every item.
\<close>

urust [verbosity = 1] \<open>
  \<omega>\<open>hol_names = ["sampleCount" \<rightarrow> \<open>sample_count\<close>]\<close>
  struct ShowcaseReading { sampleCount: u32, ready: bool }

  \<omega>\<open>name = "showcase_signal", verbosity = 2\<close>
  enum ShowcaseSignal { Quiet, Loud(u32) }

  \<omega>\<open>application_def, verbosity = 2\<close>
  fn ShowcaseLevel(reading: ShowcaseReading, signal: ShowcaseSignal) -> u32 {
    match signal {
      ShowcaseSignal::Quiet => 0,
      ShowcaseSignal::Loud(gain) => if reading.ready { reading.sampleCount * gain } else { gain },
    }
  }

  \<omega>\<open>abbrev, register_notation = false\<close>
  fn ShowcaseDouble(value: u32) -> u32 { value + value }

  fn ShowcaseDoubledLevel(reading: ShowcaseReading) -> u32 {
    ShowcaseLevel(reading, ShowcaseSignal::Loud(2))
  }
\<close>

thm showcase_level_def showcase_doubled_level_def

term \<open>showcase_reading.sample_count\<close>

term \<open>showcase_double\<close>

subsection\<open> Pretty declaration output \<close>

text\<open>
The common \<open>pretty\<close> option changes verbosity-controlled declaration output to include
human-readable uRust. For expressions it removes redundant groups while preserving required
precedence; for datatypes it prints the normalized declaration after the artifact manifest. The
formatted source is reparsed by the new frontend so the InfoView inherits the parser's lexical,
semantic, entity, typing, and embedded-language markup.
\<close>

urust_expr [pretty, verbosity = 1]
  showoff_pretty_expression
  \<open>
    let grouped = (((1 + 1)));
    if grouped > 2 { grouped } else { 0 }
  \<close>

subsection\<open> Expressions, bindings, and control flow \<close>

text\<open>
Features: array literals and indexing, numeric tuple projections, suffixed decimal and hexadecimal
literals, nested tuple destructuring, \<open>let\<close> and \<open>const\<close>, operator precedence,
explicit narrowing and widening casts, strings, and \<open>if\<close>/\<open>else\<close>.
\<close>

urust_expr showoff_expression
  \<open>
    let inputs = vec![0x10_u32, 0x0f_u32, 0x20_u32];
    let tuple_view =
      (inputs[0_usize], (inputs[1_usize], true));
    let (base, (mask, enabled)) =
      tuple_view;
    \<comment> \<open>
      Formal comments retain Isabelle document checking, including \<^term>\<open>enabled\<close>,
      while remaining layout for both uRust frontends.
    \<close>
    const shift = 1_u64;
    let computed = (base | mask) << shift;
    let narrowed = computed as u16;
    let restored = narrowed as u32;
    assert!(tuple_view.0 == inputs[0_usize]);
    if tuple_view.1.1 && enabled && restored > inputs[2_usize] {
      (restored, "large")
    } else {
      (restored + 1_u32, "small")
    }
  \<close>

subsection\<open> Denotation navigation \<close>

text\<open>
Surface tokens now retain their exact denotational source ranges. In jEdit, control-flow keywords,
operators, casts, collection delimiters, calls, projections, and built-in macro heads jump to the
HOL constant selected by lowering. For example, the two \<open>match\<close> expressions below deliberately
select different roots: the numeral form targets \<^const>\<open>ncase_selector\<close>, while the constructor
form targets the native case encoding.
\<close>

urust_expr showoff_denotation_navigation
  \<open>
    let values = [1u64, 2u64];
    let selected =
      match values[0usize] {
        0 \<Rightarrow> 0u64,
        _ \<Rightarrow> values[1usize] as u64,
      };
    let wrapped = Some(selected);
    assert!(selected > 0u64);
    match wrapped {
      Some(value) \<Rightarrow> value + 1u64,
      None \<Rightarrow> 0u64,
    }
  \<close>

subsection\<open> Rust-aligned grammar and integer literals \<close>

text\<open>
Features: binary and octal literals, internal and trailing separators, unified prefix operators,
unary-before-cast precedence, nested block comments, and a direct conditional operand. Block-like classification affects
only statement and match-arm separator elision; it does not form a separate precedence ladder.
\<close>

urust_expr  showoff_grammar_literals
  \<open>
    let mask = 0b1010_0001u32;
    let permissions = 0o7_55u32;
    let narrowed = !mask as u8;
    /* Nested Rust block comments are ordinary layout.
       /* Their contents are not tokenized as uRust. */ */
    let adjusted =
      if true { mask } else { permissions } + 1_;
    (mask, permissions, narrowed, adjusted)
  \<close>

subsection\<open> Return match arms \<close>

text\<open>
Direct returns use expression-arm commas, including guarded arms. Braced return statements retain
semicolons, and the final arm may omit its comma.
\<close>

urust_expr showoff_return_match_arms ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
  \<open>
    match Some(\<llangle>7 :: nat\<rrangle>) {
      Some(value) if value > 0 \<Rightarrow> return value,
      Some(_) \<Rightarrow> { return \<llangle>0 :: nat\<rrangle>; },
      None \<Rightarrow> return \<llangle>1 :: nat\<rrangle>
    }
  \<close>

subsection\<open> List captures and structural integer patterns \<close>

text\<open>
An ordinary binding can alias an irrefutable rest-only list pattern. Matching then combines integer
elements with a middle capture, whose elements retain their source order.
\<close>

urust_expr showoff_list_captures
  \<open>
    let whole @ [rest @ ..] = \<llangle>[0, 11, 23, 42] :: nat list\<rrangle>;
    match whole {
      [0, middle @ .., 42] => (rest, middle),
      _ => (rest, [])
    }
  \<close>

lemma showoff_list_captures_result:
  \<open>
    showoff_list_captures =
      literal ([0, 11, 23, 42] :: nat list, [11, 23] :: nat list, TNil)
  \<close>
  by (simp add: showoff_list_captures_def micro_rust_simps)

subsection\<open> Array repeats \<close>

text\<open>
Features: ordinary repeat operands evaluated once, inline-const bodies evaluated once per element,
and arithmetic or contextual repeat lengths converted from \<mu>Rust \<open>usize\<close> values.
\<close>

urust_expr showoff_array_repeats
  \<open>
    let ordinary = [0u64/* repeat operand */; (1 + 1) * 2];
    let generated = [const { /* outer /* nested */ */ Some(0u64) }; 3usize];
    (ordinary, generated)
  \<close>

context
  fixes repeat_length :: \<open>64 word\<close>
begin

urust_expr showoff_contextual_array_repeat
  \<open> [const { Some(0u64) }; repeat_length] \<close>

end

subsection\<open> Rust type aliases \<close>

text\<open>
Type aliases are ordinary declarations available to subsequent commands and importing theories.
Using an alias as a cast target produces the same checked term as the expanded primitive.
\<close>

urust_type_alias \<open> type SmallId = u16; \<close>

urust_type_alias \<open> type IdPair<T> = (T, T); \<close>

urust_type_alias \<open> type BytePointer<T> = *const T; \<close>

urust_type_alias "types::BufferSize" \<open> type BufferSize = SmallId; \<close>

urust_datatype \<open>
  struct AliasBuffer {
    pointer: BytePointer<u8>,
    length: types::BufferSize,
  }
\<close>

urust_fn \<open>
  fn AliasBufferPointer(buffer: AliasBuffer) -> BytePointer<u8> {
    buffer.pointer
  }
\<close>

urust_fn \<open>
  fn KeepIdPair(pair: IdPair<SmallId>) -> (u16, u16) {
    pair
  }
\<close>

urust_expr showoff_scoped_cast_alias
  \<open> 0u64 as SmallId \<close>

urust_expr showoff_scoped_cast_alias_primitive
  \<open> 0u64 as u16 \<close>

lemma showoff_scoped_cast_alias_equal:
  \<open> showoff_scoped_cast_alias = showoff_scoped_cast_alias_primitive \<close>
  unfolding showoff_scoped_cast_alias_def showoff_scoped_cast_alias_primitive_def
  by (rule refl)

urust_expr showoff_cast_alias_repeats
  \<open>
    let ordinary = [0u64 as SmallId; 2 as usize];
    let generated = [const { /* outer /* nested */ */ 1u64 as SmallId }; 3usize];
    (ordinary, generated)
  \<close>

subsection\<open> Rust use imports \<close>

text\<open>
A \<open>urust\<close> chunk imports complete Rust use items under shorter names for its members.
The aliases end with the chunk. A grouped \<open>self\<close> imports the
enum type, while its variants are imported separately. Inside a body, a use statement is visible
throughout its block, including before the statement, and it is erased from the checked term.
\<close>

urust \<open>
  use DatatypeEvent::{self as Event, Idle, Packet as Carried};
  use types::BufferSize as Length;
  fn EventLength(event: Event, fallback: Length) -> Length {
    match event {
      Idle => fallback,
      Carried(_) => {
        let empty = 0u64 as Inner;
        use types::BufferSize as Inner;
        empty
      }
    }
  }
\<close>

urust_expr showoff_imported_events
  \<open>
    {
      let quiet = Quiet;
      use DatatypeEvent::{self as Event, Idle as Quiet};
      (quiet, Event::Idle)
    }
  \<close>

urust_expr showoff_qualified_events
  \<open> { let quiet = DatatypeEvent::Idle; (quiet, DatatypeEvent::Idle) } \<close>

lemma showoff_imported_events_equal:
  \<open> showoff_imported_events = showoff_qualified_events \<close>
  unfolding showoff_imported_events_def showoff_qualified_events_def
  by (rule refl)

text\<open>
As in Rust, a block import shadows a same-named local bound outside its block, and the local is
visible again after the block.
\<close>

urust_expr showoff_block_shadowing
  \<open>
    {
      use DatatypeEvent as Event;
      let marker = |event| event;
      let inner = { use Event::Idle as marker; marker };
      (inner, marker(Event::Idle))
    }
  \<close>

urust_expr showoff_block_shadowing_qualified
  \<open>
    {
      let marker = |event| event;
      let inner = { DatatypeEvent::Idle };
      (inner, marker(DatatypeEvent::Idle))
    }
  \<close>

lemma showoff_block_shadowing_equal:
  \<open> showoff_block_shadowing = showoff_block_shadowing_qualified \<close>
  unfolding showoff_block_shadowing_def showoff_block_shadowing_qualified_def
  by (rule refl)

subsection\<open> Imports in chunks \<close>

text\<open>
A chunk may contain use items. Their aliases are visible to every declaration of the chunk,
including declarations written before the use item, and disappear when the command ends; the
generated declarations above remain available. An item that the chunk declares can be imported by the
members after it.
\<close>

urust [verbosity = 1] \<open>
  use types::BufferSize as Length;
  fn ShowcaseArrivalTag(arrival: Arrival) -> u32 {
    match arrival {
      Waiting => 0,
      Delivered(packet) => packet.tag,
    }
  }

  use DatatypeEvent::{self as Arrival, Idle as Waiting, Packet as Delivered};

  struct ShowcaseFrame { arrival: Arrival, size: Length }

  use ShowcaseArrivalTag as tag_of;

  fn ShowcaseFrameTag(frame: ShowcaseFrame) -> u32 { tag_of(frame.arrival) }
\<close>

urust_fn \<open>
  fn ShowcaseQualifiedTag(arrival: DatatypeEvent) -> u32 {
    match arrival {
      DatatypeEvent::Idle => 0,
      DatatypeEvent::Packet(packet) => packet.tag,
    }
  }
\<close>

lemma showcase_arrival_tag_equal:
  \<open> showcase_arrival_tag = showcase_qualified_tag \<close>
  unfolding showcase_arrival_tag_def showcase_qualified_tag_def
  by (rule refl)

subsection\<open> Primitive associated items \<close>

definition showoff_primitive_u8_max :: \<open> 8 word \<close>
  where \<open> showoff_primitive_u8_max = 7 \<close>

definition showoff_primitive_u64_max :: \<open> 64 word \<close>
  where \<open> showoff_primitive_u64_max = 63 \<close>

definition showoff_primitive_count :: \<open> 64 word \<close>
  where \<open> showoff_primitive_count = 3 \<close>

definition showoff_primitive_values :: \<open> 64 word option list \<close>
  where \<open> showoff_primitive_values = [Some 5, None] \<close>

definition showoff_primitive_from ::
    \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> showoff_primitive_from = lift_fun1 id \<close>

micro_rust_notation (literal) showoff_primitive_u8_max ("u8::MAX")

micro_rust_notation (literal) showoff_primitive_u64_max ("u64::MAX")

micro_rust_notation (literal) showoff_primitive_count ("usize::COUNT")

micro_rust_notation (literal) showoff_primitive_values ("u64::VALUES")

micro_rust_notation (call) showoff_primitive_from ("u64::from")

text\<open>
Exact registered primitive heads compose with ordinary layout, casts, calls, postfixes, and repeat
lengths. The primitive token remains a keyword while the terminal associated item carries notation
navigation.
\<close>

urust_expr showoff_primitive_associated_items
  \<open>
    let repeated =
      [u64 /* associated constant */ :: MAX; usize::COUNT];
    let widened = u8::MAX as u64;
    let converted = u64::from(widened);
    let selected = u64::VALUES[0_usize]?;
    (repeated, converted, selected)
  \<close>

subsection\<open> Logging and yield \<close>

text\<open>
Features: registered logger calls, mixed logging-data entries, lexical identifier capture, primitive
yield and logging, and ordinary sequencing.
\<close>

urust_expr showoff_logging_yield
  \<open>
    let request' = \<llangle>7 :: nat\<rrangle>;
    info!(l\<llangle>"request ", request', " started"\<rrangle>);
    \<y>\<i>\<e>\<l>\<d>;
    \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat request']\<rrangle>;
    debug!(l\<llangle>"request ", request', " resumed"\<rrangle>)
  \<close>

subsection\<open> Calls, methods, and propagation \<close>

urust_fn
  [attrs = [micro_rust_simps]] \<open> fn showoff_inline_disabled() -> u64 { 3u64 } \<close>

text\<open>
The optional \<open>application_def\<close> shape keeps the explicit source parameters on the generated
definition theorem's left-hand side without changing the curried function value.
\<close>

urust_fn [application_def, verbosity = 2] \<open> fn showoff_declared_mix(left: u64, right: u64) -> u64 { left * 3u64 + right } \<close>

text\<open>
Bare declaration wildcards keep their typed argument slots and source order but introduce no
lexical name. They may be repeated or mixed with named parameters in either command.
\<close>

urust_fn [application_def] \<open> fn showoff_wildcard_function(_: (), kept: u64, _: bool) -> u64 { kept + 1_u64 } \<close>

urust_expr [abbrev] showoff_wildcard_expression ::
  \<open>unit \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit, unit) expression\<close>
  (_, kept)
  \<open> kept \<close>

urust_fn [abbrev, verbosity = 2] \<open> fn showoff_abbreviated_function(item: u64) -> u64 { item + 1_u64 } \<close>

urust_expr [verbosity = 2] showoff_typed_common ::
  \<open>64 word \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  (left, right)
  \<open> left * 5u64 + right \<close>

urust_expr [abbrev] showoff_contextual_mix
  (left, right)
  \<open> left * 3_u64 + right \<close>

definition showoff_bump ::
    \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_bump \<equiv> lift_fun1 (\<lambda>x. x + 1) \<close>

definition showoff_mix ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_mix \<equiv> lift_fun2 (\<lambda>x y. x * 3 + y) \<close>

definition showoff_generic_bump ::
    \<open>nat \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_generic_bump _ \<equiv> showoff_bump \<close>

definition showoff_generic_parameter :: nat
  where \<open> showoff_generic_parameter = 1 \<close>

notation showoff_generic_parameter ("\<clubsuit>")

urust_notation (call) showoff_generic_bump ("Showoff::bump")

text\<open>
Features: an array literal, range slicing and indexing, a let-bound
expression-antiquotation callee, an arity-indexed HOL function literal with a restricted turbofish,
nested calls, receiver-prepended method calls, method chaining, Option propagation around call and
method results, propagation grouped before a method, a conditional argument, structured-path
turbofish with ordinary HOL identifier arithmetic, comparisons, and an \<open>if let\<close> binder with a
fallback.
\<close>

urust_expr showoff_calls
  \<open>
    let inputs = [5_u64, 2_u64, 1_u64, 0_u64];
    let active = inputs[0_usize..2_usize];
    let seed = active[0_usize];
    let seed_present = matches!(Some(seed), Some(_));
    debug_assert!(seed_present, ignored_showoff_diagnostic);
    let callable = \<llangle>showoff_bump\<rrangle>;
    let lifted =
      \<llangle>\<lambda>ignored x. x + 1\<rrangle>\<^sub>2
        ::<showoff_generic_parameter>(seed);
    let direct =
      Some(Showoff::bump::<showoff_generic_parameter + 1>(
        \<epsilon>\<open>callable\<close>(lifted)
      ))?;
    let chained =
      (Some(direct.showoff_mix(showoff_bump(active[1_usize])))?).showoff_bump();
    if let Some(selected) = Some(chained) {
      if selected >= 20_u64 {
        Some(
          selected.showoff_mix(
            (if true { Some(inputs[2_usize])? } else { Some(inputs[3_usize])? })
          )
        )?
      } else {
        Some(seed.showoff_bump().showoff_bump())?
      }
    } else {
      seed
    }
  \<close>

urust_expr showoff_function_command_call
  \<open> showoff_declared_mix(4_u64, 2_u64) \<close>

urust_expr showoff_function_abbreviation_call
  \<open> showoff_abbreviated_function(4_u64) \<close>

subsection\<open> Registered struct construction \<close>

datatype showoff_struct_value =
  ShowoffStructValue "64 word" bool

definition showoff_struct_lift ::
    \<open>
      64 word \<Rightarrow> bool \<Rightarrow>
      (unit, showoff_struct_value, unit, unit, unit) function_body
    \<close>
  where \<open> showoff_struct_lift \<equiv> lift_fun2 ShowoffStructValue \<close>

micro_rust_notation (call) showoff_struct_lift ("Showoff::StructValue")

text\<open>
The labels are retained for source markup and otherwise erase exactly as in the active frontend;
the registered qualified head receives the two initializers in source order. Parentheses make the
struct expression explicit when it is used as a control head.
\<close>

urust_expr showoff_struct_expression
  \<open>
    match_case (
      Showoff::StructValue {
        payload: 7_u64,
        enabled: true
      }
    ) {
      ShowoffStructValue(payload, _) \<Rightarrow> payload
    }
  \<close>

subsection\<open> Nested and guarded matches \<close>

datatype showoff_event =
    ShowoffData "nat option" bool
  | ShowoffRetry "nat option"
  | ShowoffStop

datatype showoff_registered_event =
    ShowoffRegisteredData nat
  | ShowoffRegisteredStop

datatype showoff_singleton_event =
  ShowoffSingletonEvent nat

simple_word_enum (plugins del: word_conversion) (8)
  showoff_word_state =
    ShowoffWordIdle = 1
  | ShowoffWordRunning = 2
  | ShowoffWordSleeping = 3

micro_rust_notation (literal)
  showoff_registered_event.ShowoffRegisteredData
  ("Showoff::Event::Data")

micro_rust_notation (literal)
  showoff_registered_event.ShowoffRegisteredStop
  ("Showoff::Event::Stop")

micro_rust_notation (literal)
  showoff_singleton_event.ShowoffSingletonEvent
  ("Showoff::Singleton::Event")

definition showoff_singleton_event_lift ::
    \<open>
      nat \<Rightarrow>
      (unit, showoff_singleton_event, unit, unit, unit) function_body
    \<close>
  where
    \<open> showoff_singleton_event_lift \<equiv> lift_fun1 ShowoffSingletonEvent \<close>

micro_rust_notation (call)
  showoff_singleton_event_lift
  ("Showoff::Singleton::Event")

definition showoff_registered_number :: nat where
  \<open> showoff_registered_number \<equiv> 7 \<close>

micro_rust_notation (literal)
  showoff_registered_number
  ("Showoff::Seven")

urust_expr showoff_registered_match
  \<open>
    match \<llangle>ShowoffRegisteredData 7\<rrangle> {
      Showoff::Event::Data(value) \<Rightarrow> value,
      Showoff::Event::Stop \<Rightarrow> 0
    }
  \<close>

urust_expr showoff_registered_numeric_match
  \<open>
    match 7 {
      0 \<Rightarrow> False,
      Showoff::Seven \<Rightarrow> True,
      _ \<Rightarrow> False
    }
  \<close>

urust_expr showoff_registered_nested_nullary_match
  \<open>
    match Some(Showoff::Event::Stop) {
      Some(Showoff::Event::Stop) \<Rightarrow> True,
      _ \<Rightarrow> False
    }
  \<close>

urust_expr  showoff_registered_singleton_match
  \<open>
    match Some(Showoff::Singleton::Event(9)) {
      Some(Showoff::Singleton::Event(whole @ _)) \<Rightarrow> whole,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr  showoff_bare_word_state_match ::
  \<open>
    showoff_word_state \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (state)
  \<open>
    match_case state {
      ShowoffWordIdle \<Rightarrow> 0,
      ShowoffWordRunning | ShowoffWordSleeping \<Rightarrow> 1
    }
  \<close>

text\<open>
Features: automatic case and registered-value/numeral switch routing, an explicit
numeric switch, datatype-aware qualified constructor markup, constructor and value patterns,
bare typedef-backed variants, or-patterns, direct structural-matrix lowering, deep
registered-nullary constructor cases with genuine fall-through, structural-totality removal of
redundant singleton fallbacks, full guard bodies, semicolon-free explicit match sequencing, nested
matches, ordered fall-through, and antiquotation capture of both a let-bound variable and an arm
binder.
\<close>

text\<open>
C1-I5 gives a guarded or-pattern one source-arm guard and next-arm fall-through, so this showcase
uses the corrected semantics instead of asserting equality with the old alternative expansion.
\<close>

urust_expr  showoff_matches
  \<open>
    let floor = \<llangle>2 :: nat\<rrangle>;
    match \<llangle>ShowoffData (Some 7) True\<rrangle> {
      ShowoffData(Some(x), true) | ShowoffRetry(Some(x))
          if
            let threshold = floor;
            match_case Some(()) { Some(marker) \<Rightarrow> marker, None \<Rightarrow> () }
            if let Some(limit) = Some(threshold) {
              x > limit
            } else {
              false
            }
          \<Rightarrow>
        match_switch x {
          0 | 1 \<Rightarrow> floor,
          _ \<Rightarrow> \<llangle>x + floor\<rrangle>
        },
      ShowoffData(Some(x), false)
          if (match Some(x) {
            Some(_) \<Rightarrow> true,
            None \<Rightarrow> false
          }) \<Rightarrow>
        x,
      ShowoffData(None, _) | ShowoffRetry(None) | ShowoffStop \<Rightarrow>
        0,
      _ \<Rightarrow>
        1
    }
  \<close>

subsection\<open> Advanced patterns \<close>

datatype showoff_packet =
    ShowoffPacket
      (showoff_tag: nat)
      (showoff_payload: "nat list")
      (showoff_fallback: "nat option")
  | ShowoffEmpty

text\<open>
Features: struct, slice-rest, constructor, reference-pattern wrappers, and
or-patterns in one match, followed by a guard and antiquotation capture of
bindings from deep inside the pattern. Binder declarations retain coloring and shared
highlighting without hyperlinks; uses navigate to the canonical declaration.
\<close>

urust_expr  showoff_patterns
  \<open>
    match \<llangle>ShowoffPacket 2 [3, 5, 8] (Some 13)\<rrangle> {
      ShowoffPacket {
        showoff_tag: &tag,
        showoff_payload: [&head, .., & mut tail],
        showoff_fallback: &Some(&backup)
      } if tag > 0 && backup > 0 \<Rightarrow>
        \<llangle>head + tail + backup\<rrangle>,
      ShowoffPacket {
        showoff_tag: _,
        showoff_payload: [],
        ..
      } | ShowoffEmpty \<Rightarrow>
        0,
      _ \<Rightarrow>
        1
    }
  \<close>

subsection\<open> Fueled loops and mutable state \<close>

definition showoff_reference ::
    \<open>'v \<Rightarrow> (unit, (unit, unit, 'v) Global_Store.ref, unit, unit, unit) function_body\<close>
  where \<open> showoff_reference \<equiv> undefined \<close>

definition showoff_dereference ::
    \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> (unit, 'v, unit, unit, unit) function_body\<close>
  where \<open> showoff_dereference \<equiv> undefined \<close>

definition showoff_update ::
    \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      (unit, unit, unit, unit, unit) function_body\<close>
  where \<open> showoff_update \<equiv> undefined \<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> showoff_dereference
adhoc_overloading store_reference_const \<rightleftharpoons> showoff_reference
adhoc_overloading store_update_const \<rightleftharpoons> showoff_update

text\<open>
Features: fuel captured from local binders, nested fueled loops, semicolon-free
loop sequencing, iterator conversion and loop-pattern binders, arrays of
references, indexed reads and updates, mutable word, boolean, and optional state,
numeric switching, assignment, and \<open>while let\<close> termination.
\<close>

urust_expr showoff_nested_loops
  \<open>
    let outer_fuel = \<llangle>4 :: nat\<rrangle>;
    let inner_fuel = \<llangle>2 :: nat\<rrangle>;
    let mut phase = 0_u32;
    let mut active = \<llangle>True\<rrangle>;
    let registers = [phase];
    #[fuel(\<epsilon>\<open>outer_fuel\<close>)] while (*active) {
      match_switch *registers[0_usize] {
        0 \<Rightarrow> {
          *registers[0_usize] = *registers[0_usize] + 1_u32;
        },
        1 \<Rightarrow> {
          #[fuel(\<epsilon>\<open>inner_fuel\<close>)] loop {
            *registers[0_usize] = *registers[0_usize] + 1_u32;
          }
          *active = false;
        },
        _ \<Rightarrow> {
          *active = false;
        }
      };
    }
    (*registers[0_usize], *active)
  \<close>

urust_expr showoff_for_and_while_let
  \<open>
    let values = [1_u32, 2_u32, 3_u32];
    let mut total = 0_u32;
    for value in values {
      *total += value;
    }
    let pending_values = [Some(4_u32), None];
    let steps = \<llangle>2 :: nat\<rrangle>;
    let mut pending = pending_values[0_usize];
    #[fuel(\<epsilon>\<open>steps\<close>)] while let Some(extra) = *pending {
      *total += extra;
      *pending = None;
    }
    assert_eq!(*total, 10_u32);
    *total
  \<close>

subsection\<open> Iterator combinators \<close>

text\<open>
Features: receiver-prepended iterator methods, chained \<open>into_iter\<close>
conversion, shortest-input truncation, and pair-valued iterator elements.
\<close>

urust_fn \<open>
  fn showoff_iterator_zip() -> \<tau>\<open>(unit, 32 word \<times> bool \<times> tnil, unit, unit, unit) iterator\<close> {
    [1_u32, 2_u32].into_iter().zip([True, False].into_iter())
  }
  \<close>

text\<open>
Features: a mutable reference parameter with an erased lifetime, a write through it, and a
caller that passes a mutable local with \<open>&mut\<close>.
\<close>

urust_fn
  \<open>
  fn ShowoffIncrement<'a>(counter: &'a mut u32) {
    *counter += 1_u32;
  }
  \<close>

urust_expr showoff_borrowed_increment
  \<open>
    let mut counter = 0_u32;
    ShowoffIncrement(&mut counter);
    *counter
  \<close>

text\<open>
Features: a match expression in the while condition, a direct function call on
dereferenced state, conditional loop-body control flow, a nested unconditional
loop, assignment from call results, and capture of two independent fuel binders.
\<close>

urust_expr showoff_loop_pipeline
  \<open>
    let scan_fuel = \<llangle>5 :: nat\<rrangle>;
    let burst_fuel = \<llangle>2 :: nat\<rrangle>;
    let mut cursor = 0_u64;
    #[fuel(\<epsilon>\<open>scan_fuel\<close>)] while (
      match_switch *cursor {
        0 | 1 | 2 \<Rightarrow> true,
        _ \<Rightarrow> false
      }
    ) {
      let next = showoff_bump(*cursor);
      if next == 2_u64 {
        #[fuel(\<epsilon>\<open>burst_fuel\<close>)] loop {
          *cursor = showoff_bump(*cursor);
        }
      } else {
        *cursor = next;
      }
    }
    *cursor
  \<close>

subsection\<open> Macro composition pipeline \<close>

text\<open>
Features: vector construction and indexing, nested \<open>matches!\<close> conditions,
direct complete-body macro arguments with sequencing and nested control flow,
parenthesis and bracket delimiters, ignored-body erasure, an aborting
\<open>let ... else\<close> binding, and aborting fallback branches.
\<close>

urust_expr showoff_macro_pipeline
  \<open>
    let candidates = vec![Some(4_u32), None];
    let first = candidates[0_usize];
    debug_assert!(
      let present = matches!(first, Some(_));
      if present { true } else { false },
      let ignored = unknown_pipeline_value;
      ignored
    );
    let Some(candidate) = first else {
      unreachable!("candidate disappeared")
    };
    let selected =
      if matches!(first, Some(_)) {
        let values = vec![4_u32, 8_u32];
        assert_eq!(values[0_usize], 4_u32);
        assert_eq!(candidate, values[0_usize]);
        candidate
      } else {
        unreachable!("candidate disappeared")
      };
    assert![
      let selected_present = matches!(Some(selected), Some(_));
      selected_present
    ];
    if selected > 0_u32 {
      selected
    } else {
      panic!("non-positive selection")
    }
  \<close>

subsection\<open> Closure capture and higher-order invocation \<close>

definition showoff_invoke_closure ::
    \<open>64 word \<Rightarrow>
      (64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body) \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_invoke_closure value closure \<equiv> closure value \<close>

text\<open>
Features: direct higher-order argument passing, a helper that invokes the supplied
closure, capture of an outer local and the closure formal, nested block control flow,
local bindings inside the closure, value-antiquotation capture, and a terminal return.
\<close>

urust_expr showoff_closure_pipeline
  \<open>
    let outer = 3_u64;
    showoff_invoke_closure(
      5_u64,
      |input| {
        let adjusted =
          if input > outer {
            let bump = 1_u64;
            \<llangle>input + outer + bump\<rrangle>
          } else {
            outer
          };
        return \<llangle>adjusted + outer\<rrangle>;
      }
    )
  \<close>

definition showoff_invoke_pair_closure ::
    \<open>64 word \<times> 64 word \<times> tnil \<Rightarrow>
      (64 word \<times> 64 word \<times> tnil \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body) \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_invoke_pair_closure value closure \<equiv> closure value \<close>

text\<open>
Features: a tuple-pattern closure formal, destructured inside the closure body exactly as a
\<open>let\<close> binding would, with capture of an outer local.
\<close>

urust_expr showoff_closure_tuple_formal
  \<open>
    let scale = 2_u64;
    showoff_invoke_pair_closure(
      (3_u64, 4_u64),
      |(width, height)| {
        let area = width * height;
        area * scale
      }
    )
  \<close>

subsection\<open> Accepted-surface improvements \<close>

text\<open>
Features: Rust line comments and glued suffixes, an indexed array with a trailing
separator, trailing separators on calls, tuples, and match arms, ASCII match
arrows, propagation directly into a method, a mixed \<open>else if let\<close> chain,
a total conditional binding without an unreachable fallback in the checked term,
and empty ordinary and unsafe blocks.
\<close>

urust_expr  showoff_improvements
  \<open>
    // These spellings are accepted only by the dedicated parser.
    let seeds = [1u64, 2u64,];
    let seed = seeds[0usize];
    let bumped = Some(showoff_bump(seed,))?.showoff_bump();
    let selected =
      if seed == 0u64 {
        seed
      } else if let Some(value) = Some(bumped) {
        value
      } else if bumped > 2u64 {
        bumped
      } else {
        seed
      };
    let total =
      if let selected_value = selected {
        selected_value
      } else {
        seed
      };
    match Some(total) {
      Some(value) => (value, {}, unsafe {},),
      None => (0u64, {}, unsafe {},),
    }
  \<close>

subsection\<open> Lexical callbacks and member names \<close>

text\<open>
A local callback shadows the automatically registered direct call. A method name still selects the
registered function, and the callback stops shadowing after its block. The explicit qualified
notation also remains available within that block.
\<close>

urust_fn lexical_showcase_global
  \<open> fn ShowcaseStep(item: u64) -> u64 { item + 1u64 } \<close>

micro_rust_notation (call) lexical_showcase_global ("Showcase::step")

urust_expr lexical_showcase_scope
  \<open>
    let local_result = {
      let ShowcaseStep = |item| item + 2u64;
      (ShowcaseStep(3u64), 3u64.ShowcaseStep(), Showcase::step(3u64))
    };
    (local_result, ShowcaseStep(3u64))
  \<close>

urust_expr lexical_showcase_scope_control
  \<open>
    let local_result = {
      let local_callback = |item| item + 2u64;
      (local_callback(3u64), 3u64.ShowcaseStep(), Showcase::step(3u64))
    };
    (local_result, ShowcaseStep(3u64))
  \<close>

lemma \<open>lexical_showcase_scope = lexical_showcase_scope_control\<close>
  unfolding lexical_showcase_scope_def lexical_showcase_scope_control_def by (rule refl)

subsection\<open> Inherent impl blocks \<close>

text\<open>
An inherent \<open>impl\<close> block is a chunk member. Each member is an ordinary \<open>urust_fn\<close>
declaration, named \<open>showcase_odometer_<member>\<close> unless an \<open>\<omega>\<close> \<open>name\<close>
annotation chooses another name, and registers its associated path
\<open>ShowcaseOdometer::f\<close>. A member whose first parameter is a \<open>self\<close> receiver also registers a
method entry, so it is called as \<open>x.f(..)\<close> or \<open>ShowcaseOdometer::f(x, ..)\<close>; an
associated function such as \<open>zeroed\<close> is called only through its path. \<open>Self\<close> names the
implementing type in signatures, struct expressions, patterns and paths, and \<open>Self::f(..)\<close>
calls this impl's own member. At verbosity 1 each member prints its registration manifest.
\<close>

urust [verbosity = 1] \<open>
  struct ShowcaseOdometer { distance: u32 }

  impl ShowcaseOdometer {
    fn zeroed() -> Self { Self { distance: 0_u32 } }

    fn reading(self) -> u32 { self.distance }

    \<omega>\<open>name = "showcase_odometer_store"\<close>
    fn set_distance(&mut self, distance: u32) { self.distance = distance; }

    fn doubled(self) -> u32 { Self::reading(self) + self.reading() }
  }

  fn ShowcaseOdometerTotal(odometer: ShowcaseOdometer) -> u32 {
    let fresh = ShowcaseOdometer::zeroed();
    odometer.reading() + ShowcaseOdometer::reading(fresh) + odometer.doubled()
  }

  fn ShowcaseOdometerReset(odometer: &mut ShowcaseOdometer) {
    odometer.set_distance(1_u32);
    ShowcaseOdometer::set_distance(odometer, 0_u32);
  }
\<close>

urust_fn [register_notation = false] showcase_odometer_reading_control
  \<open> fn reading(self: ShowcaseOdometer) -> u32 { self.distance } \<close>

lemma showcase_odometer_reading_is_typed_member:
  \<open> showcase_odometer_reading = showcase_odometer_reading_control \<close>
  unfolding showcase_odometer_reading_def showcase_odometer_reading_control_def
  by (rule refl)

section\<open> Type-directed automatic call notation \<close>

text\<open>
Two functions may share a Rust call name when their argument types distinguish them. Direct and
method calls use the same notation registry, and repeating an explicit notation is idempotent.
\<close>

urust_fn showcase_echo_word \<open> fn showcaseEcho(value: u8) -> u8 { value } \<close>
urust_fn showcase_echo_flag \<open> fn showcaseEcho(value: bool) -> bool { value } \<close>
micro_rust_notation (call) showcase_echo_word ("showcaseEcho")

urust_fn \<open>
  fn showcaseEchoPair(value: u8, flag: bool) -> (u8, bool) {
    (value.showcaseEcho(), showcaseEcho(flag))
  }
\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> showoff_dereference
no_adhoc_overloading store_reference_const \<rightleftharpoons> showoff_reference
no_adhoc_overloading store_update_const \<rightleftharpoons> showoff_update

subsection\<open> Datatype selector naming \<close>

text\<open>
Enum payload rename keys use the source variant name. \<open>"Variant.field"\<close> renames a named
payload selector and \<open>"Variant.N"\<close> gives a tuple field a selector, also after the
constructor itself is renamed. Rust paths and patterns keep their source spelling.
\<close>

urust_datatype [backend = hol, hol_names = [
  "Sent" \<rightarrow> \<open>SelectorNameSent\<close>,
  "Sent.0" \<rightarrow> \<open>selector_name_sent_id\<close>,
  "Bounced.code" \<rightarrow> \<open>selector_name_bounce_code\<close>
]] \<open>
  enum SelectorNameDelivery { Sent(u32), Bounced { code: u32 } }
\<close>

urust_expr showoff_selector_name_delivery \<open>
  match SelectorNameDelivery::Sent(7u32) {
    SelectorNameDelivery::Sent(id) \<Rightarrow> id,
    SelectorNameDelivery::Bounced { code } \<Rightarrow> code,
  }
\<close>

lemma
  \<open>selector_name_sent_id (SelectorNameSent n) = n\<close>
  \<open>selector_name_bounce_code (Bounced c) = c\<close>
  by simp_all

text\<open>
The inline-only \<open>[unprefixed_selectors]\<close> drops the type prefix from automatic selectors,
while explicit keys still choose their own names. Rust field access is unchanged.
\<close>

urust_datatype [unprefixed_selectors, hol_names = ["selectorNameAttempts" \<rightarrow> \<open>selector_name_tries\<close>]]
\<open>
  struct SelectorNameReceipt { selectorNameId: u32, selectorNameAttempts: u32 }
\<close>

urust_expr showoff_selector_name_receipt \<open>
  (SelectorNameReceipt { selectorNameId: 3u32, selectorNameAttempts: 1u32 }).selectorNameAttempts
\<close>

lemma
  \<open>selector_name_id (make_selector_name_receipt i a) = i\<close>
  \<open>selector_name_tries (make_selector_name_receipt i a) = a\<close>
  by simp_all

subsection\<open> Retained generic headers \<close>

text\<open>
The complete HOL type supplies the body and channels while the Rust header keeps its structured
generic/callable bounds and local lifetime binder. The unmapped header names require no registry
entry. This preserves header syntax, without adding a trait solver or const evaluation.
\<close>

urust_fn [pp_test] showoff_retained_header
  :: \<open> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body \<close>
\<open>
  fn ShowoffRetainedHeader<F: for<'a> Fn(&'a Unknown) -> Unknown,
      T: Sequence<Item = Unknown>, const N: bool>(value: Unknown) -> Unknown
    where T: [const] Marker
  { value }
\<close>

urust_fn showoff_retained_header_plain
  :: \<open> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body \<close>
  \<open> fn ShowoffRetainedHeaderPlain(value: Unknown) -> Unknown { value } \<close>

lemma showoff_retained_header_twin:
  \<open>showoff_retained_header = showoff_retained_header_plain\<close>
  unfolding showoff_retained_header_def showoff_retained_header_plain_def by (rule refl)

subsection\<open> Generic inherent impl scopes \<close>

text\<open>
A mixed impl header makes its lifetime, element type and capacity available to every member.
Each member extends that scope independently. The target selects the inherited arguments;
the final turbofish below supplies only the member's local type.
\<close>

urust \<open>
  struct ShowcaseStorage<T, const N: usize> { value: T, slots: [T; N] }
  impl<'a, T, const N: usize> ShowcaseStorage<T, N> {
    fn capacity(self) -> usize { N }
    fn borrow(&'a mut self) -> &'a mut Self { self }
    fn choose<'b, U>(&'b mut self, value: U) -> U { value }
  }
  \<omega>\<open>register_notation = false\<close>
  fn ShowcaseStorageCapacityTwin<T, const N: usize>(self: ShowcaseStorage<T, N>) -> usize { N }
  \<omega>\<open>register_notation = false\<close>
  fn ShowcaseStorageBorrowTwin<'a, T, const N: usize>(self: &'a mut ShowcaseStorage<T, N>)
      -> &'a mut ShowcaseStorage<T, N> { self }
  \<omega>\<open>register_notation = false\<close>
  fn ShowcaseStorageChooseTwin<'b, T, const N: usize, U>(self: &'b mut ShowcaseStorage<T, N>, value: U)
      -> U { value }
  fn ShowcaseStorageSelected(storage: &mut ShowcaseStorage<u8, 3>, value: bool) -> bool {
    ShowcaseStorage::<u8, 3>::choose::<bool>(storage, value)
  }
  fn ShowcaseStorageMethod(storage: &mut ShowcaseStorage<u8, 3>, value: bool) -> bool {
    storage.choose::<bool>(value)
  }
  fn ShowcaseStorageCallTwin(storage: &mut ShowcaseStorage<u8, 3>, value: bool) -> bool {
    \<epsilon>\<open>showcase_storage_choose\<close>(storage, value)
  }
\<close>

lemma showcase_storage_capacity_twin:
  \<open> showcase_storage_capacity = showcase_storage_capacity_twin \<close>
  unfolding showcase_storage_capacity_def showcase_storage_capacity_twin_def by (rule refl)
lemma showcase_storage_borrow_twin:
  \<open> showcase_storage_borrow = showcase_storage_borrow_twin \<close>
  unfolding showcase_storage_borrow_def showcase_storage_borrow_twin_def by (rule refl)
lemma showcase_storage_choose_twin:
  \<open> showcase_storage_choose = showcase_storage_choose_twin \<close>
  unfolding showcase_storage_choose_def showcase_storage_choose_twin_def by (rule refl)
lemma showcase_storage_selected_twin:
  \<open> showcase_storage_selected = showcase_storage_call_twin \<close>
  unfolding showcase_storage_selected_def showcase_storage_call_twin_def by (rule refl)
lemma showcase_storage_method_twin:
  \<open> showcase_storage_method = showcase_storage_call_twin \<close>
  unfolding showcase_storage_method_def showcase_storage_call_twin_def by (rule refl)


subsection\<open> Outlives bounds with erased lifetime relations \<close>

text\<open>
Bounds validate the combined impl and member lifetime scope, including forward and cyclic
relations. They leave the HOL function, mutable-reference channels and call behavior unchanged.
No borrow relation is inferred from these erased source assertions.
\<close>

urust \<open>
  struct ShowcaseOutlives<T> { value: T }
  impl<'a: 'b, 'b: 'a, T: 'b> ShowcaseOutlives<T>
  where Self: 'static, Unknown<&'a T>: 'b {
    fn carry<'c: 'a, U: 'c>(&'b mut self, value: &'c mut U) -> &'c mut U
    where T: 'c { value }
  }
  fn ShowcaseOutlivesPlain<'b, 'c, T, U>(owner: &'b mut ShowcaseOutlives<T>, value: &'c mut U)
    -> &'c mut U { value }
  fn ShowcaseOutlivesSelected<'a, 'b>(owner: &'a mut ShowcaseOutlives<u8>, value: &'b mut bool)
    -> &'b mut bool { ShowcaseOutlives::<u8>::carry::<bool>(owner, value) }
  fn ShowcaseOutlivesCallTwin<'a, 'b>(owner: &'a mut ShowcaseOutlives<u8>, value: &'b mut bool)
    -> &'b mut bool { \<epsilon>\<open>showcase_outlives_carry\<close>(owner, value) }
\<close>

lemma showcase_outlives_erased:
  \<open> showcase_outlives_carry = showcase_outlives_plain \<close>
  unfolding showcase_outlives_carry_def showcase_outlives_plain_def by (rule refl)
lemma showcase_outlives_selected_twin:
  \<open> showcase_outlives_selected = showcase_outlives_call_twin \<close>
  unfolding showcase_outlives_selected_def showcase_outlives_call_twin_def by (rule refl)


subsection\<open> Generic signature fidelity in one callable pipeline \<close>

text\<open>
The generic inherent impl retains its element and const-capacity source slots. Outlives bounds
validate the impl and member scope, then erase. A member-local callable consumes the actual
array type and shares its enclosing computation channels. These authoritative declarations need
no HOL type escapes. The retained-header control above separately keeps complete HOL signatures
unchanged even when their Rust callable syntax lies outside the authoritative denotation.
\<close>

urust \<open>
  struct ShowcaseCallableStorage<T, const N: usize> { slots: [T; N] }
  impl<'a, T: 'a, const N: usize> ShowcaseCallableStorage<T, N> where Self: 'static {
    fn apply<'b: 'a, F: std::ops::FnOnce([T; N]) -> T + 'b>(self: Self, callback: F) -> T
    where T: 'b { callback(self.slots) }
    fn capacity(self: Self) -> usize { N }
  }
  \<omega>\<open>register_notation = false\<close>
  fn ShowcaseCallableStoragePlain<T, const N: usize, F: Fn([T; N]) -> T>(
      owner: ShowcaseCallableStorage<T, N>, callback: F) -> T { callback(owner.slots) }
  fn ShowcaseCallableSelected<F: Fn([bool; 3]) -> bool>(
      owner: ShowcaseCallableStorage<bool, 3>, callback: F) -> bool {
    ShowcaseCallableStorage::<bool, 3>::apply::<F>(owner, callback)
  }
  fn ShowcaseCallableMethod<F: Fn([bool; 3]) -> bool>(
      owner: ShowcaseCallableStorage<bool, 3>, callback: F) -> bool { owner.apply::<F>(callback) }
  fn ShowcaseCallableCallTwin<F: Fn([bool; 3]) -> bool>(
      owner: ShowcaseCallableStorage<bool, 3>, callback: F) -> bool {
    \<epsilon>\<open>showcase_callable_storage_apply\<close>(owner, callback)
  }
\<close>

lemma showcase_callable_storage_twin:
  \<open> showcase_callable_storage_apply = showcase_callable_storage_plain \<close>
  unfolding showcase_callable_storage_apply_def showcase_callable_storage_plain_def by (rule refl)
lemma showcase_callable_selected_twin:
  \<open> showcase_callable_selected = showcase_callable_call_twin \<close>
  unfolding showcase_callable_selected_def showcase_callable_call_twin_def by (rule refl)
lemma showcase_callable_method_twin:
  \<open> showcase_callable_method = showcase_callable_call_twin \<close>
  unfolding showcase_callable_method_def showcase_callable_call_twin_def by (rule refl)


subsection\<open> Explicit scoped representation choices \<close>

urust_type [model = \<open>epoch = 'epoch\<close>]
  "ShowcaseModel" = \<open>'epoch option\<close>
context notes [[urust_model_parameters = \<open>
  ["address" \<rightarrow> \<open>nat\<close>, "global" \<rightarrow> \<open>unit\<close>,
   "epoch" \<rightarrow> \<open>bool\<close>]
\<close>]]
begin
urust_fn showcase_model_parameters \<open>
  fn ShowcaseModelParameters(value: ShowcaseModel, pointer: &mut u32) -> ShowcaseModel { value }
\<close>
urust_fn showcase_model_parameters_escape \<open>
  fn ShowcaseModelParametersEscape(value: \<tau>\<open>bool option\<close>,
    pointer: \<tau>\<open>(nat, unit, 32 word) ref\<close>) -> \<tau>\<open>bool option\<close> { value }
\<close>
lemma showcase_model_parameters_twin:
  \<open> showcase_model_parameters = showcase_model_parameters_escape \<close>
  unfolding showcase_model_parameters_def showcase_model_parameters_escape_def by (rule refl)
end


section\<open> Shared representations with scoped model parameters \<close>

urust_type [model = \<open>epoch = 'epoch\<close>, shared = \<open>value\<close>]
  "ShowcaseSharedValueModel" = \<open>'epoch option\<close>
urust_type [model = \<open>epoch = 'epoch\<close>, shared = \<open>readonly\<close>]
  "ShowcaseSharedReadonlyModel" = \<open>'epoch option\<close>
context notes [[urust_model_parameters = \<open>
  ["address" \<rightarrow> \<open>nat\<close>, "global" \<rightarrow> \<open>unit\<close>,
   "epoch" \<rightarrow> \<open>bool\<close>]
\<close>]]
begin
urust_fn [pp_test] showcase_shared_representations \<open>
  fn ShowcaseSharedRepresentations(value: &ShowcaseSharedValueModel,
    storage: &mut ShowcaseSharedReadonlyModel, observed: &ShowcaseSharedReadonlyModel)
    -> &ShowcaseSharedValueModel { value }
\<close>
urust_fn showcase_shared_representations_escape \<open>
  fn ShowcaseSharedRepresentationsEscape(value: \<tau>\<open>bool option\<close>,
    storage: \<tau>\<open>(nat, unit, bool option) ref\<close>,
    observed: \<tau>\<open>(nat, unit, bool option) ro_ref\<close>) -> \<tau>\<open>bool option\<close> { value }
\<close>
lemma showcase_shared_representations_twin:
  \<open> showcase_shared_representations = showcase_shared_representations_escape \<close>
  unfolding showcase_shared_representations_def showcase_shared_representations_escape_def by (rule refl)
urust_fn [pp_test, state = \<open>'state\<close>, abort = \<open>'abort\<close>,
  input = \<open>'input\<close>, output = \<open>'output\<close>] showcase_shared_callback \<open>
  fn ShowcaseSharedCallback<F: Fn(&ShowcaseSharedValueModel) -> &ShowcaseSharedValueModel>(
    callback: F, value: &ShowcaseSharedValueModel) -> &ShowcaseSharedValueModel { callback(value) }
\<close>
urust_fn [state = \<open>'state\<close>, abort = \<open>'abort\<close>,
  input = \<open>'input\<close>, output = \<open>'output\<close>] showcase_shared_callback_escape \<open>
  fn ShowcaseSharedCallbackEscape(callback: \<tau>\<open>bool option \<Rightarrow>
    ('state, bool option, 'abort, 'input, 'output) function_body\<close>,
    value: \<tau>\<open>bool option\<close>) -> \<tau>\<open>bool option\<close> { callback(value) }
\<close>
lemma showcase_shared_callback_twin:
  \<open> showcase_shared_callback = showcase_shared_callback_escape \<close>
unfolding showcase_shared_callback_def showcase_shared_callback_escape_def by (rule refl)
ML_val\<open>
local
  val ctxt = \<^context>
  fun canonical typ = Term_Subst.instantiateT (TVars.make
    (rev (Term.add_tvarsT typ []) |> map_index
      (fn (index, variable as (_, sort)) => (variable, TVar (("shared_showcase", index), sort))))) typ
  fun typ name = canonical (Sign.the_const_type (Proof_Context.theory_of ctxt)
    (Proof_Context.intern_const ctxt name))
in
  val _ = List.app (fn (native, escaped) => if typ native = typ escaped then ()
    else error "shared showcase changed full principal types, sorts or sharing")
    [("showcase_shared_representations", "showcase_shared_representations_escape"),
     ("showcase_shared_callback", "showcase_shared_callback_escape")]
end
\<close>
end

section\<open> Canonical slices and qualified vectors \<close>

context notes [[urust_model_parameters = \<open>
  ["address" \<rightarrow> \<open>nat\<close>, "global" \<rightarrow> \<open>unit\<close>]
\<close>]]
begin
urust_fn [pp_test] showcase_sequences \<open>
  fn ShowcaseSequences<'a, T>(value: [T], shared: &'a [T], editable: &'a mut [T],
    vector: std::vec::Vec<T>) -> [T] { value }
\<close>
urust_fn showcase_sequences_escape \<open>
  fn ShowcaseSequencesEscape<T>(value: \<tau>\<open>'T list\<close>,
    shared: \<tau>\<open>(nat, unit, 'T list) ro_ref\<close>,
    editable: \<tau>\<open>(nat, unit, 'T list) ref\<close>,
    vector: \<tau>\<open>'T list\<close>) -> \<tau>\<open>'T list\<close> { value }
\<close>
lemma showcase_sequences_twin:
  \<open> showcase_sequences = showcase_sequences_escape \<close>
  unfolding showcase_sequences_def showcase_sequences_escape_def by (rule refl)
end

end
