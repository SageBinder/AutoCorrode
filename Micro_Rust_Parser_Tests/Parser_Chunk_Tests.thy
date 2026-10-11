(* Readable urust chunk examples; internal audits are in Parser_Chunk_Regression_Tests. *)

theory Parser_Chunk_Tests
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
    Shallow_Separation_Logic.Separation_Algebra
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]
declare [[urust_register_notation = true]]

chapter\<open> Source-ordered uRust chunks \<close>

text\<open>
The plain \<open>urust\<close> command declares a nonempty chunk of complete Rust \<open>fn\<close>,
\<open>struct\<close> and \<open>enum\<close> items in source order. Each item uses the same parsed-item
declaration operation as \<open>urust_fn\<close> or \<open>urust_datatype\<close>, so earlier items are available
to later ones exactly as in a sequence of single-item commands. An optional
\<open>\<omega>\<open>OPTION, OPTION = VALUE, ...\<close>\<close> annotation on its own line immediately before an item
supplies that item's options, including the command-layer HOL binding \<open>name\<close>.
An optional outer list supplies defaults for \<open>pp_test\<close>, \<open>pretty\<close>, \<open>verbosity\<close> and
\<open>register_notation\<close>. A failure in any item rejects the whole command.
\<close>


section\<open> Mixed functions and datatypes \<close>

urust \<open>
  \<omega>\<open>renames = ["sampleValue" \<rightarrow> "sample"]\<close>
  struct ChunkPacket { sampleValue: u32, valid: bool }

  \<omega>\<open>name = "chunk_choice"\<close>
  enum ChunkChoice { Ready, Empty }

  \<omega>\<open>name = "chunk_packet_value", application_def\<close>
  fn ChunkPacketValue(packet: ChunkPacket) -> u32 { packet.sampleValue }

  \<omega>\<open>abbrev, register_notation = false\<close>
  fn ChunkIdentity(value: u32) -> u32 { value }
\<close>

thm chunk_packet_value_def
term \<open>chunk_packet.sample\<close>
term \<open>chunk_choice.Ready\<close>
term \<open>chunk_identity\<close>

text\<open> The same declarations through the single-item commands, under distinct names. \<close>

urust_fn [application_def] control_packet_value
  \<open> fn ControlPacketValue(packet: ChunkPacket) -> u32 { packet.sampleValue } \<close>

urust_fn [abbrev, register_notation = false]
  \<open> fn ControlIdentity(value: u32) -> u32 { value } \<close>

urust_datatype [renames = ["sampleValue" \<rightarrow> "sample"]]
  \<open> struct ControlPacket { sampleValue: u32, valid: bool } \<close>

urust_datatype control_choice \<open> enum ControlChoice { Ready, Empty } \<close>

lemma chunk_packet_value_matches_control:
  shows \<open>chunk_packet_value = control_packet_value\<close>
  by (intro ext) (simp only: chunk_packet_value_def control_packet_value_def)

lemma chunk_identity_matches_control:
  shows \<open>chunk_identity = control_identity\<close>
  by (rule refl)


section\<open> One-item chunks \<close>

urust \<open> fn ChunkSingleFunction() -> u32 { 1 } \<close>

urust \<open> struct ChunkSingleUnit; \<close>

urust \<open>
  \<omega>\<open>name = _\<close>
  fn ChunkCheckedOnly(value: u32) -> u32 { value + 1 }
\<close>


section\<open> Item shapes, layout and consecutive transitions \<close>

text\<open>
Items may use any supported shape. Comments, strings, nested braces, expression
antiquotations and signature HOL type escapes do not disturb item boundaries.
\<close>

urust \<open>
  // A unit struct and a tuple struct, each terminated by a semicolon.
  struct ChunkMarker;
  struct ChunkPair(u32, \<tau>\<open>nat\<close>);

  /* An empty named struct and an empty tuple struct. */
  struct ChunkNothing {}
  struct ChunkNoFields();

  fn ChunkBraces(flag: bool) -> u32 {
    let text = "} { fn struct";
    if flag { { 1 } } else { \<epsilon>\<open>literal 2\<close> }
  }

  \<comment> \<open>An enum with payload variants after a function body.\<close>
  enum ChunkShape { Dot, Line(u32), Box { width: u32, height: u32 } }

  fn ChunkEscape(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }

  #[repr(u8)]
  enum ChunkLevel { Low = 1, High = 2 }

  fn ChunkAfterRepr() -> bool { true }
\<close>

term \<open>make_chunk_pair\<close>
term \<open>chunk_shape.Box\<close>
thm chunk_braces_def chunk_escape_def chunk_after_repr_def


section\<open> Outer defaults and annotation overrides \<close>

text\<open>
An annotation replaces the outer default, which replaces the scoped configuration.
Annotations never become defaults for later items.
\<close>

urust [register_notation = false, verbosity = 1] \<open>
  \<omega>\<open>register_notation\<close>
  fn ChunkRegistered(value: u32) -> u32 { value }

  fn ChunkUnregistered(value: u32) -> u32 { value }

  \<omega>\<open>verbosity = 2, pretty = false\<close>
  struct ChunkDefaulted { value: u32 }

  \<omega>\<open>register_notation = true\<close>
  struct ChunkAliased { value: u32 }
\<close>

urust_fn chunk_calls_registered
  \<open> fn ChunkCallsRegistered(value: u32) -> u32 { ChunkRegistered(value) } \<close>


section\<open> Every option kind \<close>

urust \<open>
  \<omega>\<open>attrs = [micro_rust_simps], pp_test = true, pretty = false, verbosity = 0\<close>
  fn ChunkWithAttributes(value: u32) -> u32 { value }

  \<omega>\<open>state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>\<close>
  fn ChunkChannels(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }

  \<omega>\<open>parameters = ["T" \<rightarrow> "'element::ord"], name = chunk_holder\<close>
  struct ChunkHolder<T> { element: T }

  \<omega>\<open>backend = hol\<close>
  enum ChunkNative { NativeFirst, NativeSecond(u32) }

  \<omega>\<open>backend = "simple_word_enum", word_width = 16, plugins = (plugins only: word_conversion)\<close>
  enum ChunkWord { WordLow = 1, WordHigh = 2 }

  \<omega>\<open>pp_test = false, abbrev = false, application_def = false, register_notation\<close>
  fn ChunkExplicitBooleans() -> u32 { 0 }

  \<omega>\<open>backend = "simple_word_enum", word_width = 16\<close>
  enum ChunkWordPlugins { PluginLow = 1, PluginHigh = 2 }

  \<omega>\<open>backend = "enum"\<close>
  #[repr(u8)]
  enum ChunkReprCustom { ReprCustomLow = 1, ReprCustomHigh = 2 }

  #[repr(u8)]
  enum ChunkReprDefault { ReprDefaultLow = 1, ReprDefaultHigh = 2 }
\<close>

thm chunk_with_attributes_def
term \<open>chunk_holder.chunk_holder_element\<close>

urust_fn [attrs = [micro_rust_simps], pp_test = true, pretty = false, verbosity = 0]
  \<open> fn ControlWithAttributes(value: u32) -> u32 { value } \<close>

urust_fn [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>]
  \<open> fn ControlChannels(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_datatype [parameters = ["T" \<rightarrow> "'element::ord"]] control_holder
  \<open> struct ControlHolder<T> { element: T } \<close>

urust_datatype [backend = "simple_word_enum", word_width = 16, plugins = (plugins only: word_conversion)]
  \<open> enum ControlWord { ControlWordLow = 1, ControlWordHigh = 2 } \<close>


section\<open> Earlier declarations in later items \<close>

urust \<open>
  enum ChunkSignal { Stop, Go(u32) }

  struct ChunkEnvelope { signal: ChunkSignal, count: u32 }

  fn ChunkMakeEnvelope(count: u32) -> ChunkEnvelope {
    ChunkEnvelope { signal: ChunkSignal::Go(count), count: count }
  }

  fn ChunkSignalValue(envelope: ChunkEnvelope) -> u32 {
    match envelope.signal {
      ChunkSignal::Stop => 0,
      ChunkSignal::Go(value) => value,
    }
  }

  fn ChunkRoundTrip(count: u32) -> u32 {
    ChunkSignalValue(ChunkMakeEnvelope(count))
  }
\<close>

thm chunk_round_trip_def


section\<open> Locale contexts \<close>

locale chunk_bounded =
  fixes chunk_limit :: \<open>64 word\<close>
begin

urust \<open>
  struct ChunkBoundedCell { contents: u64 }

  fn ChunkBoundedLimit() -> u64 { \<epsilon>\<open>literal chunk_limit\<close> }
\<close>

end

interpretation chunk_bounded_seven: chunk_bounded \<open>7\<close> .

thm chunk_bounded.chunk_bounded_limit_def
thm chunk_bounded_seven.chunk_bounded_limit_def

text\<open>
Declarations inside an experiment remain confined to it, as for single-item commands.
Datatype generation inside an experiment is a separate boundary of \<open>urust_datatype\<close>.
\<close>

experiment
begin

urust \<open>
  fn ChunkConfinedOne() -> u32 { 1 }

  fn ChunkConfinedTwo() -> u32 { ChunkConfinedOne() }
\<close>

end

ML_val \<open>
  @{assert} (is_none (URust_Item_Scope.lookup_function \<^context> "ChunkConfinedOne"));
  @{assert} (is_none (URust_Item_Scope.lookup_function \<^context> "ChunkConfinedTwo"))
\<close>

end
