(* Readable examples of source-ordered urust chunks and Rust use imports in chunks and
   blocks. The ML audits are in Parser_Chunk_Use_ML_Tests. *)

theory Parser_Chunk_Use_Examples
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
    Shallow_Separation_Logic.Separation_Algebra
begin

chapter\<open> Rust use import fixtures \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

text\<open>
Declaration-only items shared by the Rust block and chunk import tests. Every
name is synthetic. The items cover each namespace and shape that an import can target: generated
enums, variants and structs, a generated function, exact literal and call notations, an overloaded
literal, Rust type mappings and a type alias.
\<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

urust_datatype \<open> enum UseChoice { Empty, Value(u32), Named { sample: u32 } } \<close>

urust_datatype \<open> enum UseOtherChoice { Value(bool) } \<close>

urust_datatype \<open> struct UsePacket { sample: u32 } \<close>

urust_datatype \<open> struct UseTuple(u32); \<close>

urust_datatype \<open> struct UseUnit; \<close>

urust_datatype \<open> struct UseWrapper<T> { inner: T } \<close>

urust_fn \<open> fn use_increment(x: u32) -> u32 { x + 1 } \<close>

urust_fn \<open> fn use_pair(x: u32, y: u64) -> u64 { y } \<close>

urust_fn \<open> fn use_identity(x: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { x } \<close>

urust_fn [register_notation = false] use_demo_increment_impl
  \<open> fn demo_increment(x: u32) -> u32 { x + 2 } \<close>

urust_fn [register_notation = false] use_demo_value_impl
  \<open> fn demo_value() -> u32 { 9 } \<close>

definition use_demo_width :: \<open> 32 word \<close> where
  \<open> use_demo_width = 4 \<close>

definition use_demo_zero_narrow :: \<open> 32 word \<close> where
  \<open> use_demo_zero_narrow = 0 \<close>

definition use_demo_zero_wide :: \<open> 64 word \<close> where
  \<open> use_demo_zero_wide = 0 \<close>

definition use_demo_count :: \<open> 64 word \<close> where
  \<open> use_demo_count = 2 \<close>

micro_rust_notation (call) use_demo_increment_impl ("demo::increment")

micro_rust_notation (call) use_demo_value_impl ("demo::value")

micro_rust_notation (literal) use_demo_width ("demo::WIDTH")

micro_rust_notation (literal) use_demo_zero_narrow ("demo::ZERO")

micro_rust_notation (literal) use_demo_zero_wide ("demo::ZERO")

micro_rust_notation (literal) use_demo_count ("demo::COUNT")

urust_type "demo::Width" = \<open> 32 word \<close>

urust_type "demo::Cell<'a>" = \<open> 'a list \<close>

urust_type_alias "demo::Short" \<open> type Short = u16; \<close>

urust_type_alias "demo::Pointer" \<open> type Pointer<T> = *const T; \<close>

urust \<open>
  use use_increment as fixture_step;
  fn UseFixtureImported(x: u32) -> u32 { fixture_step(x) }
\<close>

chapter\<open> Source-ordered uRust chunks \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

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
  \<omega>\<open>hol_names = ["sampleValue" \<rightarrow> \<open>sample\<close>]\<close>
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

urust_fn [application_def] \<open> fn ControlPacketValue(packet: ChunkPacket) -> u32 { packet.sampleValue } \<close>

urust_fn [abbrev, register_notation = false]
  \<open> fn ControlIdentity(value: u32) -> u32 { value } \<close>

urust_datatype [hol_names = ["sampleValue" \<rightarrow> \<open>sample\<close>]]
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

urust_fn \<open> fn ChunkCallsRegistered(value: u32) -> u32 { ChunkRegistered(value) } \<close>

section\<open> Every option kind \<close>

urust \<open>
  \<omega>\<open>attrs = [micro_rust_simps], pp_test = true, pretty = false, verbosity = 0\<close>
  fn ChunkWithAttributes(value: u32) -> u32 { value }

  \<omega>\<open>state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>\<close>
  fn ChunkChannels(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }

  \<omega>\<open>hol_type_parameters = ["T" \<rightarrow> \<open>'element::ord\<close>], name = chunk_holder\<close>
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

urust_datatype [hol_type_parameters = ["T" \<rightarrow> \<open>'element::ord\<close>]] control_holder
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

chapter\<open> Rust use imports \<close>

section\<open> Scoped imports \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

text\<open>
Imports belong to their chunk or block. Every generated definition below is compared by kernel
reflexivity with its explicitly qualified counterpart, so the import changes only name resolution.
\<close>

subsection\<open> Values, calls and constructors \<close>

urust_fn \<open> fn UseFixtureImportedQualified(x: u32) -> u32 { use_increment(x) } \<close>

lemma \<open> use_fixture_imported = use_fixture_imported_qualified \<close>
  unfolding use_fixture_imported_def use_fixture_imported_qualified_def by (rule refl)

urust_expr use_call \<open> use demo::increment as inc; inc(3) \<close>

urust_expr use_call_qualified \<open> demo::increment(3) \<close>

lemma \<open> use_call = use_call_qualified \<close>
  unfolding use_call_def use_call_qualified_def by (rule refl)

urust_expr use_literal \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; Width_Value \<close>

urust_expr use_literal_qualified \<open> demo::WIDTH \<close>

lemma \<open> use_literal = use_literal_qualified \<close>
  unfolding use_literal_def use_literal_qualified_def by (rule refl)

urust_expr use_overloaded_narrow \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; ZERO + 1u32 \<close>

urust_expr use_overloaded_narrow_qualified \<open> demo::ZERO + 1u32 \<close>

lemma \<open> use_overloaded_narrow = use_overloaded_narrow_qualified \<close>
  unfolding use_overloaded_narrow_def use_overloaded_narrow_qualified_def by (rule refl)

urust_expr use_overloaded_wide \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; ZERO + 1u64 \<close>

urust_expr use_overloaded_wide_qualified \<open> demo::ZERO + 1u64 \<close>

lemma \<open> use_overloaded_wide = use_overloaded_wide_qualified \<close>
  unfolding use_overloaded_wide_def use_overloaded_wide_qualified_def by (rule refl)

urust_expr use_nullary_call \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; fetch() \<close>

urust_expr use_nullary_call_qualified \<open> demo::value() \<close>

lemma \<open> use_nullary_call = use_nullary_call_qualified \<close>
  unfolding use_nullary_call_def use_nullary_call_qualified_def by (rule refl)

urust_expr use_generated_call \<open> use use_increment as bump; bump(2) \<close>

urust_expr use_generated_call_qualified \<open> use_increment(2) \<close>

lemma \<open> use_generated_call = use_generated_call_qualified \<close>
  unfolding use_generated_call_def use_generated_call_qualified_def by (rule refl)

urust_expr use_heterogeneous \<open> use use_identity as ident; (ident(1u32), ident(true)) \<close>

urust_expr use_heterogeneous_qualified \<open> (use_identity(1u32), use_identity(true)) \<close>

lemma \<open> use_heterogeneous = use_heterogeneous_qualified \<close>
  unfolding use_heterogeneous_def use_heterogeneous_qualified_def by (rule refl)

urust_expr use_constructors \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; use Selection::Value as SelectedValue; (Present(3), Empty, Selection::Value(4), SelectedValue(5)) \<close>

urust_expr use_constructors_qualified
  \<open> (UseChoice::Value(3), UseChoice::Empty, UseChoice::Value(4), UseChoice::Value(5)) \<close>

lemma \<open> use_constructors = use_constructors_qualified \<close>
  unfolding use_constructors_def use_constructors_qualified_def by (rule refl)

urust_expr use_named_construction
  \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; use {UsePacket as Packet, UseTuple as Tuple1, UseUnit as Unit1, UseWrapper as Wrapper}; (NamedVariant { sample: 5 }, Selection::Named { sample: 6 }, Packet { sample: 7 }) \<close>

urust_expr use_named_construction_qualified
  \<open> (UseChoice::Named { sample: 5 }, UseChoice::Named { sample: 6 }, UsePacket { sample: 7 }) \<close>

lemma \<open> use_named_construction = use_named_construction_qualified \<close>
  unfolding use_named_construction_def use_named_construction_qualified_def by (rule refl)

urust_expr use_struct_constructors \<open> use {UsePacket as Packet, UseTuple as Tuple1, UseUnit as Unit1, UseWrapper as Wrapper}; (Tuple1(7), Unit1) \<close>

urust_expr use_struct_constructors_qualified \<open> (UseTuple(7), UseUnit) \<close>

lemma \<open> use_struct_constructors = use_struct_constructors_qualified \<close>
  unfolding use_struct_constructors_def use_struct_constructors_qualified_def by (rule refl)

urust_expr use_repeat \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; [0u8; COUNT] \<close>

urust_expr use_repeat_qualified \<open> [0u8; demo::COUNT] \<close>

lemma \<open> use_repeat = use_repeat_qualified \<close>
  unfolding use_repeat_def use_repeat_qualified_def by (rule refl)

urust_expr use_cast (x) \<open> use demo::{Width as Word32, Short, Cell, Pointer}; x as Short \<close>

urust_expr use_cast_qualified (x) \<open> x as demo::Short \<close>

lemma \<open> use_cast = use_cast_qualified \<close>
  unfolding use_cast_def use_cast_qualified_def by (rule refl)

subsection\<open> Patterns \<close>

urust_expr use_match (c)
  \<open>
    use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; match c {
      Present(n) => n,
      Empty => 0,
      NamedVariant { sample } => sample,
    }
  \<close>

urust_expr use_match_qualified (c)
  \<open>
    match c {
      UseChoice::Value(n) => n,
      UseChoice::Empty => 0,
      UseChoice::Named { sample } => sample,
    }
  \<close>

lemma \<open> use_match = use_match_qualified \<close>
  unfolding use_match_def use_match_qualified_def by (rule refl)

urust_expr use_match_enum_paths (c)
  \<open>
    use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; match c {
      Selection::Value(n) => n,
      Selection::Named { sample } => sample,
      _ => 0,
    }
  \<close>

urust_expr use_match_enum_paths_qualified (c)
  \<open>
    match c {
      UseChoice::Value(n) => n,
      UseChoice::Named { sample } => sample,
      _ => 0,
    }
  \<close>

lemma \<open> use_match_enum_paths = use_match_enum_paths_qualified \<close>
  unfolding use_match_enum_paths_def use_match_enum_paths_qualified_def by (rule refl)

urust_expr use_literal_pattern (x) \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; match x { Width_Value => 1u32, _ => 0 } \<close>

urust_expr use_literal_pattern_qualified (x) \<open> match x { demo::WIDTH => 1u32, _ => 0 } \<close>

lemma \<open> use_literal_pattern = use_literal_pattern_qualified \<close>
  unfolding use_literal_pattern_def use_literal_pattern_qualified_def by (rule refl)

urust_expr use_struct_pattern (p) \<open> use {UsePacket as Packet, UseTuple as Tuple1, UseUnit as Unit1, UseWrapper as Wrapper}; match p { Packet { sample } => sample } \<close>

urust_expr use_struct_pattern_qualified (p) \<open> match p { UsePacket { sample } => sample } \<close>

lemma \<open> use_struct_pattern = use_struct_pattern_qualified \<close>
  unfolding use_struct_pattern_def use_struct_pattern_qualified_def by (rule refl)

subsection\<open> Types \<close>

urust \<open>
  use demo::{Width as Word32, Short, Cell, Pointer};
  use UseWrapper as Wrapper;
  fn use_signature(x: Word32, y: Short, z: Cell<u8>, w: Wrapper<u8>, p: Pointer<u8>) -> Short { y }
\<close>

urust_fn \<open>
    fn use_signature_qualified(
      x: demo::Width, y: demo::Short, z: demo::Cell<u8>, w: UseWrapper<u8>, p: demo::Pointer<u8>
    ) -> demo::Short { y }
  \<close>

lemma \<open> use_signature = use_signature_qualified \<close>
  unfolding use_signature_def use_signature_qualified_def by (rule refl)

urust \<open>
  use demo::{Width as Word32, Short, Cell};
  struct UseImportedFields { width: Word32, short: Short, cell: Cell<u8> }
\<close>

urust_datatype \<open> struct UseQualifiedFields { width: demo::Width, short: demo::Short, cell: demo::Cell<u8> } \<close>

subsection\<open> Rejections without fallback \<close>

urust_expr_rejects \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; Width_Value(3) \<close> \<open> resolves to "demo::WIDTH", which cannot be used as a call \<close>

urust_expr_rejects \<open> use demo::increment as inc; inc \<close> \<open> resolves to "demo::increment", which cannot be used as a value \<close>

urust_expr_rejects \<open> use demo::increment as inc; [0u8; inc] \<close> \<open> which cannot be used as an array repeat length \<close>

urust_expr_rejects \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; Present \<close> \<open> requires positional call syntax \<close>

urust_expr_rejects \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; Empty() \<close> \<open> is a bare value, not a call \<close>

urust_expr_rejects \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; Present(1, 2) \<close> \<open> expects 1 argument(s), but got 2 \<close>

urust_expr_rejects \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; Selection::Missing(1) \<close> \<open> resolves to "UseChoice::Missing", which cannot be used as a call \<close>

urust_expr_rejects \<open> use demo::{Width as Word32, Short, Cell, Pointer}; Word32::Value(1) \<close> \<open> is not a generated enum and cannot qualify a path \<close>

urust_expr_rejects \<open> use use_increment as bump; bump::<u8>(1) \<close> \<open> generic arguments are not supported on generated Rust function paths \<close>

urust_expr_rejects \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; 1u8 as NamedVariant \<close> \<open> names the enum variant "UseChoice::Named", not a type \<close>

urust_expr_rejects \<open> use demo::{Width as Word32, Short, Cell, Pointer}; 1u8 as Word32 \<close> \<open> no supported cast operation \<close>

text\<open>
Closure formals resolve generated constructors as \<open>for\<close> binders do: an imported unit variant is a
refutable formal, and an unimported generated variant basename requires its exact item path.
\<close>

urust_expr_rejects \<open> use UseChoice::Empty; |Empty| () \<close> \<open> unsupported or refutable pattern in a closure formal position \<close>

urust_expr_rejects \<open> |Empty| () \<close> \<open> generated Rust constructor pattern "Empty" requires an exact item path \<close>

subsection\<open> Locales, experiments and interpretation \<close>

locale use_command_locale =
  fixes use_command_parameter :: nat
begin

urust_expr use_locale_literal \<open> use demo::WIDTH as LocaleWidth; LocaleWidth \<close>
urust_expr use_locale_literal_qualified \<open> demo::WIDTH \<close>
lemma \<open> use_locale_literal = use_locale_literal_qualified \<close>
  unfolding use_locale_literal_def use_locale_literal_qualified_def by (rule refl)

end

context use_command_locale
begin

urust_expr use_locale_reopened \<open> use demo::WIDTH as LocaleWidth; LocaleWidth \<close>

end

experiment
begin

urust_expr use_experiment_call \<open> use demo::value as experiment_fetch; experiment_fetch() \<close>

end

interpretation use_command_interpretation: use_command_locale 0 .

section\<open> Block imports \<close>

text\<open>
A use statement is visible throughout its block, including before its declaration, and in every
nested expression scope; it never escapes the block. Each block's imports are resolved before any
of its expressions or patterns, and are erased: every definition below is kernel-equal to its
import-free counterpart.
\<close>

definition use_tick :: \<open> (nat, nat, 'r, 'abort, 'i, 'o) expression \<close> where
  \<open> use_tick = bind (get id) (\<lambda>current. bind (put Suc) (\<lambda>_. literal current)) \<close>

urust_expr use_block_before_declaration
  \<open> { let answer = local_inc(41); let retained = answer; use demo::increment as local_inc; retained } \<close>

urust_expr use_block_before_declaration_plain
  \<open> { let answer = demo::increment(41); let retained = answer; retained } \<close>

lemma \<open> use_block_before_declaration = use_block_before_declaration_plain \<close>
  unfolding use_block_before_declaration_def use_block_before_declaration_plain_def by (rule refl)

urust_expr use_block_reverse_dependencies
  \<open> { assert!(LocalPresent(7) == LocalSelection::Value(7)); use LocalSelection::Value as LocalPresent; use UseChoice as LocalSelection; LocalPresent(8) } \<close>

urust_expr use_block_reverse_dependencies_plain
  \<open> { assert!(UseChoice::Value(7) == UseChoice::Value(7)); UseChoice::Value(8) } \<close>

lemma \<open> use_block_reverse_dependencies = use_block_reverse_dependencies_plain \<close>
  unfolding use_block_reverse_dependencies_def use_block_reverse_dependencies_plain_def by (rule refl)

urust_expr use_block_nested
  \<open>
    {
      use demo::increment as pick;
      let first = pick(1);
      let second = { let early = pick(2); use use_increment as pick; (early, pick(3)) };
      let third = pick(4);
      let sibling = { use use_increment as pick; pick(5) };
      (first, second, third, sibling, pick(6))
    }
  \<close>

urust_expr use_block_nested_plain
  \<open>
    {
      let first = demo::increment(1);
      let second = { let early = use_increment(2); (early, use_increment(3)) };
      let third = demo::increment(4);
      let sibling = { use_increment(5) };
      (first, second, third, sibling, demo::increment(6))
    }
  \<close>

lemma \<open> use_block_nested = use_block_nested_plain \<close>
  unfolding use_block_nested_def use_block_nested_plain_def by (rule refl)

urust_expr use_block_captured_identity
  \<open>
    {
      use UseChoice as Selected;
      use Selected::Value as Captured;
      { use UseOtherChoice as Selected; (Captured(7), Selected::Value(true)) }
    }
  \<close>

urust_expr use_block_captured_identity_plain
  \<open> { { (UseChoice::Value(7), UseOtherChoice::Value(true)) } } \<close>

lemma \<open> use_block_captured_identity = use_block_captured_identity_plain \<close>
  unfolding use_block_captured_identity_def use_block_captured_identity_plain_def by (rule refl)

urust_expr use_block_closures
  \<open>
    {
      let callback = || selected_value();
      use demo::value as selected_value;
      let inner = |x| { use demo::increment as step; step(x) };
      use use_increment as shadowed;
      let first = shadowed(1);
      let shadowed = |x| x;
      (callback(), inner(2), first, shadowed(3))
    }
  \<close>

urust_expr use_block_closures_plain
  \<open>
    {
      let callback = || demo::value();
      let inner = |x| { demo::increment(x) };
      let first = use_increment(1);
      let shadowed = |x| x;
      (callback(), inner(2), first, shadowed(3))
    }
  \<close>

lemma \<open> use_block_closures = use_block_closures_plain \<close>
  unfolding use_block_closures_def use_block_closures_plain_def by (rule refl)

urust_expr use_block_control (c, choice)
  \<open>
    {
      let branch = if c { use demo::increment as step; step(1) } else { use use_increment as step; step(2) };
      for i in 0u32..3 { use demo::increment as each; each(i); }
      let UseChoice::Value(n) = choice else { use demo::value as fallback; return fallback(); };
      let matched = match choice { UseChoice::Empty => { use demo::value as arm; arm() }, _ => n };
      (branch, matched)
    }
  \<close>

urust_expr use_block_control_plain (c, choice)
  \<open>
    {
      let branch = if c { demo::increment(1) } else { use_increment(2) };
      for i in 0u32..3 { demo::increment(i); }
      let UseChoice::Value(n) = choice else { return demo::value(); };
      let matched = match choice { UseChoice::Empty => { demo::value() }, _ => n };
      (branch, matched)
    }
  \<close>

lemma \<open> use_block_control = use_block_control_plain \<close>
  unfolding use_block_control_def use_block_control_plain_def by (rule refl)

urust_expr use_block_patterns (choice)
  \<open>
    {
      use UseChoice::{Value as V, Empty as E, Named as N};
      match choice { V(n) => n, E => 0, N { sample } => sample }
    }
  \<close>

urust_expr use_block_patterns_plain (choice)
  \<open>
    {
      match choice { UseChoice::Value(n) => n, UseChoice::Empty => 0, UseChoice::Named { sample } => sample }
    }
  \<close>

lemma \<open> use_block_patterns = use_block_patterns_plain \<close>
  unfolding use_block_patterns_def use_block_patterns_plain_def by (rule refl)

urust_expr use_block_binder (choice) \<open> { use UseChoice::Value as V; match choice { V(n) => n, other => 0 } } \<close>

urust_expr use_block_binder_plain (choice) \<open> { match choice { UseChoice::Value(n) => n, other => 0 } } \<close>

lemma \<open> use_block_binder = use_block_binder_plain \<close>
  unfolding use_block_binder_def use_block_binder_plain_def by (rule refl)

urust_expr use_block_namespaces
  \<open> { use UsePacket as Pick; use demo::value as Pick; let packet = Pick { sample: Pick() }; packet } \<close>

urust_expr use_block_namespaces_plain
  \<open> { let packet = UsePacket { sample: demo::value() }; packet } \<close>

lemma \<open> use_block_namespaces = use_block_namespaces_plain \<close>
  unfolding use_block_namespaces_def use_block_namespaces_plain_def by (rule refl)

urust_expr use_block_cast (x) \<open> { use demo::Short as LocalShort; x as LocalShort } \<close>

urust_expr use_block_cast_plain (x) \<open> { x as u16 } \<close>

lemma \<open> use_block_cast = use_block_cast_plain \<close>
  unfolding use_block_cast_def use_block_cast_plain_def by (rule refl)

urust_expr use_block_terminal (x)
  \<open> { let only = { use demo::value; }; let after = { x; use demo::value; }; (only, after) } \<close>

urust_expr use_block_terminal_plain (x) \<open> { let only = {}; let after = { x; }; (only, after) } \<close>

lemma \<open> use_block_terminal = use_block_terminal_plain \<close>
  unfolding use_block_terminal_def use_block_terminal_plain_def by (rule refl)

urust_expr use_implicit_body \<open> let first = body_inc(1); use demo::increment as body_inc; body_inc(first) \<close>

urust_expr use_implicit_body_plain \<open> let first = demo::increment(1); demo::increment(first) \<close>

lemma \<open> use_implicit_body = use_implicit_body_plain \<close>
  unfolding use_implicit_body_def use_implicit_body_plain_def by (rule refl)

urust_fn \<open> fn use_function_body(x: u32) -> u32 { use demo::increment as step; step(x) } \<close>

urust_fn \<open> fn use_function_body_plain(x: u32) -> u32 { demo::increment(x) } \<close>

lemma \<open> use_function_body = use_function_body_plain \<close>
  unfolding use_function_body_def use_function_body_plain_def by (rule refl)

urust_expr use_effect_order
  \<open>
    {
      use demo::value as unused_value;
      let first = \<epsilon>\<open> use_tick \<close>;
      use UseChoice::Value as UnusedPresent;
      let second = \<epsilon>\<open> use_tick \<close>;
      (first, second)
    }
  \<close>

urust_expr use_effect_order_plain
  \<open> { let first = \<epsilon>\<open> use_tick \<close>; let second = \<epsilon>\<open> use_tick \<close>; (first, second) } \<close>

lemma use_effect_order_plain: \<open> use_effect_order = use_effect_order_plain \<close>
  unfolding use_effect_order_def use_effect_order_plain_def by (rule refl)

lemma use_effect_order_evaluation:
  \<open> evaluate use_effect_order 0 = Success (0, 1, TNil) 2 \<close>
  by (simp add: use_effect_order_def use_tick_def micro_rust_simps evaluate_def get_def put_def
    literal_def Core_Expression.bind.simps bind_evaluate Let_def)

subsection\<open> Block rejections \<close>

urust_expr_rejects \<open> { use Left as Right; use Right as Left; 1 } \<close> \<open> cyclic imports \<close>

urust_expr_rejects \<open> { use MissingTarget as Unused; 1 } \<close> \<open> unknown import target "MissingTarget" \<close>

urust_expr_rejects \<open> { let ExistingName = 7u32; { use ExistingName as Captured; 1 } } \<close>
  \<open> unknown import target "ExistingName" \<close>

urust_expr_rejects \<open> |param| { use param as captured; 1 } \<close> \<open> unknown import target "param" \<close>

urust_expr_rejects \<open> { use demo::value; use demo::value; 1 } \<close> \<open> duplicate import "value" \<close>

urust_expr_rejects \<open> { use demo::WIDTH as w; w() } \<close> \<open> which cannot be used as a call \<close>

urust_expr_rejects \<open> (use demo::value; 1) \<close> \<open> use declarations require an enclosing block \<close>

urust_expr_rejects \<open> assert!(use demo::value; true) \<close> \<open> use declarations require an enclosing block \<close>

urust_expr_rejects \<open> UsePacket { sample: use demo::value; 1 } \<close> \<open> use declarations require an enclosing block \<close>

urust_expr_rejects \<open> match 1u32 { _ if use demo::value; true => 1, _ => 0 } \<close>
  \<open> use declarations require an enclosing block \<close>

context use_command_locale
begin

urust_expr_rejects \<open> { use use_command_parameter as fixed_alias; 1 } \<close>
  \<open> unknown import target "use_command_parameter" \<close>

end

section\<open> Rust block shadowing of lexical locals \<close>

text\<open>
As in Rust, the use items of a block take effect at its entry. A block import therefore shadows a
same-named local bound outside the block (an enclosing let, a function, closure or declaration
parameter, or a match, if-let, while-let, for or let-else binder) within that block, while a local
bound inside the block, even before the use item, shadows the import. Every local shadows chunk and
chunk aliases. Each definition is kernel-equal to its import-free or qualified counterpart.
\<close>

urust_expr use_shadow_outer_let
  \<open> { let pick = |x| x; let inside = { use demo::increment as pick; pick(1) }; let captured = { use demo::increment as pick; || pick(3) }; (inside, captured(), pick(2)) } \<close>

urust_expr use_shadow_outer_let_plain
  \<open> { let pick = |x| x; let inside = { demo::increment(1) }; let captured = { || demo::increment(3) }; (inside, captured(), pick(2)) } \<close>

lemma \<open> use_shadow_outer_let = use_shadow_outer_let_plain \<close>
  unfolding use_shadow_outer_let_def use_shadow_outer_let_plain_def by (rule refl)

urust_expr use_shadow_arguments (step, w) \<open> use demo::increment as step; use demo::WIDTH as w; (step(1), w) \<close>

urust_expr use_shadow_arguments_plain (step, w) \<open> (demo::increment(1), demo::WIDTH) \<close>

lemma \<open> use_shadow_arguments = use_shadow_arguments_plain \<close>
  unfolding use_shadow_arguments_def use_shadow_arguments_plain_def by (rule refl)

urust_fn \<open> fn use_shadow_parameter(step: u32) -> u32 { use demo::increment as step; step(1) } \<close>

urust_fn \<open> fn use_shadow_parameter_plain(step: u32) -> u32 { demo::increment(1) } \<close>

lemma \<open> use_shadow_parameter = use_shadow_parameter_plain \<close>
  unfolding use_shadow_parameter_def use_shadow_parameter_plain_def by (rule refl)

urust_expr use_shadow_binders (choice)
  \<open>
    {
      let closure = |pick| { use demo::increment as pick; pick(1) };
      let arm = match choice { UseChoice::Value(pick) => { use demo::increment as pick; pick(2) }, _ => 0 };
      let branch = if let UseChoice::Value(pick) = choice { use demo::increment as pick; pick(3) } else { 0 };
      for pick in 0u32..2 { use demo::increment as pick; pick(4); }
      (closure(7u32), arm, branch)
    }
  \<close>

urust_expr use_shadow_binders_plain (choice)
  \<open>
    {
      let closure = |pick| { demo::increment(1) };
      let arm = match choice { UseChoice::Value(pick) => { demo::increment(2) }, _ => 0 };
      let branch = if let UseChoice::Value(pick) = choice { demo::increment(3) } else { 0 };
      for pick in 0u32..2 { demo::increment(4); }
      (closure(7u32), arm, branch)
    }
  \<close>

lemma \<open> use_shadow_binders = use_shadow_binders_plain \<close>
  unfolding use_shadow_binders_def use_shadow_binders_plain_def by (rule refl)

urust_expr use_shadow_let_else (choice)
  \<open> { let UseChoice::Value(pick) = choice else { return 0; }; { use demo::increment as pick; pick(5) } } \<close>

urust_expr use_shadow_let_else_plain (choice)
  \<open> { let UseChoice::Value(pick) = choice else { return 0; }; { demo::increment(5) } } \<close>

lemma \<open> use_shadow_let_else = use_shadow_let_else_plain \<close>
  unfolding use_shadow_let_else_def use_shadow_let_else_plain_def by (rule refl)

urust_expr use_shadow_restored (pick) \<open> { let inside = { use demo::increment as pick; pick(1) }; (inside, pick) } \<close>

urust_expr use_shadow_restored_plain (pick) \<open> { let inside = { demo::increment(1) }; (inside, pick) } \<close>

lemma \<open> use_shadow_restored = use_shadow_restored_plain \<close>
  unfolding use_shadow_restored_def use_shadow_restored_plain_def by (rule refl)

urust_expr use_shadow_inner_locals
  \<open>
    {
      let before = { let pick = |x| x; use demo::increment as pick; pick(1) };
      let nested = { use demo::increment as pick; { let pick = |x| x; pick(2) } };
      let through = { use demo::increment as pick; let pick = |x| x; { use demo::value as unrelated; pick(3) } };
      let inner = { use demo::increment as pick; let pick = |x| x; ({ use use_increment as pick; pick(4) }, pick(6)) };
      let formal = { use demo::increment as pick; let f = |pick| pick; f(5) };
      (before, nested, through, inner, formal)
    }
  \<close>

urust_expr use_shadow_inner_locals_plain
  \<open>
    {
      let before = { let pick = |x| x; pick(1) };
      let nested = { { let pick = |x| x; pick(2) } };
      let through = { let pick = |x| x; { pick(3) } };
      let inner = { let pick = |x| x; ({ use_increment(4) }, pick(6)) };
      let formal = { let f = |pick| pick; f(5) };
      (before, nested, through, inner, formal)
    }
  \<close>

lemma \<open> use_shadow_inner_locals = use_shadow_inner_locals_plain \<close>
  unfolding use_shadow_inner_locals_def use_shadow_inner_locals_plain_def by (rule refl)

urust_expr use_shadow_endpoint_and_length (x)
  \<open> { let w = 0u32; let n = 1u64; { use demo::WIDTH as w; use demo::COUNT as n; (match x { 0..=w => 1u32, _ => 0 }, [0u8; n]) } } \<close>

urust_expr use_shadow_endpoint_and_length_plain (x)
  \<open> { let w = 0u32; let n = 1u64; { (match x { 0..=demo::WIDTH => 1u32, _ => 0 }, [0u8; demo::COUNT]) } } \<close>

lemma \<open> use_shadow_endpoint_and_length = use_shadow_endpoint_and_length_plain \<close>
  unfolding use_shadow_endpoint_and_length_def use_shadow_endpoint_and_length_plain_def by (rule refl)

urust_expr use_shadow_control_head_local \<open> { use demo::value as v; let v = true; if v {} } \<close>

urust_expr use_shadow_contexts (choice)
  \<open>
    {
      let pick = |x| x;
      let early = { let r = pick(1); use demo::increment as pick; r };
      #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let UseChoice::Value(bound) = choice { use demo::increment as bound; bound(2); }
      let guarded = match choice { UseChoice::Value(bound) if bound > 0 => { use demo::increment as bound; bound(3) }, _ => 0 };
      assert_eq!({ use demo::increment as pick; pick(4) }, pick(5));
      let initialized = { use demo::increment as pick; let pick = pick(6); pick };
      let packet = { let sample = 5u32; { use demo::WIDTH as sample; UsePacket { sample: sample } } };
      let deeper = { use demo::increment as pick; let f = |pick| { use demo::WIDTH as pick; pick }; f(7u32) };
      let UseChoice::Value(v) = choice else { use demo::increment as pick; return (pick(8), 0, 0, UsePacket { sample: 0 }, demo::WIDTH, 0); };
      (early, guarded, initialized, packet, deeper, pick(v))
    }
  \<close>

urust_expr use_shadow_contexts_plain (choice)
  \<open>
    {
      let pick = |x| x;
      let early = { let r = demo::increment(1); r };
      #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let UseChoice::Value(bound) = choice { demo::increment(2); }
      let guarded = match choice { UseChoice::Value(bound) if bound > 0 => { demo::increment(3) }, _ => 0 };
      assert_eq!({ demo::increment(4) }, pick(5));
      let initialized = { let pick = demo::increment(6); pick };
      let packet = { let sample = 5u32; { UsePacket { sample: demo::WIDTH } } };
      let deeper = { let f = |pick| { demo::WIDTH }; f(7u32) };
      let UseChoice::Value(v) = choice else { return (demo::increment(8), 0, 0, UsePacket { sample: 0 }, demo::WIDTH, 0); };
      (early, guarded, initialized, packet, deeper, pick(v))
    }
  \<close>

lemma \<open> use_shadow_contexts = use_shadow_contexts_plain \<close>
  unfolding use_shadow_contexts_def use_shadow_contexts_plain_def by (rule refl)

urust_expr use_shadow_implicit_closure (pick) \<open> use demo::increment as pick; let f = || pick(1); f() \<close>

urust_expr use_shadow_implicit_closure_plain (pick) \<open> let f = || demo::increment(1); f() \<close>

lemma \<open> use_shadow_implicit_closure = use_shadow_implicit_closure_plain \<close>
  unfolding use_shadow_implicit_closure_def use_shadow_implicit_closure_plain_def by (rule refl)

urust_expr use_shadow_rebound_argument (pick) \<open> { use demo::increment as pick; let pick = |x| x; pick(1) } \<close>

urust_expr use_shadow_rebound_argument_plain (pick) \<open> { let pick = |x| x; pick(1) } \<close>

lemma \<open> use_shadow_rebound_argument = use_shadow_rebound_argument_plain \<close>
  unfolding use_shadow_rebound_argument_def use_shadow_rebound_argument_plain_def by (rule refl)

urust_expr use_shadow_parameter_argument (use_shadow_parameter)
  \<open> (use_shadow_parameter, { use demo::WIDTH as use_shadow_parameter; use_shadow_parameter }) \<close>

urust_expr use_shadow_parameter_argument_plain (other) \<open> (other, { demo::WIDTH }) \<close>

lemma \<open> use_shadow_parameter_argument = use_shadow_parameter_argument_plain \<close>
  unfolding use_shadow_parameter_argument_def use_shadow_parameter_argument_plain_def by (rule refl)

locale use_shadow_locale =
  fixes use_shadow_fixed :: \<open> 32 word \<close>
begin

urust_fn \<open> fn use_shadow_locale_fn(x: u32) -> u32 { let y = x; { use demo::WIDTH as y; y } } \<close>
urust_fn \<open> fn use_shadow_locale_fn_plain(x: u32) -> u32 { let y = x; { demo::WIDTH } } \<close>
lemma \<open> use_shadow_locale_fn = use_shadow_locale_fn_plain \<close>
  unfolding use_shadow_locale_fn_def use_shadow_locale_fn_plain_def by (rule refl)

end

urust_expr_rejects \<open> |w| { use demo::WIDTH as w; w(1) } \<close> \<open> which cannot be used as a call \<close>

urust_expr_rejects \<open> { use demo::COUNT as n; let n = 1u64; [0u8; n] } \<close>
  \<open> array repeat length cannot use lexical local "n" \<close>

urust_expr_rejects \<open> { let v = true; { use demo::value as v; if v {} } } \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects \<open> use demo::value as v; if v {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects \<open> { let pick = 1u32; { use demo::increment as pick; pick } } \<close>
  \<open> which cannot be used as a value \<close>

urust_expr_rejects \<open> { let n = 1u64; { use demo::increment as n; [0u8; n] } } \<close>
  \<open> cannot be used as an array repeat length \<close>

section\<open> Review regressions \<close>

text\<open>
Regressions for the first independent review: struct heads, report transactions, the two-phase
batch operation, body visibility,
reserved keywords, scope collection and source conventions.
\<close>

subsection\<open> Struct heads stay in the type namespace \<close>

urust_expr use_struct_head_value_import \<open> { use demo::increment as UsePacket; UsePacket { sample: 2 } } \<close>

urust_expr use_struct_head_value_import_plain \<open> { UsePacket { sample: 2 } } \<close>

lemma \<open> use_struct_head_value_import = use_struct_head_value_import_plain \<close>
  unfolding use_struct_head_value_import_def use_struct_head_value_import_plain_def by (rule refl)

urust_expr use_struct_pattern_value_import (p)
  \<open> { use demo::WIDTH as UsePacket; match p { UsePacket { sample } => sample } } \<close>

urust_expr use_struct_pattern_value_import_plain (p) \<open> { match p { UsePacket { sample } => sample } } \<close>

lemma \<open> use_struct_pattern_value_import = use_struct_pattern_value_import_plain \<close>
  unfolding use_struct_pattern_value_import_def use_struct_pattern_value_import_plain_def
  by (rule refl)

text\<open>
Exact call-notation keys remain usable as struct-call heads when imported, as the existing struct
syntax accepts them, provided no Rust type resolves the head.
\<close>

urust_expr use_struct_call_notation \<open> ({ use demo::increment as IncrementHead; IncrementHead { x: 1 } }, { use demo::increment as inc; inc { y: 2 } }) \<close>

urust_expr use_struct_call_notation_plain \<open> (demo::increment { x: 1 }, demo::increment { y: 2 }) \<close>

lemma \<open> use_struct_call_notation = use_struct_call_notation_plain \<close>
  unfolding use_struct_call_notation_def use_struct_call_notation_plain_def by (rule refl)

subsection\<open> Body visibility and reserved keywords \<close>

urust_expr_rejects \<open> { pub(crate) use demo::value; 1 } \<close> \<open> visibility qualifiers (`pub use`) are not supported \<close>

urust_expr_rejects \<open> { pub(in demo) use demo::value; 1 } \<close> \<open> visibility qualifiers (`pub use`) are not supported \<close>

urust_expr_rejects \<open> { pub use demo::value; 1 } \<close> \<open> visibility qualifiers (`pub use`) are not supported \<close>

chapter\<open> Imports in source-ordered chunks \<close>

text\<open>
A \<open>urust\<close> chunk may contain complete Rust \<open>use\<close> items. The
imports of one chunk form one batch: it is validated before the first declaration, its aliases are
visible to every declaration of the chunk, including declarations written before the \<open>use\<close>
item, and no alias survives the command. Every declaration elaborates with the batch prepared for
its own member context, so a target that the chunk declares is available only to the members after
it. After the last declaration every target must resolve. Every generated definition below is
compared by kernel reflexivity with a fully qualified single-item control.
\<close>

section\<open> Aliases visible to earlier and later members \<close>

urust \<open>
  fn ChunkImportEarly(x: u32) -> u32 { step(x) }

  use demo::{increment as step, value as fetch, WIDTH as Width_Value};

  fn ChunkImportLate() -> u32 { step(fetch()) + Width_Value }
\<close>

urust_fn \<open> fn ChunkImportEarlyControl(x: u32) -> u32 { demo::increment(x) } \<close>

urust_fn \<open> fn ChunkImportLateControl() -> u32 { demo::increment(demo::value()) + demo::WIDTH } \<close>

lemma \<open> chunk_import_early = chunk_import_early_control \<close>
  unfolding chunk_import_early_def chunk_import_early_control_def by (rule refl)

lemma \<open> chunk_import_late = chunk_import_late_control \<close>
  unfolding chunk_import_late_def chunk_import_late_control_def by (rule refl)

section\<open> Importing an item declared earlier in the same chunk \<close>

text\<open>
A member declared by the chunk can be imported; the alias resolves for the members after that
declaration. The rejections in the audit section show the same alias unavailable before it.
\<close>

urust \<open>
  fn ChunkImportHelper(x: u32) -> u32 { x + 1 }

  use ChunkImportHelper as helper;

  fn ChunkImportCaller(x: u32) -> u32 { helper(helper(x)) }
\<close>

urust_fn \<open>
  fn ChunkImportCallerControl(x: u32) -> u32 { ChunkImportHelper(ChunkImportHelper(x)) }
\<close>

lemma \<open> chunk_import_caller = chunk_import_caller_control \<close>
  unfolding chunk_import_caller_def chunk_import_caller_control_def by (rule refl)

section\<open> Shadowing among registrations, chunk and body imports \<close>

text\<open>
A chunk alias shadows an existing call registration inside the chunk; a body import shadows the
chunk alias throughout its block, including before the body import, and only there. After the
command the call registration is visible again.
\<close>

micro_rust_notation (call) use_demo_value_impl ("chunk_import_pick")

urust \<open>
  fn ChunkImportShadowed(x: u32) -> u32 { chunk_import_pick(x) }

  fn ChunkImportBodyShadow() -> u32 {
    let outer = chunk_import_pick(1);
    let inner = { let early = chunk_import_pick(2); use use_increment as chunk_import_pick; early };
    outer + inner + chunk_import_pick(3)
  }

  use demo::increment as chunk_import_pick;
\<close>

urust_fn \<open> fn ChunkImportShadowedControl(x: u32) -> u32 { demo::increment(x) } \<close>

urust_fn \<open>
  fn ChunkImportBodyShadowControl() -> u32 {
    let outer = demo::increment(1);
    let inner = { let early = use_increment(2); early };
    outer + inner + demo::increment(3)
  }
\<close>

lemma \<open> chunk_import_shadowed = chunk_import_shadowed_control \<close>
  unfolding chunk_import_shadowed_def chunk_import_shadowed_control_def by (rule refl)

lemma \<open> chunk_import_body_shadow = chunk_import_body_shadow_control \<close>
  unfolding chunk_import_body_shadow_def chunk_import_body_shadow_control_def by (rule refl)

urust_expr chunk_import_registered_again \<open> chunk_import_pick() \<close>

urust_expr chunk_import_registered_again_control \<open> demo::value() \<close>

lemma \<open> chunk_import_registered_again = chunk_import_registered_again_control \<close>
  unfolding chunk_import_registered_again_def chunk_import_registered_again_control_def
  by (rule refl)

text\<open>
As for Rust module-level imports, member parameters shadow chunk aliases and outer call registrations, while a
body import shadows the parameters of its member. The controls use unimported parameter names.
\<close>

urust \<open>
  use demo::increment as chunk_shadow_pick;
  fn ChunkShadowParameter(chunk_shadow_pick: u32) -> u32 { chunk_shadow_pick }
  fn ChunkShadowBody(chunk_shadow_pick: u32) -> u32 {
    use use_increment as chunk_shadow_pick;
    chunk_shadow_pick(1)
  }
  fn ChunkShadowRegistered(chunk_import_pick: u32) -> u32 { chunk_import_pick }
  // A parameter also wins against a chunk alias whose target is declared later.
  fn ChunkShadowUnavailable(chunk_shadow_later: u32) -> u32 { chunk_shadow_later }
  use ChunkShadowLater as chunk_shadow_later;
  fn ChunkShadowLater(value: u32) -> u32 { value }
\<close>

urust_fn \<open> fn ChunkShadowParameterControl(other: u32) -> u32 { other } \<close>

urust_fn \<open> fn ChunkShadowBodyControl(other: u32) -> u32 { use_increment(1) } \<close>

lemma \<open> chunk_shadow_parameter = chunk_shadow_parameter_control \<close>
  unfolding chunk_shadow_parameter_def chunk_shadow_parameter_control_def by (rule refl)

lemma \<open> chunk_shadow_body = chunk_shadow_body_control \<close>
  unfolding chunk_shadow_body_def chunk_shadow_body_control_def by (rule refl)

lemma \<open> chunk_shadow_registered = chunk_shadow_parameter_control \<close>
  unfolding chunk_shadow_registered_def chunk_shadow_parameter_control_def by (rule refl)

lemma \<open> chunk_shadow_unavailable = chunk_shadow_parameter_control \<close>
  unfolding chunk_shadow_unavailable_def chunk_shadow_parameter_control_def by (rule refl)

text\<open>
A body binding that is unavailable in the value namespace, because its chunk alias names a value
declared later, never rejects when a local bound inside its block shadows it; a local bound at the
member level wins through an unrelated body import frame.
\<close>

urust_type "ChunkShadowPending" = \<open> nat \<close>

urust \<open>
  use ChunkShadowPending as chunk_shadow_pending;
  use demo::increment as chunk_shadow_pick;
  fn ChunkShadowPendingUser(x: u32) -> u32 {
    use chunk_shadow_pending as chunk_shadow_inner;
    let chunk_shadow_inner = x;
    chunk_shadow_inner
  }
  fn ChunkShadowPending(value: u32) -> u32 { value }
  fn ChunkShadowThrough(x: u32) -> u32 {
    let chunk_shadow_pick = x;
    { use demo::value as chunk_shadow_unrelated; chunk_shadow_pick }
  }
\<close>

urust_fn \<open> fn ChunkShadowLocalControl(x: u32) -> u32 { let y = x; y } \<close>

urust_fn \<open> fn ChunkShadowThroughControl(x: u32) -> u32 { let y = x; { y } } \<close>

lemma \<open> chunk_shadow_pending_user = chunk_shadow_local_control \<close>
  unfolding chunk_shadow_pending_user_def chunk_shadow_local_control_def by (rule refl)

lemma \<open> chunk_shadow_through = chunk_shadow_through_control \<close>
  unfolding chunk_shadow_through_def chunk_shadow_through_control_def by (rule refl)

section\<open> Same-spelling type and value aliases \<close>

urust \<open>
  use {UsePacket as ChunkImportPair, demo::value as ChunkImportPair};

  fn ChunkImportSpelling(packet: ChunkImportPair) -> u32 { ChunkImportPair() + packet.sample }
\<close>

urust_fn \<open>
  fn ChunkImportSpellingControl(packet: UsePacket) -> u32 { demo::value() + packet.sample }
\<close>

lemma \<open> chunk_import_spelling = chunk_import_spelling_control \<close>
  unfolding chunk_import_spelling_def chunk_import_spelling_control_def by (rule refl)

section\<open> Signatures, fields, calls, construction and patterns \<close>

urust \<open>
  struct ChunkImportHolder { choice: Choice, word: Word, tuple: Tuple1 }

  fn ChunkImportBuild(n: u32) -> ChunkImportHolder {
    ChunkImportHolder { choice: Present(n), word: n, tuple: Tuple1(n) }
  }

  use UseChoice::{self as Choice, Value as Present, Empty as Absent};
  use {UseTuple as Tuple1, demo::Width as Word};

  fn ChunkImportInspect(holder: ChunkImportHolder, fallback: Word) -> u32 {
    match holder.choice {
      Present(n) => n,
      Absent => fallback,
      Choice::Named { sample } => sample,
    }
  }

  fn ChunkImportUnwrap(tuple: Tuple1) -> u32 {
    match tuple { Tuple1(n) => n }
  }
\<close>

urust_datatype \<open>
  struct ChunkImportHolderControl { choice: UseChoice, word: demo::Width, tuple: UseTuple }
\<close>

urust_fn \<open>
  fn ChunkImportBuildControl(n: u32) -> ChunkImportHolder {
    ChunkImportHolder { choice: UseChoice::Value(n), word: n, tuple: UseTuple(n) }
  }
\<close>

urust_fn \<open>
  fn ChunkImportInspectControl(holder: ChunkImportHolder, fallback: demo::Width) -> u32 {
    match holder.choice {
      UseChoice::Value(n) => n,
      UseChoice::Empty => fallback,
      UseChoice::Named { sample } => sample,
    }
  }
\<close>

urust_fn \<open> fn ChunkImportUnwrapControl(tuple: UseTuple) -> u32 { match tuple { UseTuple(n) => n } } \<close>

lemma \<open> chunk_import_build = chunk_import_build_control \<close>
  unfolding chunk_import_build_def chunk_import_build_control_def by (rule refl)

lemma \<open> chunk_import_inspect = chunk_import_inspect_control \<close>
  unfolding chunk_import_inspect_def chunk_import_inspect_control_def by (rule refl)

lemma \<open> chunk_import_unwrap = chunk_import_unwrap_control \<close>
  unfolding chunk_import_unwrap_def chunk_import_unwrap_control_def by (rule refl)

section\<open> Imports in a locale target \<close>

locale chunk_import_locale =
  fixes chunk_import_param :: nat
begin

urust \<open>
  use demo::increment as local_step;
  fn ChunkImportLocal(x: u32) -> u32 { local_step(x) }
\<close>

urust_fn \<open> fn ChunkImportLocalControl(x: u32) -> u32 { demo::increment(x) } \<close>

lemma \<open> chunk_import_local = chunk_import_local_control \<close>
  unfolding chunk_import_local_def chunk_import_local_control_def by (rule refl)

end

section\<open> Alias absence after the command \<close>

text\<open> An import-only chunk validates and resolves its imports and declares nothing. \<close>

urust \<open> use demo::{value as only_value, increment}; \<close>

section\<open> Datatype selector naming in annotations \<close>

text\<open>
A member's \<omega> annotation carries \<open>unprefixed_selectors\<close> and qualified payload rename keys
exactly as the single-item datatype command does.
\<close>

urust \<open>
  \<omega>\<open>unprefixed_selectors, hol_names = ["selectorNameChunkTotal" \<rightarrow> \<open>selector_name_chunk_sum\<close>]\<close>
  struct SelectorNameChunkTally { selectorNameChunkCount: u32, selectorNameChunkTotal: u64 }

  \<omega>\<open>backend = hol, hol_names = ["Filled.0" \<rightarrow> \<open>selector_name_chunk_filled\<close>]\<close>
  enum SelectorNameChunkSlot { Hollow, Filled(u32) }

  fn SelectorNameChunkRead(tally: SelectorNameChunkTally) -> u32 { tally.selectorNameChunkCount }
\<close>

thm selector_name_chunk_tally_selector_name_chunk_count_lens_valid

lemma
  \<open>selector_name_chunk_count (make_selector_name_chunk_tally c t) = c\<close>
  \<open>selector_name_chunk_sum (make_selector_name_chunk_tally c t) = t\<close>
  \<open>selector_name_chunk_filled (Filled n) = n\<close>
  by simp_all

urust_fn \<open>
  fn SelectorNameChunkReadControl(tally: SelectorNameChunkTally) -> u32 {
    tally.selectorNameChunkCount
  }
\<close>

lemma \<open> selector_name_chunk_read = selector_name_chunk_read_control \<close>
  unfolding selector_name_chunk_read_def selector_name_chunk_read_control_def by (rule refl)

end
