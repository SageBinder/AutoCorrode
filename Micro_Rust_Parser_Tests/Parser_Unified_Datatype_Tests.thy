theory Parser_Unified_Datatype_Tests
  imports Parser_Test_Utils
begin

section\<open> Generic declarations and backend selection \<close>

declare [[urust_pp_test = true, urust_pretty = false, urust_verbosity = 0]]

urust_datatype \<open> struct Buffer<T, const N: usize> { values: [T; N] } \<close>
urust_datatype \<open> struct Envelope<T, const N: usize, P> { buffer: Buffer<T, N> } \<close>
urust_datatype \<open> struct GenericUnit<T, U, const N: usize>; \<close>
urust_datatype \<open> struct GenericTuple<T, U, const N: usize>(u32); \<close>
urust_datatype \<open> struct EmptyNamed<T> {} \<close>
urust_datatype \<open> struct EmptyTuple<T>(); \<close>
urust_datatype [parameters = ["T" \<rightarrow> "'element::ord"]] \<open>
  struct SortedHint<T>;
\<close>

\<comment>\<open>RUST-CHANGE: this proof-source mirror omits a PhantomData field and its pure
initializer/pattern slot. The original type parameter is retained. Automatic field handling is
not requested; effectful initializers would need explicit effect-preserving source adaptation.\<close>
urust_datatype \<open> struct TaggedAddress<T> { address: u64 } \<close>

urust_type "Sized<'a, const 'n>" = \<open>('a, 'n::len) array\<close>
urust_datatype \<open> struct MappedBuffer<T, const N: usize> { values: Sized<T, N> } \<close>
urust_type_alias \<open> type ConcreteBuffer = Buffer<u8, 0x10>; \<close>
urust_type_alias \<open> type ForwardBuffer<T, const N: usize> = Buffer<T, N>; \<close>
urust_type_alias \<open> type UnusedWidth<const N: usize> = u8; \<close>
urust_datatype [parameters = ["N" \<rightarrow> "'length::len"]] \<open>
  struct IndirectBuffer<T, const N: usize> { inner: ForwardBuffer<T, N> }
\<close>

urust_datatype [parameters = ["T" \<rightarrow> "'element", "P" \<rightarrow> "'tag"]] \<open>
  enum Choice<T, P> { Empty, Data(T), Named { value: T, active: bool } }
\<close>
urust_datatype \<open> enum Ordinary<T, P, const N: usize> { One, Two, Three } \<close>
urust_datatype [backend = hol] \<open> enum NativeChoice<T, P> { NativeEmpty, NativeData(T) } \<close>
urust_datatype [backend = "enum"] \<open> enum Single<T, P> { Only(T) } \<close>
urust_datatype \<open> #[repr(u8)] enum Status<T, P> { Idle, Ready = 7, Busy } \<close>
urust_datatype [backend = "simple_word_enum", word_width = 16,
  plugins = (plugins only: word_conversion)] \<open>
  enum ExplicitWord { Zero, Gap = 0xff, Next }
\<close>
urust_datatype [word_width = 8] \<open> enum Boundary { Min = 0, Max = 255 } \<close>
urust_datatype [word_width = 8, renames = ["On" \<rightarrow> "ModelOn"]] \<open>
  enum RenamedWord<T, const N: usize> { Off, On = 3 }
\<close>
urust_datatype [word_width = 8] model_flags \<open>
  enum SourceFlags<T, P> { FlagOff, FlagOn = 5 }
\<close>
urust_datatype [renames = ["Wrapped" \<rightarrow> "ModelWrapped"]] \<open>
  enum RenamedPayload<T, P> { Wrapped { value: T } }
\<close>
urust_datatype [parameters = ["T" \<rightarrow> "'a", "P" \<rightarrow> "'b"]] \<open>
  enum ParameterNames<T, P> { ParameterValue(T), ParameterEmpty }
\<close>
urust_datatype \<open>
  enum EmptyShapes<T, const N: usize> { EmptyUnit, EmptyPositional(), EmptyFields {} }
\<close>
urust_datatype [backend = hol] \<open>
  enum NativeShapes<T, const N: usize> { NativeUnit, NativePositional(T), NativeFields { item: T } }
\<close>
urust_datatype [word_width = 8] \<open>
  enum WordShapes<T, const N: usize> { WordUnit, WordPositional(), WordFields {} }
\<close>

lemma buffer_selector: \<open>buffer_values (make_buffer xs) = xs\<close> by simp
lemma tagged_selector: \<open>tagged_address_address (make_tagged_address n) = n\<close> by simp
lemma word_gaps: \<open>explicit_word_to_u16_pure Gap = 255\<close>
  \<open>explicit_word_to_u16_pure Next = 256\<close>
  by (simp_all add: explicit_word_to_u16_pure_alt explicit_word_rep_defs)

urust_expr constructed_tag \<open> TaggedAddress::<u8> { address: 5u64 } \<close>
urust_expr constructed_fixed_array \<open>
  Buffer::<u8, 4> { values: \<llangle>array_constant (0 :: 8 word)\<rrangle> }
\<close>
urust_expr constructed_tuple \<open> GenericTuple::<u8, u16, 0>(3u32) \<close>
urust_expr unused_unit \<open> GenericUnit::<u8, u16, 0> \<close>
urust_expr empty_named_value \<open> EmptyNamed::<u8> {} \<close>
urust_expr empty_tuple_value \<open> EmptyTuple::<u8>() \<close>
urust_expr word_value \<open> Status::<u8, u16>::Ready \<close>
urust_expr word_conversion \<open> Status::to_u8(Status::<u8, u16>::Busy) \<close>
urust_expr renamed_word_value \<open> RenamedWord::<u8, 0>::On \<close>
urust_expr renamed_word_conversion \<open> RenamedWord::to_u8(RenamedWord::<u8, 0>::On) \<close>
urust_expr explicit_binding_conversion \<open> SourceFlags::to_u8(SourceFlags::<u8, u16>::FlagOn) \<close>
urust_expr renamed_payload_value \<open> RenamedPayload::<u32, u8>::Wrapped { value: 7u32 } \<close>
urust_expr named_choice \<open> Choice::<u32, u8>::Named { active: true, value: 3u32 } \<close>
urust_expr mixed_match \<open>
  match Choice::<u32, u8>::Data(3u32) {
    Choice::Empty => 0u32,
    Choice::Data(n) => n,
    Choice::Named { value, active: _ } => value,
  }
\<close>
urust_expr typed_pattern \<open>
  match Choice::<u32, u8>::Data(3u32) { Choice::<u32, u8>::Data(value) => value, _ => 0u32 }
\<close>
urust_expr parameter_names_match \<open>
  match ParameterNames::<u8, u16>::ParameterValue(1u8) {
    ParameterNames::ParameterValue(value) => value,
    ParameterNames::ParameterEmpty => 0u8,
  }
\<close>
urust_expr word_match \<open>
  match Status::<u8, u16>::Ready { Status::Idle => 0u8, Status::Ready => 7u8, Status::Busy => 8u8 }
\<close>
urust_expr empty_shape_match \<open>
  match (EmptyShapes::<u8, 0>::EmptyFields {}) {
    EmptyShapes::EmptyUnit => 0u8,
    EmptyShapes::EmptyPositional() => 1u8,
    EmptyShapes::EmptyFields {} => 2u8,
  }
\<close>
urust_expr native_shape_match \<open>
  match (NativeShapes::<u8, 0>::NativeFields { item: 3u8 }) {
    NativeShapes::NativeUnit => 0u8,
    NativeShapes::NativePositional(item) => item,
    NativeShapes::NativeFields { item } => item,
  }
\<close>
urust_expr word_shape_match \<open>
  match WordShapes::<u8, 0>::WordPositional() {
    WordShapes::WordUnit => 0u8,
    WordShapes::WordPositional() => 1u8,
    WordShapes::WordFields {} => 2u8,
  }
\<close>
urust_fn tagged_field \<open> fn tagged_field(x: TaggedAddress<u8>) -> u64 { x.address } \<close>
urust_fn buffer_identity \<open> fn buffer_identity(x: Buffer<u8, 4>) -> Buffer<u8, 4> { x } \<close>
urust_fn buffer_field \<open> fn buffer_field(x: Buffer<u8, 4>) -> [u8; 4] { x.values } \<close>
urust_fn forwarded_signature \<open>
  fn forwarded_signature(x: ForwardBuffer<u8, 0x10>) -> Buffer<u8, 16> { x }
\<close>
urust_fn unused_const_alias \<open>
  fn unused_const_alias(x: UnusedWidth<0>) -> UnusedWidth<16> { x }
\<close>

urust_type "Maybe<'a>" = \<open>'a option\<close>
urust_type "LooseConst<const 'n>" = \<open>'n option\<close>
urust_expr nested_type_constructor \<open> Choice::<Maybe<u8>, u16>::Data(Some(2u8)) \<close>
urust_expr escaped_type_constructor \<open>
  Choice::<\<tau>\<open>nat\<close>, u8>::Data(\<llangle>3 :: nat\<rrangle>)
\<close>
urust_expr escaped_length_constructor (xs) \<open> Buffer::<u8, \<tau>\<open>4\<close>> { values: xs } \<close>
urust_expr underscore_length (xs) \<open> Buffer::<u8, 1_6> { values: xs } \<close>
urust_expr_rejects \<open> Choice::<u8, u16>::Data(5u16) \<close> \<open>Type unification failed\<close>

urust_datatype \<open>
  struct GenericPointer<T, P, const N: usize> { pointer: *const T, values: Buffer<T, N> }
\<close>
urust_datatype \<open> enum PointerPayload<T, P> { Raw(*const T), PointerEmpty } \<close>
urust_fn generic_pointer_identity \<open>
  fn generic_pointer_identity(x: GenericPointer<u8, u16, 4>) -> GenericPointer<u8, u16, 4> { x }
\<close>
urust_fn pointer_payload \<open>
  fn pointer_payload(pointer: *const u8) -> PointerPayload<u8, u16> { PointerPayload::<u8, u16>::Raw(pointer) }
\<close>

ML_val \<open>
local
  val thy = \<^theory>
  val ctxt = \<^context>
  fun require message condition = if condition then () else error message
  fun mapping name = the (URust_Type_Mappings.lookup ctxt name)
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun command label text =
    Outer_Syntax.parse_text thy (K thy)
      (Position.make0 1 1 0 "" label "" |> Position.copy_id (Position.thread_data ())) text
    |> (fn transitions => fold (Toplevel.command_exception false)
      transitions (Toplevel.make_state (SOME thy)))
  fun rejection (label, options, source, expected) =
    (case Exn.result (fn () => command label
      ("urust_datatype " ^ options ^ " " ^ cartouche source)) () of
      Exn.Res _ => error ("invalid datatype accepted: " ^ label)
    | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn
      else require ("wrong diagnostic for " ^ label ^ ": " ^ Runtime.exn_message exn)
        (String.isSubstring expected (Runtime.exn_message exn)))
  val _ = List.app rejection
    [("word-no-width", "[backend = \"simple_word_enum\"]", "enum Invalid { First, Second }", "explicit width"),
     ("word-payload", "[backend = \"simple_word_enum\", word_width = 8]", "enum Invalid { Stored(u8) }", "no payload"),
     ("struct-enum", "[backend = \"enum\"]", "struct Invalid;", "require an enum"),
     ("width-conflict", "[word_width = 16]", "#[repr(u8)] enum Invalid { First }", "conflicts"),
     ("width-hol", "[backend = hol, word_width = 8]", "enum Invalid { First }", "requires"),
     ("unsupported-repr", "", "#[repr(i8)] enum Invalid { First }", "unsupported repr"),
     ("usize-repr", "", "#[repr(usize)] enum Invalid { First }", "unsupported repr"),
     ("explicit-overflow", "[word_width = 8]", "enum Invalid { First = 256 }", "out of range"),
     ("implicit-overflow", "[word_width = 8]", "enum Invalid { First = 255, Second }", "out of range"),
     ("duplicate-discriminant", "[word_width = 8]", "enum Invalid { First = 7, Second = 7 }", "duplicate discriminant"),
     ("recursive-generic", "", "struct Invalid<T>(Invalid<T>);", "recursive"),
     ("const-kind", "", "struct Invalid<T> { value: Buffer<u8, T> }", "type parameters used as const"),
     ("type-kind", "", "struct Invalid<const N: usize> { value: Maybe<N> }", "const parameters used as type"),
     ("const-minimum-sort", "", "struct Invalid { value: LooseConst<\<tau>\<open>nat\<close>> }", "does not satisfy sort"),
     ("const-field", "", "struct Invalid<const N: usize> { value: N }", "const parameters used as field"),
     ("zero-array", "", "struct Invalid { value: [u8; 0] }", "does not satisfy sort"),
     ("override-sort", "[parameters = [\"N\" \<rightarrow> \"'n::len0\"]]",
       "struct Invalid<const N: usize> { value: [u8; N] }", "does not satisfy inferred sort"),
     ("override-unknown", "[parameters = [\"X\" \<rightarrow> \"'x\"]]", "struct Invalid<T>;", "unknown parameter override"),
     ("override-duplicate-name", "[parameters = [\"T\" \<rightarrow> \"'x\", \"U\" \<rightarrow> \"'x\"]]",
       "struct Invalid<T, U>;", "HOL parameter names must be distinct"),
     ("automatic-marker", "", "struct Invalid<T> { value: PhantomData<T> }", "automatic PhantomData field handling is deferred"),
     ("qualified-marker", "", "struct Invalid<T> { value: core::marker::PhantomData<T> }", "automatic PhantomData field handling is deferred"),
     ("word-marker-payload", "[word_width = 8]", "enum Invalid<T> { Value(PhantomData<T>) }", "automatic PhantomData field handling is deferred")]
  val _ = List.app (fn (name, count) => require ("declared parameters were dropped: " ^ name)
    (length (URust_Type_Mappings.entry_parameter_sorts (mapping name)) = count))
    [("GenericUnit", 3), ("GenericTuple", 3), ("EmptyNamed", 1), ("EmptyTuple", 1),
     ("Ordinary", 3), ("NativeChoice", 2), ("Single", 2), ("Status", 2), ("RenamedWord", 2)]
  val _ = List.app (fn name => require ("unused shape parameter was dropped: " ^ name)
    (URust_Type_Mappings.entry_parameter_sorts (mapping name) = [\<^sort>\<open>type\<close>, \<^sort>\<open>len0\<close>]))
    ["EmptyShapes", "NativeShapes", "WordShapes"]
  val _ = require "const length sort was not inferred"
    (nth (URust_Type_Mappings.entry_parameter_sorts (mapping "Buffer")) 1 = \<^sort>\<open>len\<close>)
  val _ = require "unused word const parameter lost len0"
    (URust_Type_Mappings.entry_parameter_sorts (mapping "RenamedWord") = [\<^sort>\<open>type\<close>, \<^sort>\<open>len0\<close>])
  val _ = require "unused alias const parameter was dropped"
    (URust_Type_Mappings.entry_parameter_sorts (mapping "UnusedWidth") = [\<^sort>\<open>len0\<close>])
  val _ = require "explicit unused sorted parameter introduced an implicit memory parameter"
    (URust_Type_Mappings.entry_parameter_sorts (mapping "SortedHint") = [\<^sort>\<open>ord\<close>] andalso
     null (URust_Type_Mappings.entry_backend_parameter_sorts (mapping "SortedHint")))
  val _ = require "unused parameters acquired equality constraints"
    (Sign.of_sort thy (\<^typ>\<open>(nat \<Rightarrow> nat, nat \<Rightarrow> nat, 0) ordinary\<close>, \<^sort>\<open>equal\<close>))
  val _ = require "ordinary enum used a HOL datatype"
    (is_none (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>ordinary\<close>))
  val _ = require "HOL backend lost native constructor metadata"
    (is_some (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>native_choice\<close>))
  val _ = require "repr enum did not use a word typedef"
    (not (null (Typedef.get_info ctxt \<^type_name>\<open>status\<close>)))
  val _ = require "source and memory parameters were conflated"
    (length (URust_Type_Mappings.entry_parameter_sorts (mapping "GenericPointer")) = 3 andalso
     length (URust_Type_Mappings.entry_backend_parameter_sorts (mapping "GenericPointer")) = 2)
  val _ = require "temporary overloaded setting escaped"
    (not (Config.get ctxt Typedef.overloaded) andalso not (Config.get_global thy Typedef.overloaded))
  val _ = require "duplicate word notation registration"
    (null (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral "Status::Ready"))
  val recovered = command "backend-recovery"
    ("urust_datatype [word_width = 8] " ^ cartouche "enum Invalid { Recovered = 255 }") |> Toplevel.context_of
  val _ = require "failed declarations left registry state"
    (is_some (URust_Type_Mappings.lookup recovered "Invalid") andalso is_none (URust_Type_Mappings.lookup ctxt "Invalid"))
in val _ = writeln "unified generic datatype probes passed" end
\<close>

section\<open> Ordinary explicit singleton modelling \<close>

text\<open>No builtin mapping or field policy is installed for PhantomData. An ordinary HOL datatype,
manual type mapping and literal notation can model it as a stored singleton field.\<close>
datatype 'a explicit_token = ExplicitToken
urust_type "PhantomData<'a>" = \<open>'a explicit_token\<close>
urust_notation (literal) ExplicitToken ("PhantomData")
urust_datatype \<open> struct ManualCarrier<T> { value: u8, token: PhantomData<T> } \<close>
urust_expr manual_carrier \<open> ManualCarrier::<u8> { token: PhantomData, value: 5u8 } \<close>
urust_expr stored_token_abort \<open>
  ManualCarrier::<u8> { token: { assert!(false); PhantomData }, value: 5u8 }
\<close>
urust_expr stored_token_order \<open>
  ManualCarrier::<u8> {
    token: { \<epsilon>\<open>put (\<lambda>_::nat. 1)\<close>; PhantomData },
    value: { \<epsilon>\<open>put (\<lambda>_::nat. 2)\<close>; 5u8 },
  }
\<close>
lemma stored_token_abort_preserved: \<open>stored_token_abort = abort AssertionFailed\<close>
  by (simp add: stored_token_abort_def micro_rust_simps assert_def assert_val_def
    sequence_def false_def literal_def abort_def Core_Expression.bind.simps evaluate_def)
lemma stored_token_source_order:
  \<open>evaluate stored_token_order 0 = Success (make_manual_carrier 5 ExplicitToken) 2\<close>
  by (simp add: stored_token_order_def micro_rust_simps sequence_def evaluate_def
    literal_def put_def Core_Expression.bind.simps)
urust_expr_rejects \<open> ManualCarrier::<u8> { value: 5u8 } \<close> \<open>missing field "token"\<close>
urust_expr_rejects \<open>
  ManualCarrier::<u8> { value: 5u8, token: PhantomData, extra: { assert!(false); 0u8 } }
\<close> \<open>unknown field "extra"\<close>
urust_expr_rejects \<open>
  ManualCarrier::<u8> { value: 5u8, token: PhantomData, token: PhantomData }
\<close> \<open>duplicate struct initializer\<close>
urust_fn manual_token \<open> fn manual_token(x: ManualCarrier<u8>) -> PhantomData<u8> { x.token } \<close>
urust_fn manual_pattern \<open>
  fn manual_pattern(x: ManualCarrier<u8>) -> PhantomData<u8> { match x { ManualCarrier { value: _, token } => token } }
\<close>
urust_datatype \<open> #[repr(u8)] enum MappedStatus<T> { MappedReady(PhantomData<T>) = 7, MappedBusy } \<close>
ML_val \<open>
  val ctxt = \<^context>
  val carrier = the (URust_Item_Scope.lookup_constructor ctxt "ManualCarrier")
  val _ = if length (binder_types (fastype_of (URust_Item_Scope.constructor_scheme carrier))) = 2
    andalso length (URust_Item_Scope.constructor_fields carrier) = 2 then ()
    else error "manually mapped singleton field was discarded"
  val _ = if is_none (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>mapped_status\<close>) andalso
    length (binder_types (fastype_of (URust_Item_Scope.constructor_scheme
      (the (URust_Item_Scope.lookup_constructor ctxt "MappedStatus::MappedReady"))))) = 1
    then () else error "a stored singleton payload made an enum eligible for word representation"
  val source = Parser_Lex_Util.text_source "enum StoredPayload<T> { Stored(PhantomData<T>) }"
  val result = Exn.result (URust_Datatype.define
    {source = source, explicit_binding = NONE, interactive = false, verbosity = 0,
     pp_test = true, pretty = false, register_notation = true, renames = [],
     backend = "simple_word_enum", word_width = SOME 8, parameters = [], plugins = K Plugin_Name.default_filter})
      (Named_Target.theory_init \<^theory>)
  val _ = case result of Exn.Res _ => error "explicit word backend discarded a stored singleton payload"
    | Exn.Exn exn => if String.isSubstring "no payload" (Runtime.exn_message exn) then ()
      else Exn.reraise exn
\<close>

section\<open> Generic manifests and read-only pretty replay \<close>

ML_val \<open>
local
  val thy = \<^theory>
  fun require message condition = if condition then () else error message
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun probe (rust_name, backend_options, declaration, backend, count) =
    let
      val label = "unified-replay-" ^ rust_name
      val output = Synchronized.var label ([]: string list)
      fun collect chunks =
        if Position.file_of (Position.thread_data ()) = SOME label
        then Synchronized.change output (append chunks) else ()
      fun run () =
        Outer_Syntax.parse_text thy (K thy) (Position.line_file 1 label)
          ("urust_datatype [pretty, pp_test, verbosity = 2" ^ backend_options ^ "] " ^
            cartouche declaration)
        |> (fn transitions => fold (Toplevel.command_exception true)
          transitions (Toplevel.make_state (SOME thy)))
      val state = Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.writeln_fn collect run ())
      val ctxt = Toplevel.context_of state
      val plain = XML.content_of (YXML.parse_body (implode (Synchronized.value output)))
        |> Symbol.explode |> filter_out Symbol.is_control |> implode
      val _ = List.app (fn text => require ("generic manifest omitted " ^ quote text)
        (String.isSubstring text plain))
        ["backend: " ^ backend, "T ->", "P ->", "const N ->", "len0",
         "normalized uRust declaration", "normalized generated declaration"]
      val mapping = the (URust_Type_Mappings.lookup ctxt rust_name)
      val _ = require "pretty replay changed the complete parameter scheme"
        (length (URust_Type_Mappings.entry_parameter_sorts mapping) = 3 andalso
         length (URust_Type_Mappings.entry_backend_parameter_sorts mapping) = count)
      val _ = require "pretty replay registered the item twice"
        (length (URust_Item_Scope.dump_types ctxt) = length (URust_Item_Scope.dump_types \<^context>) + 1)
      val _ = require "pretty replay registered constructors twice"
        (length (URust_Item_Scope.dump_constructors ctxt) =
          length (URust_Item_Scope.dump_constructors \<^context>) + (if backend = "hol" then 1 else 2))
      val generated = String.fields (fn c => c = #"\n") plain
        |> drop_prefix (not o String.isPrefix "normalized generated declaration")
        |> space_implode "\n"
      val _ = require "verbose output lost unused HOL parameters"
        (String.isSubstring "'p" generated andalso String.isSubstring "'n" generated)
    in () end
  val _ = List.app probe
    [("ReplayRecord", "", "struct ReplayRecord<T, P, const N: usize> { value: T, pointer: *const T }", "hol", 2),
     ("ReplayCustom", "", "enum ReplayCustom<T, P, const N: usize> { ReplayValue(T), ReplayEmpty }", "enum", 0),
     ("ReplayHol", ", backend = hol", "struct ReplayHol<T, P, const N: usize>(T);", "hol", 0),
     ("ReplayWord", ", word_width = 8", "enum ReplayWord<T, P, const N: usize> { ReplayOff, ReplayOn = 9 }", "simple_word_enum", 0)]
in val _ = writeln "generic manifests and read-only pretty replay passed" end
\<close>

locale unified_declaration_scope = fixes scope_marker :: nat
begin
urust_datatype \<open> enum LocalChoice<T, P> { LocalValue(T), LocalEmpty } \<close>
urust_datatype [word_width = 8] \<open> enum LocalWord<T> { LocalOff, LocalOn = 9 } \<close>
urust_datatype \<open> struct LocalTagged<T> { value: u8 } \<close>
urust_expr local_choice \<open> LocalChoice::<u8, u16>::LocalValue(4u8) \<close>
urust_expr local_word \<open> LocalWord::<u16>::LocalOn \<close>
urust_fn local_field \<open> fn local_field(x: LocalTagged<u8>) -> u8 { x.value } \<close>
end

end
