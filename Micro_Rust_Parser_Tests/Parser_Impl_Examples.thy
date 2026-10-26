(* Readable examples of inherent impl blocks in urust chunks. The ML audits are in
   Parser_Impl_ML_Tests. *)

theory Parser_Impl_Examples
  imports
    Parser_Chunk_Use_Examples
begin

declare [[urust_pp_test = true, urust_pretty = false, urust_verbosity = 0, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

chapter\<open> Impl block parsing \<close>

text\<open>
An inherent impl block is a member of a \<open>urust\<close> chunk, such as
\<open>impl Counter { fn get(self) -> u32 { self.value } }\<close>. Its header is \<open>impl PATH {\<close>,
where the target path may carry concrete or HOL-escaped generic arguments, and its members are
complete \<open>fn\<close> items, each optionally preceded by an annotation on its own line. The first
parameter of a member may be a receiver shorthand: \<open>self\<close>, \<open>mut self\<close>, \<open>&self\<close>
or \<open>&mut self\<close>, the references optionally with a lifetime. The syntax, its source positions
and printing are audited in \<open>Parser_Impl_ML_Tests\<close>; the chapters "Impl block declarations"
and "Impl block resolution" below show elaboration.
\<close>

section\<open> Impl blocks are not expressions \<close>

text\<open>
An impl block outside a chunk is rejected at its \<open>impl\<close> keyword, in an expression and inside
a block body alike. Like the other item rejections, it applies to input that parses completely.
\<close>

urust_expr_rejects
  \<open> impl Counter {} \<close>
  \<open> uRust impl declarations are not expressions; use a urust chunk \<close>

urust_expr_rejects
  \<open> { impl Counter { fn get(self) -> u32 { 0 } }; 1 } \<close>
  \<open> uRust impl declarations are not expressions; use a urust chunk \<close>

urust_expr_rejects
  \<open> let value = 1; impl Counter {} \<close>
  \<open> uRust impl declarations are not expressions; use a urust chunk \<close>

urust_expr_rejects
  \<open> if true { impl Counter {} } else { () } \<close>
  \<open> uRust impl declarations are not expressions; use a urust chunk \<close>

chapter\<open> Impl block declarations \<close>

text\<open>
Every member of an impl block is declared exactly as the equivalent \<open>urust_fn\<close> with the
member's HOL name and a typed receiver, and registers its associated path \<open>Type::f\<close>. A member
whose first parameter is a \<open>self\<close> receiver additionally registers a method entry under its
bare name. \<open>Self\<close> names the target type in every type position of a member. The default HOL
binding is the snake case of the target's final written segment, an underscore, and the snake case
of the member name; an \<open>\<omega>\<close> \<open>name\<close> on the member overrides it.
\<close>

section\<open> Members and their typed equivalents \<close>

urust \<open>
  struct Counter { value: u32 }

  impl Counter {
    fn new() -> Self { Counter { value: 0_u32 } }

    fn with_value(value: u32) -> Counter { Counter { value: value } }

    fn get(self) -> u32 { self.value }

    fn plus(self, step: u32) -> u32 { self.value + step }

    fn merge(self, other: Self) -> Self { Counter { value: self.value + other.value } }

    fn split(self) -> (Self, u32) { (self, self.value) }
  }
\<close>

urust \<open>
  \<omega>\<open>name = "control_counter_new", register_notation = false\<close>
  fn new() -> Counter { Counter { value: 0_u32 } }

  \<omega>\<open>name = "control_counter_with_value", register_notation = false\<close>
  fn with_value(value: u32) -> Counter { Counter { value: value } }

  \<omega>\<open>name = "control_counter_get", register_notation = false\<close>
  fn get(self: Counter) -> u32 { self.value }

  \<omega>\<open>name = "control_counter_plus", register_notation = false\<close>
  fn plus(self: Counter, step: u32) -> u32 { self.value + step }

  \<omega>\<open>name = "control_counter_merge", register_notation = false\<close>
  fn merge(self: Counter, other: Counter) -> Counter {
    Counter { value: self.value + other.value }
  }

  \<omega>\<open>name = "control_counter_split", register_notation = false\<close>
  fn split(self: Counter) -> (Counter, u32) { (self, self.value) }
\<close>

lemma counter_members_match_controls:
  shows \<open>counter_new = control_counter_new\<close>
    and \<open>counter_with_value = control_counter_with_value\<close>
    and \<open>counter_get = control_counter_get\<close>
    and \<open>counter_plus = control_counter_plus\<close>
    and \<open>counter_merge = control_counter_merge\<close>
    and \<open>counter_split = control_counter_split\<close>
  unfolding counter_new_def control_counter_new_def counter_with_value_def
    control_counter_with_value_def counter_get_def control_counter_get_def counter_plus_def
    control_counter_plus_def counter_merge_def control_counter_merge_def counter_split_def
    control_counter_split_def
  by (rule refl)+

section\<open> Receivers \<close>

text\<open>
Each receiver shorthand is its typed spelling: \<open>self\<close> is \<open>self: Self\<close>, \<open>mut self\<close> is
\<open>mut self: Self\<close>, and \<open>&mut self\<close> and \<open>&'a mut self\<close> are \<open>self: &mut Self\<close> with the
lifetime erased. Typed receivers stay available inside impls.
\<close>

urust \<open>
  struct Gauge { level: u32 }

  impl Gauge {
    fn read(self) -> u32 { self.level }

    fn read_mut(mut self) -> u32 { self.level }

    fn touch(&mut self) -> u32 { \<llangle>0 :: 32 word\<rrangle> }

    fn touch_for<'a>(&'a mut self, step: u32) -> u32 { step }

    fn read_typed(self: Gauge) -> u32 { self.level }

    fn read_typed_self(mut self: Self) -> u32 { self.level }

    fn touch_typed(self: &mut Self) -> u32 { \<llangle>0 :: 32 word\<rrangle> }
  }
\<close>

urust \<open>
  \<omega>\<open>name = "control_gauge_read", register_notation = false\<close>
  fn read(self: Gauge) -> u32 { self.level }

  \<omega>\<open>name = "control_gauge_read_mut", register_notation = false\<close>
  fn read_mut(mut self: Gauge) -> u32 { self.level }

  \<omega>\<open>name = "control_gauge_touch", register_notation = false\<close>
  fn touch(self: &mut Gauge) -> u32 { \<llangle>0 :: 32 word\<rrangle> }

  \<omega>\<open>name = "control_gauge_touch_for", register_notation = false\<close>
  fn touch_for(self: &mut Gauge, step: u32) -> u32 { step }
\<close>

lemma gauge_receivers_match_typed_spellings:
  shows \<open>gauge_read = control_gauge_read\<close>
    and \<open>gauge_read_mut = control_gauge_read_mut\<close>
    and \<open>gauge_touch = control_gauge_touch\<close>
    and \<open>gauge_touch_for = control_gauge_touch_for\<close>
    and \<open>gauge_read_typed = control_gauge_read\<close>
    and \<open>gauge_read_typed_self = control_gauge_read_mut\<close>
    and \<open>gauge_touch_typed = control_gauge_touch\<close>
  unfolding gauge_read_def control_gauge_read_def gauge_read_mut_def control_gauge_read_mut_def
    gauge_touch_def control_gauge_touch_def gauge_touch_for_def control_gauge_touch_for_def
    gauge_read_typed_def control_gauge_read_def gauge_read_typed_self_def
    control_gauge_read_mut_def gauge_touch_typed_def control_gauge_touch_def
  by (rule refl)+

section\<open> Calls \<close>

text\<open>
A path call \<open>Counter::f(..)\<close>, a method call \<open>x.f(..)\<close> and the function-style call
\<open>Counter::f(x, ..)\<close> of a method elaborate to the same term as a call of the member's constant
through an explicit call notation, here registered under control names. Arguments follow the
receiver, and calls work inside closures and nested blocks.
\<close>

micro_rust_notation (call) counter_new ("ControlCounterNew")
micro_rust_notation (call) counter_get ("ControlCounterGet")
micro_rust_notation (call) counter_plus ("ControlCounterPlus")

urust \<open>
  fn CounterPathNew() -> Counter { Counter::new() }

  fn CounterControlNew() -> Counter { ControlCounterNew() }

  fn CounterMethodGet(c: Counter) -> u32 { c.get() }

  fn CounterPathGet(c: Counter) -> u32 { Counter::get(c) }

  fn CounterControlGet(c: Counter) -> u32 { ControlCounterGet(c) }

  fn CounterMethodPlus(c: Counter) -> u32 { c.plus(1_u32) }

  fn CounterPathPlus(c: Counter) -> u32 { Counter::plus(c, 1_u32) }

  fn CounterControlPlus(c: Counter) -> u32 { ControlCounterPlus(c, 1_u32) }

  fn CounterNestedCalls(c: Counter) -> u32 {
    let read = |d| { d.get() };
    { let fresh = Counter::new(); read(fresh) + { c.plus(2_u32) } }
  }

  fn CounterNestedControl(c: Counter) -> u32 {
    let read = |d| { ControlCounterGet(d) };
    { let fresh = ControlCounterNew(); read(fresh) + { ControlCounterPlus(c, 2_u32) } }
  }
\<close>

lemma counter_calls_match_control_calls:
  shows \<open>counter_path_new = counter_control_new\<close>
    and \<open>counter_method_get = counter_control_get\<close>
    and \<open>counter_path_get = counter_control_get\<close>
    and \<open>counter_method_plus = counter_control_plus\<close>
    and \<open>counter_path_plus = counter_control_plus\<close>
    and \<open>counter_nested_calls = counter_nested_control\<close>
  unfolding counter_path_new_def counter_control_new_def counter_method_get_def
    counter_control_get_def counter_path_get_def counter_control_get_def counter_method_plus_def
    counter_control_plus_def counter_path_plus_def counter_control_plus_def
    counter_nested_calls_def counter_nested_control_def
  by (rule refl)+

subsection\<open> Receiver dispatch across types \<close>

text\<open>
Methods of different types share their bare name; a method call dispatches by receiver type.
\<close>

urust \<open>
  impl Counter {
    fn describe(self) -> u32 { self.value }
  }

  impl Gauge {
    fn describe(self) -> u32 { self.level }
  }

  fn DescribeBoth(c: Counter, g: Gauge) -> u32 { c.describe() + g.describe() }
\<close>

micro_rust_notation (call) counter_describe ("ControlCounterDescribe")
micro_rust_notation (call) gauge_describe ("ControlGaugeDescribe")

urust \<open>
  fn DescribeBothControl(c: Counter, g: Gauge) -> u32 {
    ControlCounterDescribe(c) + ControlGaugeDescribe(g)
  }
\<close>

lemma receiver_dispatch_matches_control:
  shows \<open>describe_both = describe_both_control\<close>
  unfolding describe_both_def describe_both_control_def
  by (rule refl)

subsection\<open> Maximum arity \<close>

text\<open>
A method takes up to thirteen arguments after its receiver, fourteen parameters in all.
\<close>

urust \<open>
  impl Counter {
    fn wide(self, a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32, i: u32,
        j: u32, k: u32, l: u32, m: u32) -> u32 {
      self.value + m
    }
  }

  fn CounterWideMethod(c: Counter) -> u32 {
    c.wide(1_u32, 2_u32, 3_u32, 4_u32, 5_u32, 6_u32, 7_u32, 8_u32, 9_u32, 10_u32, 11_u32,
      12_u32, 13_u32)
  }

  fn CounterWidePath(c: Counter) -> u32 {
    Counter::wide(c, 1_u32, 2_u32, 3_u32, 4_u32, 5_u32, 6_u32, 7_u32, 8_u32, 9_u32, 10_u32,
      11_u32, 12_u32, 13_u32)
  }
\<close>

lemma counter_wide_calls_match:
  shows \<open>counter_wide_method = counter_wide_path\<close>
  unfolding counter_wide_method_def counter_wide_path_def
  by (rule refl)+

section\<open> Targets \<close>

text\<open>
A target is a generated datatype, a \<open>urust_type\<close> mapping, optionally with concrete or
\<open>\<tau>\<open>...\<close>\<close> generic arguments, or a type alias of one. An alias target expands to its final
target: its members register under that target's path, and \<open>Self\<close> is the expansion.
\<close>

urust \<open>
  enum Mode { Off, On }

  impl Mode {
    fn flipped(self) -> Self { match self { Mode::Off => Mode::On, Mode::On => Mode::Off } }
  }

  fn UseModeFlip(mode: Mode) -> Mode { mode.flipped() }
\<close>

urust_type "Meter" = \<open> nat \<close>

urust_type "Slot<'t>" = \<open> 't list \<close>

urust \<open>
  impl Meter {
    fn doubled(self) -> Self { \<llangle>2 * self\<rrangle> }
  }

  impl Slot<\<tau>\<open>'a\<close>> {
    fn items(self) -> \<tau>\<open>'a list\<close> { self }
  }

  fn UseMeterDoubled(m: Meter) -> Meter { m.doubled() }

  fn UseSlotItems(s: Slot<\<tau>\<open>nat\<close>>) -> \<tau>\<open>nat list\<close> { s.items() }
\<close>

urust \<open>
  \<omega>\<open>name = "control_meter_doubled", register_notation = false\<close>
  fn doubled(self: Meter) -> Meter { \<llangle>2 * self\<rrangle> }

  \<omega>\<open>name = "control_slot_items", register_notation = false\<close>
  fn items(self: Slot<\<tau>\<open>'a\<close>>) -> \<tau>\<open>'a list\<close> { self }
\<close>

lemma mapped_targets_match_controls:
  shows \<open>meter_doubled = control_meter_doubled\<close>
    and \<open>slot_items = control_slot_items\<close>
  unfolding meter_doubled_def control_meter_doubled_def slot_items_def control_slot_items_def
  by (rule refl)+

subsection\<open> Concrete instances of one type constructor \<close>

text\<open>
Impls of different instances of one generic type may define the same member name; method calls
dispatch between them by receiver type. Their HOL names must differ.
\<close>

urust \<open>
  struct Pair<T> { left: T, right: T }

  impl Pair<u8> {
    \<omega>\<open>name = "pair_byte_total"\<close>
    fn total(self) -> u8 { self.left + self.right }
  }

  impl Pair<u16> {
    \<omega>\<open>name = "pair_word_total"\<close>
    fn total(self) -> u16 { self.left + self.right }
  }

  fn UsePairByteTotal(p: Pair<u8>) -> u8 { p.total() }

  fn UsePairWordTotal(p: Pair<u16>) -> u16 { p.total() }
\<close>

micro_rust_notation (call) pair_byte_total ("ControlPairByteTotal")
micro_rust_notation (call) pair_word_total ("ControlPairWordTotal")

urust \<open>
  fn UsePairByteControl(p: Pair<u8>) -> u8 { ControlPairByteTotal(p) }

  fn UsePairWordControl(p: Pair<u16>) -> u16 { ControlPairWordTotal(p) }
\<close>

lemma instance_dispatch_matches_control:
  shows \<open>use_pair_byte_total = use_pair_byte_control\<close>
    and \<open>use_pair_word_total = use_pair_word_control\<close>
  unfolding use_pair_byte_total_def use_pair_byte_control_def use_pair_word_total_def
    use_pair_word_control_def
  by (rule refl)+

subsection\<open> Type alias targets \<close>

text\<open>
An impl of a type alias, plain, generic or chained, registers its members under the final
target's path, here \<open>Counter\<close> and \<open>Pair\<close>, with the expansion as Self type. Default HOL
names use the alias as written. Calls through the alias head itself are covered with the type
heads.
\<close>

urust_type_alias \<open> type CounterAlias = Counter; \<close>

urust_type_alias \<open> type Twin<T> = Pair<T>; \<close>

urust_type_alias \<open> type ByteTwin = Twin<u8>; \<close>

urust \<open>
  impl CounterAlias {
    fn doubled_value(self) -> u32 { self.value + self.value }
  }

  impl Twin<u32> {
    fn left_of(self) -> u32 { self.left }
  }

  impl ByteTwin {
    fn right_of(self) -> Self { self }
  }

  fn UseAliasMembers(c: Counter, wide: Pair<u32>) -> u32 {
    Counter::doubled_value(c) + wide.left_of() + Pair::left_of(wide)
  }

  fn UseChainedAlias(narrow: Pair<u8>) -> Pair<u8> { narrow.right_of() }
\<close>

urust \<open>
  \<omega>\<open>name = "control_counter_doubled_value", register_notation = false\<close>
  fn doubled_value(self: Counter) -> u32 { self.value + self.value }

  \<omega>\<open>name = "control_twin_left_of", register_notation = false\<close>
  fn left_of(self: Pair<u32>) -> u32 { self.left }

  \<omega>\<open>name = "control_byte_twin_right_of", register_notation = false\<close>
  fn right_of(self: Pair<u8>) -> Pair<u8> { self }
\<close>

lemma alias_targets_match_controls:
  shows \<open>counter_alias_doubled_value = control_counter_doubled_value\<close>
    and \<open>twin_left_of = control_twin_left_of\<close>
    and \<open>byte_twin_right_of = control_byte_twin_right_of\<close>
  unfolding counter_alias_doubled_value_def control_counter_doubled_value_def twin_left_of_def
    control_twin_left_of_def byte_twin_right_of_def control_byte_twin_right_of_def
  by (rule refl)+

section\<open> Locales \<close>

text\<open>
An impl inside a locale may mention the locale's type parameters. Each interpretation registers
the members of its instance, and method calls dispatch between differently typed instances.
\<close>

locale impl_store =
  fixes impl_store_witness :: \<open>'a itself\<close>
begin

urust \<open>
  impl Slot<\<tau>\<open>'a\<close>> {
    fn stored(self) -> \<tau>\<open>'a list\<close> { self }

    fn stored_twice(self) -> \<tau>\<open>'a list\<close> { self.stored() }
  }
\<close>

urust \<open>
  \<omega>\<open>name = "control_slot_stored", register_notation = false\<close>
  fn stored(self: Slot<\<tau>\<open>'a\<close>>) -> \<tau>\<open>'a list\<close> { self }
\<close>

lemma slot_stored_matches_control:
  shows \<open>slot_stored = control_slot_stored\<close>
  unfolding slot_stored_def control_slot_stored_def
  by (rule refl)


end

interpretation impl_store_nat: impl_store \<open>TYPE(nat)\<close> .

interpretation impl_store_bool: impl_store \<open>TYPE(bool)\<close> .

urust \<open>
  fn UseStoredNat(s: Slot<\<tau>\<open>nat\<close>>) -> \<tau>\<open>nat list\<close> { s.stored() }

  fn UseStoredBool(s: Slot<\<tau>\<open>bool\<close>>) -> \<tau>\<open>bool list\<close> { Slot::stored(s) }
\<close>

chapter\<open> Impl block resolution \<close>

text\<open>
Inside an impl member, a leading \<open>Self\<close> path segment names the implementing type in calls,
values, struct expressions, tuple constructors, enum variants and patterns, keeping the
\<open>Self\<close> token's position. A path call \<open>T::f(..)\<close> follows Rust's E0034 rule: with two or
more impls of \<open>T::f\<close>, the call must select an instance through type-segment generic arguments
\<open>T::<A>::f(..)\<close>, a type alias or an imported type head; \<open>Self::f(..)\<close> selects the impl's own
instance. A direct call \<open>f(..)\<close> never reaches a method entry. The rejections are audited in
\<open>Parser_Impl_ML_Tests\<close>.
\<close>

section\<open> Self paths \<close>

urust \<open>
  struct Tally { count: u32 }

  struct Twofold(u32, u32);

  struct Beacon;

  enum Light { Dark, Lit(u32), Glow { level: u32 } }

  impl Tally {
    fn new() -> Self { Self { count: 0_u32 } }

    fn read(self) -> u32 { self.count }

    fn fresh() -> Self { Self::new() }

    fn reread(self) -> u32 { Self::read(self) }

    fn count_of(self) -> u32 { match self { Self { count } => count } }
  }

  impl Twofold {
    fn twin(value: u32) -> Self { Self(value, value) }

    fn first(self) -> u32 { match self { Self(first, _) => first } }
  }

  impl Beacon {
    fn make() -> Self { Self }

    fn is_beacon(self) -> bool { match self { Self => true } }
  }

  impl Light {
    fn dim() -> Self { Self::Dark }

    fn lit(level: u32) -> Self { Self::Lit(level) }

    fn glow(level: u32) -> Self { Self::Glow { level: level } }

    fn level_of(self) -> u32 {
      match self { Self::Dark => 0_u32, Self::Lit(level) | Self::Glow { level } => level }
    }

    fn wrapped_level(self) -> u32 {
      match Some(self) { Some(Self::Lit(level)) => level, _ => 0_u32 }
    }
  }
\<close>

urust \<open>
  \<omega>\<open>name = "control_tally_new", register_notation = false\<close>
  fn new() -> Tally { Tally { count: 0_u32 } }

  \<omega>\<open>name = "control_tally_fresh", register_notation = false\<close>
  fn fresh() -> Tally { Tally::new() }

  \<omega>\<open>name = "control_tally_reread", register_notation = false\<close>
  fn reread(self: Tally) -> u32 { self.read() }

  \<omega>\<open>name = "control_tally_count_of", register_notation = false\<close>
  fn count_of(self: Tally) -> u32 { match self { Tally { count } => count } }

  \<omega>\<open>name = "control_twofold_twin", register_notation = false\<close>
  fn twin(value: u32) -> Twofold { Twofold(value, value) }

  \<omega>\<open>name = "control_twofold_first", register_notation = false\<close>
  fn first(self: Twofold) -> u32 { match self { Twofold(first, _) => first } }

  \<omega>\<open>name = "control_beacon_make", register_notation = false\<close>
  fn make() -> Beacon { Beacon }

  \<omega>\<open>name = "control_beacon_is_beacon", register_notation = false\<close>
  fn is_beacon(self: Beacon) -> bool { match self { Beacon => true } }

  \<omega>\<open>name = "control_light_dim", register_notation = false\<close>
  fn dim() -> Light { Light::Dark }

  \<omega>\<open>name = "control_light_lit", register_notation = false\<close>
  fn lit(level: u32) -> Light { Light::Lit(level) }

  \<omega>\<open>name = "control_light_glow", register_notation = false\<close>
  fn glow(level: u32) -> Light { Light::Glow { level: level } }

  \<omega>\<open>name = "control_light_level_of", register_notation = false\<close>
  fn level_of(self: Light) -> u32 {
    match self { Light::Dark => 0_u32, Light::Lit(level) | Light::Glow { level } => level }
  }

  \<omega>\<open>name = "control_light_wrapped_level", register_notation = false\<close>
  fn wrapped_level(self: Light) -> u32 {
    match Some(self) { Some(Light::Lit(level)) => level, _ => 0_u32 }
  }
\<close>

lemma self_paths_match_controls:
  shows \<open>tally_new = control_tally_new\<close>
    and \<open>tally_fresh = control_tally_fresh\<close>
    and \<open>tally_reread = control_tally_reread\<close>
    and \<open>tally_count_of = control_tally_count_of\<close>
    and \<open>twofold_twin = control_twofold_twin\<close>
    and \<open>twofold_first = control_twofold_first\<close>
    and \<open>beacon_make = control_beacon_make\<close>
    and \<open>beacon_is_beacon = control_beacon_is_beacon\<close>
    and \<open>light_dim = control_light_dim\<close>
    and \<open>light_lit = control_light_lit\<close>
    and \<open>light_glow = control_light_glow\<close>
    and \<open>light_level_of = control_light_level_of\<close>
    and \<open>light_wrapped_level = control_light_wrapped_level\<close>
  unfolding tally_new_def control_tally_new_def tally_fresh_def control_tally_fresh_def
    tally_reread_def control_tally_reread_def tally_count_of_def control_tally_count_of_def
    twofold_twin_def control_twofold_twin_def twofold_first_def control_twofold_first_def
    beacon_make_def control_beacon_make_def beacon_is_beacon_def control_beacon_is_beacon_def
    light_dim_def control_light_dim_def light_lit_def control_light_lit_def light_glow_def
    control_light_glow_def light_level_of_def control_light_level_of_def
    light_wrapped_level_def control_light_wrapped_level_def
  by (rule refl)+

subsection\<open> Self patterns \<close>

text\<open>
In a pattern, \<open>Self\<close> is a path. For a unit struct it matches the unit value in \<open>let\<close>,
parameters and closure formals, as the struct's own name does in \<open>let\<close> and in closure
formals.
\<close>

urust \<open>
  impl Beacon {
    fn binds_self(self) -> bool { let Self = self; true }

    fn takes_self(Self: Beacon) -> bool { true }

    fn closes_self(self) -> bool { let check = |Self| { true }; check(self) }
  }
\<close>

urust \<open>
  \<omega>\<open>name = "control_beacon_binds_self", register_notation = false\<close>
  fn binds_self(self: Beacon) -> bool { let Beacon = self; true }

  \<omega>\<open>name = "control_beacon_takes_self", register_notation = false\<close>
  fn takes_self(_: Beacon) -> bool { true }

  \<omega>\<open>name = "control_beacon_closes_self", register_notation = false\<close>
  fn closes_self(self: Beacon) -> bool { let check = |Beacon| { true }; check(self) }
\<close>

lemma self_patterns_match_controls:
  shows \<open>beacon_binds_self = control_beacon_binds_self\<close>
    and \<open>beacon_takes_self = control_beacon_takes_self\<close>
    and \<open>beacon_closes_self = control_beacon_closes_self\<close>
  unfolding beacon_binds_self_def control_beacon_binds_self_def beacon_takes_self_def
    control_beacon_takes_self_def beacon_closes_self_def control_beacon_closes_self_def
  by (rule refl)+

subsection\<open> Total Self and alias patterns at case sites \<close>

text\<open>
At \<open>if let\<close>, \<open>while let\<close> and \<open>let \<dots> else\<close>, a total pattern through a \<open>Self\<close>,
alias or turbofish head is total like its written path: the constructor at its instance type is
still its family's member, so case compilation adds no fallback clause. Each member equals its
written-path control. (\<open>matches!\<close> with a total pattern is rejected at the base, written or
through \<open>Self\<close>; see \<open>Parser_Impl_ML_Tests\<close>.)
\<close>

urust \<open>
  enum Solitary { Only }

  struct Pocket { v: u32 }

  struct Sheath(u32);

  struct Bin<X> { x: X }
\<close>

urust_type_alias \<open> type BinByte = Bin<u8>; \<close>

urust \<open>
  impl Beacon {
    fn if_self(self) -> u32 { if let Self = self { 1_u32 } else { 2_u32 } }

    fn while_self(self) -> u32 {
      #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Self = self { }; 1_u32
    }

    fn else_self(self) -> u32 { let Self = self else { return 2_u32; }; 1_u32 }
  }

  impl Solitary {
    fn if_only(self) -> u32 { if let Self::Only = self { 1_u32 } else { 2_u32 } }

    fn while_only(self) -> u32 {
      #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Self::Only = self { }; 1_u32
    }
  }

  impl Pocket {
    fn if_fields(self) -> u32 { if let Self { v } = self { v } else { 2_u32 } }
  }

  impl Sheath {
    fn while_inner(self) -> u32 {
      #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Self(_a) = self { }; 1_u32
    }
  }

  impl Bin<u8> {
    fn if_any(self) -> u32 { if let Self { x: _ } = self { 1_u32 } else { 2_u32 } }
  }

  fn BinAliasHead(p: Bin<u8>) -> u32 { if let BinByte { x: _ } = p { 1_u32 } else { 2_u32 } }

  fn BinTurbofish(p: Bin<u8>) -> u32 { if let Bin::<u8> { x: _ } = p { 1_u32 } else { 2_u32 } }
\<close>

urust \<open>
  \<omega>\<open>name = "control_beacon_if_self", register_notation = false\<close>
  fn if_self(self: Beacon) -> u32 { if let Beacon = self { 1_u32 } else { 2_u32 } }

  \<omega>\<open>name = "control_beacon_while_self", register_notation = false\<close>
  fn while_self(self: Beacon) -> u32 {
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Beacon = self { }; 1_u32
  }

  \<omega>\<open>name = "control_beacon_else_self", register_notation = false\<close>
  fn else_self(self: Beacon) -> u32 { let Beacon = self else { return 2_u32; }; 1_u32 }

  \<omega>\<open>name = "control_solitary_if_only", register_notation = false\<close>
  fn if_only(self: Solitary) -> u32 { if let Solitary::Only = self { 1_u32 } else { 2_u32 } }

  \<omega>\<open>name = "control_solitary_while_only", register_notation = false\<close>
  fn while_only(self: Solitary) -> u32 {
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Solitary::Only = self { }; 1_u32
  }

  \<omega>\<open>name = "control_pocket_if_fields", register_notation = false\<close>
  fn if_fields(self: Pocket) -> u32 { if let Pocket { v } = self { v } else { 2_u32 } }

  \<omega>\<open>name = "control_sheath_while_inner", register_notation = false\<close>
  fn while_inner(self: Sheath) -> u32 {
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Sheath(_a) = self { }; 1_u32
  }

  \<omega>\<open>name = "control_bin_if_any", register_notation = false\<close>
  fn if_any(self: Bin<u8>) -> u32 { if let Bin { x: _ } = self { 1_u32 } else { 2_u32 } }
\<close>

lemma total_head_patterns_match_controls:
  shows \<open>beacon_if_self = control_beacon_if_self\<close>
    and \<open>beacon_while_self = control_beacon_while_self\<close>
    and \<open>beacon_else_self = control_beacon_else_self\<close>
    and \<open>solitary_if_only = control_solitary_if_only\<close>
    and \<open>solitary_while_only = control_solitary_while_only\<close>
    and \<open>pocket_if_fields = control_pocket_if_fields\<close>
    and \<open>sheath_while_inner = control_sheath_while_inner\<close>
    and \<open>bin_if_any = control_bin_if_any\<close>
    and \<open>bin_alias_head = control_bin_if_any\<close>
    and \<open>bin_turbofish = control_bin_if_any\<close>
  unfolding beacon_if_self_def control_beacon_if_self_def beacon_while_self_def
    control_beacon_while_self_def beacon_else_self_def control_beacon_else_self_def
    solitary_if_only_def
    control_solitary_if_only_def solitary_while_only_def control_solitary_while_only_def
    pocket_if_fields_def control_pocket_if_fields_def sheath_while_inner_def
    control_sheath_while_inner_def
    bin_if_any_def control_bin_if_any_def bin_alias_head_def bin_turbofish_def
  by (rule refl)+

subsection\<open> Self in closure formals \<close>

text\<open>
A closure formal is a pattern at a binding site, so \<open>Self\<close> in it is a path, inside a tuple
too, and a nullary sole constructor binds it, as the written path does.
\<close>

urust \<open>
  impl Beacon {
    fn closes_pair(self) -> u32 { let first = |(Self, x)| { x }; first((self, 1_u32)) }
  }

  impl Solitary {
    fn closes_only(self) -> bool { let check = |Self::Only| { true }; check(self) }
  }
\<close>

urust \<open>
  \<omega>\<open>name = "control_beacon_closes_pair", register_notation = false\<close>
  fn closes_pair(self: Beacon) -> u32 { let first = |(Beacon, x)| { x }; first((self, 1_u32)) }

  \<omega>\<open>name = "control_solitary_closes_only", register_notation = false\<close>
  fn closes_only(self: Solitary) -> bool { let check = |Solitary::Only| { true }; check(self) }
\<close>

lemma closure_self_patterns_match_controls:
  shows \<open>beacon_closes_pair = control_beacon_closes_pair\<close>
    and \<open>solitary_closes_only = control_solitary_closes_only\<close>
  unfolding beacon_closes_pair_def control_beacon_closes_pair_def solitary_closes_only_def
    control_solitary_closes_only_def
  by (rule refl)+

section\<open> Path selection across instantiations \<close>

text\<open>
\<open>Duo::sum\<close> is defined in two impls, so each path call selects its instance; \<open>Self::sum\<close>
in each impl selects that impl's own. \<open>Solo::only\<close> has one impl, so its unannotated path
call is accepted. The interpretations of one locale impl are one impl (\<open>Slot::stored\<close> above).
\<close>

urust \<open>
  struct Duo<T> { first: T, second: T }

  struct Solo<T> { inner: T }

  impl Duo<u8> {
    \<omega>\<open>name = "duo_byte_sum"\<close>
    fn sum(self) -> u8 { self.first + self.second }

    \<omega>\<open>name = "duo_byte_own"\<close>
    fn own(self) -> u8 { Self::sum(self) }
  }

  impl Duo<u16> {
    \<omega>\<open>name = "duo_word_sum"\<close>
    fn sum(self) -> u16 { self.first + self.second }

    \<omega>\<open>name = "duo_word_own"\<close>
    fn own(self) -> u16 { Self::sum(self) }
  }

  impl Duo<\<tau>\<open>nat\<close>> {
    \<omega>\<open>name = "duo_nat_sum"\<close>
    fn sum(self) -> \<tau>\<open>nat\<close> { \<llangle>0 :: nat\<rrangle> }
  }

  impl Solo<u8> {
    fn only(self) -> u8 { self.inner }
  }

  fn SelectByte(d: Duo<u8>) -> u8 { Duo::<u8>::sum(d) }

  fn SelectWord(d: Duo<u16>) -> u16 { Duo::<u16>::sum(d) }

  fn SelectNat(d: Duo<\<tau>\<open>nat\<close>>) -> \<tau>\<open>nat\<close> { Duo::<\<tau>\<open>nat\<close>>::sum(d) }

  fn SelectMethod(d: Duo<u16>) -> u16 { d.sum() }

  fn UseSoloOnly(s: Solo<u8>) -> u8 { Solo::only(s) }

  fn StoredNat(s: Slot<\<tau>\<open>nat\<close>>) -> \<tau>\<open>nat list\<close> { Slot::stored(s) }
\<close>

micro_rust_notation (call) duo_byte_sum ("ControlDuoByteSum")
micro_rust_notation (call) duo_word_sum ("ControlDuoWordSum")
micro_rust_notation (call) duo_nat_sum ("ControlDuoNatSum")
micro_rust_notation (call) solo_only ("ControlSoloOnly")

urust \<open>
  fn SelectByteControl(d: Duo<u8>) -> u8 { ControlDuoByteSum(d) }

  fn SelectWordControl(d: Duo<u16>) -> u16 { ControlDuoWordSum(d) }

  fn SelectNatControl(d: Duo<\<tau>\<open>nat\<close>>) -> \<tau>\<open>nat\<close> { ControlDuoNatSum(d) }

  fn UseSoloOnlyControl(s: Solo<u8>) -> u8 { ControlSoloOnly(s) }

  \<omega>\<open>name = "control_duo_byte_own", register_notation = false\<close>
  fn own(self: Duo<u8>) -> u8 { ControlDuoByteSum(self) }

  \<omega>\<open>name = "control_duo_word_own", register_notation = false\<close>
  fn own(self: Duo<u16>) -> u16 { ControlDuoWordSum(self) }
\<close>

lemma path_selection_matches_controls:
  shows \<open>select_byte = select_byte_control\<close>
    and \<open>select_word = select_word_control\<close>
    and \<open>select_nat = select_nat_control\<close>
    and \<open>select_method = select_word_control\<close>
    and \<open>use_solo_only = use_solo_only_control\<close>
    and \<open>duo_byte_own = control_duo_byte_own\<close>
    and \<open>duo_word_own = control_duo_word_own\<close>
  unfolding select_byte_def select_byte_control_def select_word_def select_word_control_def
    select_nat_def select_nat_control_def select_method_def use_solo_only_def
    use_solo_only_control_def duo_byte_own_def control_duo_byte_own_def duo_word_own_def
    control_duo_word_own_def
  by (rule refl)+

section\<open> Type heads through aliases and imports \<close>

text\<open>
A leading type head written as a type alias or a chunk or block import denotes its target: its
associated items resolve under the target's canonical path, and the alias expansion, with any
generic arguments written on the head, selects the instance. The same holds for variants and
struct heads in values and patterns.
\<close>

urust_type_alias \<open> type ByteDuo = Duo<u8>; \<close>

urust_type_alias \<open> type AnyDuo<T> = Duo<T>; \<close>

urust_type_alias \<open> type ByteDuoAgain = ByteDuo; \<close>

urust_type_alias \<open> type Lamp = Light; \<close>

urust_type_alias \<open> type TallyAlias = Tally; \<close>

urust \<open>
  impl demo::Width {
    fn bits(self) -> u32 { self }
  }

  fn AliasSelect(d: Duo<u8>) -> u8 { ByteDuo::sum(d) }

  fn GenericAliasSelect(d: Duo<u16>) -> u16 { AnyDuo::<u16>::sum(d) }

  fn ChainedAliasSelect(d: Duo<u8>) -> u8 { ByteDuoAgain::sum(d) }

  fn ImportedHeadSelect(d: Duo<u8>) -> u8 {
    use Duo as Both;
    Both::<u8>::sum(d)
  }

  fn ImportedAliasSelect(d: Duo<u8>) -> u8 {
    use ByteDuo as Bytes;
    Bytes::sum(d)
  }

  fn CanonicalWidthBits(w: demo::Width) -> u32 { demo::Width::bits(w) }

  fn ImportedWidthBits(w: demo::Width) -> u32 {
    use demo::Width as Word32;
    Word32::bits(w)
  }

  fn LampValue() -> Light { Lamp::Lit(3_u32) }

  fn LampLevel(light: Light) -> u32 {
    match light { Lamp::Lit(level) => level, Lamp::Glow { level } => level, Lamp::Dark => 0_u32 }
  }

  fn TallyAliasValue() -> Tally { TallyAlias { count: 1_u32 } }

  fn TallyAliasCount(tally: Tally) -> u32 { match tally { TallyAlias { count } => count } }

  fn ImportedLamp() -> Light {
    use Lamp as Signal;
    Signal::Glow { level: 2_u32 }
  }
\<close>

urust \<open>
  fn LampValueControl() -> Light { Light::Lit(3_u32) }

  fn LampLevelControl(light: Light) -> u32 {
    match light { Light::Lit(level) => level, Light::Glow { level } => level, Light::Dark => 0_u32 }
  }

  fn TallyAliasValueControl() -> Tally { Tally { count: 1_u32 } }

  fn TallyAliasCountControl(tally: Tally) -> u32 { match tally { Tally { count } => count } }

  fn ImportedLampControl() -> Light { Light::Glow { level: 2_u32 } }
\<close>

lemma type_heads_match_canonical_paths:
  shows \<open>alias_select = select_byte\<close>
    and \<open>generic_alias_select = select_word\<close>
    and \<open>chained_alias_select = select_byte\<close>
    and \<open>imported_head_select = select_byte\<close>
    and \<open>imported_alias_select = select_byte\<close>
    and \<open>imported_width_bits = canonical_width_bits\<close>
    and \<open>lamp_value = lamp_value_control\<close>
    and \<open>lamp_level = lamp_level_control\<close>
    and \<open>tally_alias_value = tally_alias_value_control\<close>
    and \<open>tally_alias_count = tally_alias_count_control\<close>
    and \<open>imported_lamp = imported_lamp_control\<close>
  unfolding alias_select_def generic_alias_select_def chained_alias_select_def
    imported_head_select_def imported_alias_select_def select_byte_def select_word_def
    imported_width_bits_def canonical_width_bits_def lamp_value_def lamp_value_control_def lamp_level_def
    lamp_level_control_def tally_alias_value_def tally_alias_value_control_def
    tally_alias_count_def tally_alias_count_control_def imported_lamp_def
    imported_lamp_control_def
  by (rule refl)+

subsection\<open> Generic arguments of type heads \<close>

text\<open>
A head that fixes an instance (\<open>Self\<close>, a type alias with its expansion's and its written
arguments, an imported alias) instantiates the constructors it reaches, in values, calls, struct
expressions and patterns, exactly like the canonical path with type-segment arguments.
\<close>

urust \<open>
  enum Hold<T> { Empty, Holding(T) }

  struct Parcel<T> { inner: T }

  impl Hold<u8> {
    \<omega>\<open>name = "hold_byte_wrap"\<close>
    fn wrap(value: u8) -> Self { Self::Holding(value) }
  }

  impl Parcel<u8> {
    \<omega>\<open>name = "parcel_byte_unwrap"\<close>
    fn unwrap(self) -> u8 { match self { Self { inner } => inner } }
  }
\<close>

urust_type_alias \<open> type ByteHold = Hold<u8>; \<close>

urust_type_alias \<open> type AnyHold<T> = Hold<T>; \<close>

urust_type_alias \<open> type ByteParcel = Parcel<u8>; \<close>

urust \<open>
  fn AliasHolding() -> bool { let held = ByteHold::Holding(1); true }

  fn AliasEmpty() -> bool { let held = ByteHold::Empty; true }

  fn GenericAliasHolding() -> bool { let held = AnyHold::<u8>::Holding(1); true }

  fn ImportedAliasHolding() -> bool {
    use ByteHold as Held;
    let held = Held::Holding(1);
    true
  }

  fn AliasHoldLevel(held: Hold<u8>) -> u8 {
    match held { ByteHold::Holding(value) => value, ByteHold::Empty => 0_u8 }
  }

  fn AliasParcel() -> bool { let parcel = ByteParcel { inner: 1 }; true }

  fn AliasParcelInner(parcel: Parcel<u8>) -> u8 { match parcel { ByteParcel { inner } => inner } }
\<close>

urust \<open>
  fn CanonicalHolding() -> bool { let held = Hold::<u8>::Holding(1); true }

  fn CanonicalEmpty() -> bool { let held = Hold::<u8>::Empty; true }

  fn CanonicalHoldLevel(held: Hold<u8>) -> u8 {
    match held { Hold::Holding(value) => value, Hold::Empty => 0_u8 }
  }

  fn CanonicalParcel() -> bool { let parcel = Parcel { inner: 1_u8 }; true }

  fn CanonicalParcelInner(parcel: Parcel<u8>) -> u8 { match parcel { Parcel { inner } => inner } }

  \<omega>\<open>name = "control_hold_byte_wrap", register_notation = false\<close>
  fn wrap(value: u8) -> Hold<u8> { Hold::<u8>::Holding(value) }

  \<omega>\<open>name = "control_parcel_byte_unwrap", register_notation = false\<close>
  fn unwrap(self: Parcel<u8>) -> u8 { match self { Parcel { inner } => inner } }
\<close>

lemma type_head_arguments_match_canonical_paths:
  shows \<open>alias_holding = canonical_holding\<close>
    and \<open>alias_empty = canonical_empty\<close>
    and \<open>generic_alias_holding = canonical_holding\<close>
    and \<open>imported_alias_holding = canonical_holding\<close>
    and \<open>alias_hold_level = canonical_hold_level\<close>
    and \<open>alias_parcel = canonical_parcel\<close>
    and \<open>alias_parcel_inner = canonical_parcel_inner\<close>
    and \<open>hold_byte_wrap = control_hold_byte_wrap\<close>
    and \<open>parcel_byte_unwrap = control_parcel_byte_unwrap\<close>
  unfolding alias_holding_def canonical_holding_def alias_empty_def canonical_empty_def
    generic_alias_holding_def imported_alias_holding_def alias_hold_level_def
    canonical_hold_level_def alias_parcel_def canonical_parcel_def alias_parcel_inner_def
    canonical_parcel_inner_def hold_byte_wrap_def control_hold_byte_wrap_def
    parcel_byte_unwrap_def control_parcel_byte_unwrap_def
  by (rule refl)+

subsection\<open> Exact keys under alias heads \<close>

text\<open>
A written key with an exact registration resolves as written (D133), before its head is expanded
through an alias: here an explicit call key and an explicit literal key spelled with the alias.
\<close>

definition tally_limit :: \<open>32 word\<close> where
  \<open> tally_limit = 3 \<close>

micro_rust_notation (call) tally_new ("TallyAlias::spawn")

micro_rust_notation (literal) tally_limit ("TallyAlias::LIMIT")

micro_rust_notation (literal) tally_limit ("ControlTallyLimit")

micro_rust_notation (call) tally_new ("ControlTallySpawn")

urust \<open>
  fn AliasExactCall() -> Tally { TallyAlias::spawn() }

  fn AliasExactLiteral() -> u32 { TallyAlias::LIMIT }

  fn AliasExactCallControl() -> Tally { ControlTallySpawn() }

  fn AliasExactLiteralControl() -> u32 { ControlTallyLimit }
\<close>

lemma exact_keys_under_alias_heads:
  shows \<open>alias_exact_call = alias_exact_call_control\<close>
    and \<open>alias_exact_literal = alias_exact_literal_control\<close>
  unfolding alias_exact_call_def alias_exact_call_control_def alias_exact_literal_def
    alias_exact_literal_control_def
  by (rule refl)+

section\<open> Direct calls and method entries \<close>

text\<open>
A direct call does not reach a method entry. Beside the method \<open>describe\<close> of
\<open>Counter\<close> and \<open>Gauge\<close>, the free function \<open>describe\<close> is the only target of a direct
call, while method calls keep dispatching by receiver.
\<close>

urust_fn \<open> fn describe(value: u32) -> u32 { value + 1_u32 } \<close>

urust \<open>
  fn DescribeDirect(value: u32) -> u32 { describe(value) }

  fn DescribeMethods(c: Counter, g: Gauge) -> u32 { c.describe() + g.describe() }
\<close>

micro_rust_notation (call) describe ("ControlDescribe")

urust \<open>
  fn DescribeDirectControl(value: u32) -> u32 { ControlDescribe(value) }
\<close>

lemma direct_calls_skip_methods:
  shows \<open>describe_direct = describe_direct_control\<close>
    and \<open>describe_methods = describe_both_control\<close>
  unfolding describe_direct_def describe_direct_control_def describe_methods_def
    describe_both_control_def
  by (rule refl)+

chapter\<open> Source identities of concrete impls \<close>

urust_type [erase = \<open> 'tag, 'capacity \<close>]
  "ErasureOwner<'tag, const 'capacity>" = \<open> nat \<close>
urust_type_alias \<open> type ErasureAlpha = ErasureOwner<Alpha, 0>; \<close>

text\<open>
These owners have the same HOL Self type. Their erased source tags distinguish associated
selection. A HOL-only local receiver cannot recover a tag, so use an explicit associated path.
\<close>

urust \<open>
  impl ErasureOwner<Alpha, 0> {
    \<omega>\<open>name = "erasure_alpha_get"\<close>
    fn erased_get(self) -> Self { self }
    fn erased_self(self) -> Self { Self::erased_get(self) }
  }
  impl ErasureOwner<Beta, 0> {
    \<omega>\<open>name = "erasure_beta_get"\<close>
    fn erased_get(self) -> Self { self }
  }
  fn ErasureViaAlias(value: ErasureAlpha) -> ErasureAlpha {
    ErasureAlpha::erased_get(value)
  }
  fn ErasureViaExpanded(value: ErasureOwner<Alpha, 0>) -> ErasureOwner<Alpha, 0> {
    ErasureOwner::<Alpha, 0>::erased_get(value)
  }
\<close>
lemma erasure_alias_expanded: \<open> erasure_via_alias = erasure_via_expanded \<close>
  unfolding erasure_via_alias_def erasure_via_expanded_def by (rule refl)

urust_type "ErasureNatural" = \<open> nat \<close>
urust_type "ErasureBoolean" = \<open> bool \<close>
urust_type "ErasureOtherNatural" = \<open> nat \<close>

urust \<open>
  impl ErasureOtherNatural {
    fn reverse_owner<T>(self, value: T) -> Self { self }
  }
  impl ErasureNatural {
    fn sparse_owner<T>(self, value: ErasureOwner<T, 0>) -> Self { self }
  }
  impl ErasureBoolean {
    fn sparse_owner<T>(self, value: T) -> Self { self }
    fn reverse_owner<T>(self, value: T) -> Self { self }
  }
  impl ErasureNatural {
    fn reverse_owner<T>(self, value: ErasureOwner<T, 0>) -> Self { self }
  }
  impl ErasureOtherNatural {
    fn sparse_owner<T>(self, value: T) -> Self { self }
  }
  impl ErasureNatural {
    fn ambiguous_erased<T>(self, value: ErasureOwner<T, 0>) -> Self { self }
  }
  impl ErasureOtherNatural {
    fn ambiguous_erased<T>(self, value: ErasureOwner<T, 0>) -> Self { self }
  }
  fn ErasureScopedForward<T>(value: ErasureOwner<T, 0>) -> ErasureOwner<T, 0> {
    value.sparse_owner::<T>(value)
  }
  fn ErasureScopedReverse<T>(value: ErasureOwner<T, 0>) -> ErasureOwner<T, 0> {
    value.reverse_owner::<T>(value)
  }
\<close>

chapter\<open> Combined mapping owners \<close>

urust_type [erase = \<open> 'tag, 'capacity \<close>,
  implicit = \<open> global = 'store, address = 'addr \<close>]
  "ImplCombined<'payload, 'tag, const 'capacity>" =
    \<open> ('addr, 'store, 'payload) Global_Store.ref \<close>
urust_type_alias \<open> type ImplCombinedAlias = ImplCombined<u8, Alpha, 0>; \<close>

urust \<open>
  impl ImplCombined<u8, Alpha, 0> {
    \<omega>\<open>name = "impl_combined_alpha"\<close>
    fn combined_identity(self) -> Self { self }
    fn combined_self(self) -> Self { Self::combined_identity(self) }
    fn combined_share(self, other: ImplCombinedAlias, pointer: *const u8,
        borrowed: &mut u8) -> Self { self }
  }
  impl ImplCombined<u8, Beta, 0> {
    \<omega>\<open>name = "impl_combined_beta"\<close>
    fn combined_identity(self) -> Self { self }
  }
  fn ImplCombinedViaAlias(value: ImplCombinedAlias) -> ImplCombinedAlias {
    ImplCombinedAlias::combined_identity(value)
  }
  fn ImplCombinedViaExpanded(value: ImplCombined<u8, Alpha, 0>) -> ImplCombined<u8, Alpha, 0> {
    ImplCombined::<u8, Alpha, 0>::combined_identity(value)
  }
\<close>

lemma impl_combined_alias_twin:
  \<open> impl_combined_via_alias = impl_combined_via_expanded \<close>
  unfolding impl_combined_via_alias_def impl_combined_via_expanded_def by (rule refl)

urust_type [implicit = \<open> address = 'a, global = 'g \<close>]
  "ImplBackendOnly" = \<open> ('a, 'g, 8 word) Global_Store.ref \<close>
urust_type_alias \<open> type ImplBackendOnlyAlias = ImplBackendOnly; \<close>
urust_type [implicit = \<open> global = 'g \<close>]
  "ImplGlobalBackend" = \<open> 'g option \<close>
urust_type_alias \<open> type ImplGlobalBackendAlias = ImplGlobalBackend; \<close>

urust \<open>
  impl ImplBackendOnly {
    fn backend_share(self, other: ImplBackendOnlyAlias, pointer: *const u8,
        borrowed: &mut u8) -> Self { self }
  }
  impl ImplGlobalBackend {
    fn global_share(self, other: ImplGlobalBackendAlias, pointer: *const u8) -> Self { self }
  }
\<close>
urust_fn [register_notation = false] impl_backend_share_escape \<open>
  fn ImplBackendShareEscape(self: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close>,
      other: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close>,
      pointer: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close>,
      borrowed: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close>)
      -> \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close> { self }
\<close>

lemma impl_backend_share_twin:
  \<open> impl_backend_only_backend_share = impl_backend_share_escape \<close>
  unfolding impl_backend_only_backend_share_def impl_backend_share_escape_def by (rule refl)

chapter\<open> Generic inherent impl scopes \<close>

text\<open>
Impl declarations contribute no callable arguments. Their parameters constrain the target,
while each member adds its own declarations. These twins check the complete generated
functions; call twins also check explicit target and local-member instantiation.
\<close>

urust \<open>
  struct GenericPocket<T> { value: T }
  struct GenericBuffer<T, const N: usize> { value: [T; N] }

  impl<T> GenericPocket<T> {
    fn retain(self) -> Self { self }
    fn pass(value: T) -> T { value }
    fn replace<U>(self, value: U) -> U { value }
    fn relay<U>(self, value: U) -> U { Self::replace::<U>(self, value) }
    fn irrelevant(value: u8) -> u8 { value }
  }

  impl<'a, T, const N: usize> GenericBuffer<T, N> {
    fn retain(self) -> Self { self }
    fn capacity(self) -> usize { N }
    fn borrow(&'a mut self) -> &'a mut Self { self }
    fn replace<'b, U>(&'b mut self, value: U) -> U { value }
  }
\<close>

urust_fn [register_notation = false] generic_pocket_retain_twin \<open>
  fn RetainTwin<T>(self: GenericPocket<T>) -> GenericPocket<T> { self }
\<close>
urust_fn [register_notation = false] generic_pocket_pass_twin \<open>
  fn PassTwin<T>(value: T) -> T { value }
\<close>
urust_fn [register_notation = false] generic_pocket_replace_twin \<open>
  fn ReplaceTwin<T, U>(self: GenericPocket<T>, value: U) -> U { value }
\<close>
urust_fn [register_notation = false] generic_pocket_relay_control \<open>
  fn RelayControl<T, U>(self: GenericPocket<T>, value: U) -> U {
    \<epsilon>\<open>generic_pocket_replace\<close>(self, value)
  }
\<close>
urust_fn [register_notation = false] generic_pocket_irrelevant_twin \<open>
  fn IrrelevantTwin(value: u8) -> u8 { value }
\<close>
urust_fn [register_notation = false] generic_buffer_retain_twin \<open>
  fn BufferRetainTwin<T, const N: usize>(self: GenericBuffer<T, N>) -> GenericBuffer<T, N> { self }
\<close>
urust_fn [register_notation = false] generic_buffer_capacity_twin \<open>
  fn BufferCapacityTwin<T, const N: usize>(self: GenericBuffer<T, N>) -> usize { N }
\<close>
urust_fn [register_notation = false] generic_buffer_borrow_twin \<open>
  fn BufferBorrowTwin<'a, T, const N: usize>(self: &'a mut GenericBuffer<T, N>)
    -> &'a mut GenericBuffer<T, N> { self }
\<close>
urust_fn [register_notation = false] generic_buffer_replace_twin \<open>
  fn BufferReplaceTwin<'b, T, const N: usize, U>(self: &'b mut GenericBuffer<T, N>, value: U) -> U { value }
\<close>

lemma generic_pocket_retain_twin:
  \<open> generic_pocket_retain = generic_pocket_retain_twin \<close>
  unfolding generic_pocket_retain_def generic_pocket_retain_twin_def by (rule refl)
lemma generic_pocket_pass_twin:
  \<open> generic_pocket_pass = generic_pocket_pass_twin \<close>
  unfolding generic_pocket_pass_def generic_pocket_pass_twin_def by (rule refl)
lemma generic_pocket_replace_twin:
  \<open> generic_pocket_replace = generic_pocket_replace_twin \<close>
  unfolding generic_pocket_replace_def generic_pocket_replace_twin_def by (rule refl)
lemma generic_pocket_relay_twin:
  \<open> generic_pocket_relay = generic_pocket_relay_control \<close>
  unfolding generic_pocket_relay_def generic_pocket_relay_control_def by (rule refl)
lemma generic_pocket_irrelevant_twin:
  \<open> generic_pocket_irrelevant = generic_pocket_irrelevant_twin \<close>
  unfolding generic_pocket_irrelevant_def generic_pocket_irrelevant_twin_def by (rule refl)
lemma generic_buffer_retain_twin:
  \<open> generic_buffer_retain = generic_buffer_retain_twin \<close>
  unfolding generic_buffer_retain_def generic_buffer_retain_twin_def by (rule refl)
lemma generic_buffer_capacity_twin:
  \<open> generic_buffer_capacity = generic_buffer_capacity_twin \<close>
  unfolding generic_buffer_capacity_def generic_buffer_capacity_twin_def by (rule refl)
lemma generic_buffer_borrow_twin:
  \<open> generic_buffer_borrow = generic_buffer_borrow_twin \<close>
  unfolding generic_buffer_borrow_def generic_buffer_borrow_twin_def by (rule refl)
lemma generic_buffer_replace_twin:
  \<open> generic_buffer_replace = generic_buffer_replace_twin \<close>
  unfolding generic_buffer_replace_def generic_buffer_replace_twin_def by (rule refl)

urust_fn generic_impl_selected_call \<open>
  fn GenericImplSelectedCall(owner: GenericPocket<u8>, value: bool) -> bool {
    GenericPocket::<u8>::replace::<bool>(owner, value)
  }
\<close>
urust_fn generic_impl_inferred_call \<open>
  fn GenericImplInferredCall(owner: GenericPocket<u8>, value: bool) -> bool {
    GenericPocket::replace(owner, value)
  }
\<close>
urust_fn generic_impl_method_call \<open>
  fn GenericImplMethodCall(owner: GenericPocket<u8>, value: bool) -> bool {
    owner.replace::<bool>(value)
  }
\<close>
urust_fn [register_notation = false] generic_impl_call_twin \<open>
  fn GenericImplCallTwin(owner: GenericPocket<u8>, value: bool) -> bool {
    \<epsilon>\<open>generic_pocket_replace\<close>(owner, value)
  }
\<close>
lemma generic_impl_selected_call_twin:
  \<open> generic_impl_selected_call = generic_impl_call_twin \<close>
  unfolding generic_impl_selected_call_def generic_impl_call_twin_def by (rule refl)
lemma generic_impl_inferred_call_twin:
  \<open> generic_impl_inferred_call = generic_impl_call_twin \<close>
  unfolding generic_impl_inferred_call_def generic_impl_call_twin_def by (rule refl)
lemma generic_impl_method_call_twin:
  \<open> generic_impl_method_call = generic_impl_call_twin \<close>
  unfolding generic_impl_method_call_def generic_impl_call_twin_def by (rule refl)

section\<open> Erased target arguments and member witness demand \<close>

urust_type [erase = \<open> 'tag \<close>] "ImplDemandBox<'tag>" = \<open> unit \<close>
urust \<open>
  impl<T> ImplDemandBox<T> {
    fn pass(value: T) -> T { value }
    fn irrelevant(value: u8) -> u8 { value }
    fn local<U>(self, value: U) -> U { value }
  }
  fn ImplDemandSelected(value: u8) -> u8 { ImplDemandBox::<u8>::pass(value) }
  fn ImplDemandOpaque(value: u8) -> u8 { ImplDemandBox::<UnmappedTag>::irrelevant(value) }
  fn ImplDemandLocal(owner: ImplDemandBox<UnmappedTag>, value: bool) -> bool {
    ImplDemandBox::<UnmappedTag>::local::<bool>(owner, value)
  }
  fn ImplDemandSelectedTwin(value: u8) -> u8 { \<epsilon>\<open>impl_demand_box_pass\<close>(value) }
  fn ImplDemandOpaqueTwin(value: u8) -> u8 { \<epsilon>\<open>impl_demand_box_irrelevant\<close>(value) }
  fn ImplDemandLocalTwin(owner: ImplDemandBox<UnmappedTag>, value: bool) -> bool {
    \<epsilon>\<open>impl_demand_box_local\<close>(owner, value)
  }
\<close>
lemma impl_demand_selected_twin:
  \<open> impl_demand_selected = impl_demand_selected_twin \<close>
  unfolding impl_demand_selected_def impl_demand_selected_twin_def by (rule refl)
lemma impl_demand_opaque_twin:
  \<open> impl_demand_opaque = impl_demand_opaque_twin \<close>
  unfolding impl_demand_opaque_def impl_demand_opaque_twin_def by (rule refl)
lemma impl_demand_local_twin:
  \<open> impl_demand_local = impl_demand_local_twin \<close>
  unfolding impl_demand_local_def impl_demand_local_twin_def by (rule refl)

section\<open> Inherited member refinement and HOL parameter names \<close>

urust_trait "impl_scope::Ordered" = \<open> ord \<close>
urust \<open>
  impl<T> GenericPocket<T> {
    fn strengthened(self, value: T) -> T where T: impl_scope::Ordered { value }
    fn unchanged(self, value: T) -> T { value }
  }
  \<omega>\<open>hol_type_parameters = ["T" \<rightarrow> \<open>'payload::ord\<close>]\<close>
  impl<T> GenericPocket<T> {
    fn named(self, value: T) -> T { value }
    \<omega>\<open>name = "generic_pocket_named_local", hol_type_parameters = ["U" \<rightarrow> \<open>'local::type\<close>]\<close>
    fn local_named<U>(self, value: U) -> U { value }
  }
  \<omega>\<open>name = "generic_pocket_strengthened_control", register_notation = false\<close>
  fn StrengthenedControl<T: impl_scope::Ordered>(self: GenericPocket<T>, value: T) -> T { value }
  \<omega>\<open>name = "generic_pocket_unchanged_control", register_notation = false\<close>
  fn UnchangedControl<T>(self: GenericPocket<T>, value: T) -> T { value }
  \<omega>\<open>name = "generic_pocket_named_control", register_notation = false, hol_type_parameters = ["T" \<rightarrow> \<open>'payload::ord\<close>]\<close>
  fn NamedControl<T>(self: GenericPocket<T>, value: T) -> T { value }
  \<omega>\<open>name = "generic_pocket_named_local_control", register_notation = false,
    hol_type_parameters = ["T" \<rightarrow> \<open>'payload::ord\<close>, "U" \<rightarrow> \<open>'local::type\<close>]\<close>
  fn NamedLocalControl<T, U>(self: GenericPocket<T>, value: U) -> U { value }
\<close>
lemma generic_pocket_strengthened_twin:
  \<open> generic_pocket_strengthened = generic_pocket_strengthened_control \<close>
  unfolding generic_pocket_strengthened_def generic_pocket_strengthened_control_def by (rule refl)
lemma generic_pocket_unchanged_twin:
  \<open> generic_pocket_unchanged = generic_pocket_unchanged_control \<close>
  unfolding generic_pocket_unchanged_def generic_pocket_unchanged_control_def by (rule refl)
lemma generic_pocket_named_twin:
  \<open> generic_pocket_named = generic_pocket_named_control \<close>
  unfolding generic_pocket_named_def generic_pocket_named_control_def by (rule refl)
lemma generic_pocket_named_local_twin:
  \<open> generic_pocket_named_local = generic_pocket_named_local_control \<close>
  unfolding generic_pocket_named_local_def generic_pocket_named_local_control_def by (rule refl)

section\<open> Canonical aliases and lazy target witnesses \<close>

urust_type [erase = \<open> 'first, 'second \<close>]
  "ImplDemandPair<'first, 'second>" = \<open> unit \<close>
urust_type_alias \<open> type ImplDemandSwap<A, B> = ImplDemandPair<B, A>; \<close>
urust_type_alias \<open> type ImplDemandNested<A, B> = ImplDemandSwap<B, A>; \<close>
urust_type_alias \<open> type ImplDemandDiscard<const N: usize> = ImplDemandBox<u8>; \<close>
urust_type_alias \<open> type ImplDemandPointerTag = *const u8; \<close>
urust \<open>
  impl<Right, Left> ImplDemandSwap<Left, Right> {
    fn first(value: Right) -> Right { value }
    fn second(value: Left) -> Left { value }
  }
  impl<T> ImplDemandPair<T, T> {
    fn repeated(value: T) -> T { value }
  }
  impl<T: impl_scope::Ordered> GenericPocket<T> {
    fn inline_bound(self, value: T) -> T { value }
  }
  impl<T> GenericPocket<T> where T: impl_scope::Ordered {
    fn where_bound(self, value: T) -> T { value }
  }
  fn ImplDemandAliasFirst(value: u8) -> u8 { ImplDemandSwap::<bool, u8>::first(value) }
  fn ImplDemandAliasSecond(value: bool) -> bool { ImplDemandSwap::<bool, u8>::second(value) }
  fn ImplDemandNestedFirst(value: u8) -> u8 { ImplDemandNested::<u8, bool>::first(value) }
  fn ImplDemandRepeated(value: u8) -> u8 { ImplDemandPair::<u8, u8>::repeated(value) }
  fn ImplDemandLazy(value: u8) -> u8 { ImplDemandBox::<ImplDemandPointerTag>::irrelevant(value) }
  fn ImplDemandPointer(value: *const u8) -> *const u8 {
    ImplDemandBox::<ImplDemandPointerTag>::pass(value)
  }
  fn ImplDemandAliasFirstTwin(value: u8) -> u8 { \<epsilon>\<open>impl_demand_swap_first\<close>(value) }
  fn ImplDemandAliasSecondTwin(value: bool) -> bool { \<epsilon>\<open>impl_demand_swap_second\<close>(value) }
  fn ImplDemandNestedFirstTwin(value: u8) -> u8 { \<epsilon>\<open>impl_demand_swap_first\<close>(value) }
  fn ImplDemandRepeatedTwin(value: u8) -> u8 { \<epsilon>\<open>impl_demand_pair_repeated\<close>(value) }
  fn ImplDemandLazyTwin(value: u8) -> u8 { \<epsilon>\<open>impl_demand_box_irrelevant\<close>(value) }
  fn ImplDemandPointerTwin(value: *const u8) -> *const u8 { \<epsilon>\<open>impl_demand_box_pass\<close>(value) }
  \<omega>\<open>name = "generic_pocket_bound_control", register_notation = false\<close>
  fn BoundControl<T: impl_scope::Ordered>(self: GenericPocket<T>, value: T) -> T { value }
\<close>
lemma impl_demand_alias_first_twin:
  \<open> impl_demand_alias_first = impl_demand_alias_first_twin \<close>
  unfolding impl_demand_alias_first_def impl_demand_alias_first_twin_def by (rule refl)
lemma impl_demand_alias_second_twin:
  \<open> impl_demand_alias_second = impl_demand_alias_second_twin \<close>
  unfolding impl_demand_alias_second_def impl_demand_alias_second_twin_def by (rule refl)
lemma impl_demand_nested_first_twin:
  \<open> impl_demand_nested_first = impl_demand_nested_first_twin \<close>
  unfolding impl_demand_nested_first_def impl_demand_nested_first_twin_def by (rule refl)
lemma impl_demand_repeated_twin:
  \<open> impl_demand_repeated = impl_demand_repeated_twin \<close>
  unfolding impl_demand_repeated_def impl_demand_repeated_twin_def by (rule refl)
lemma impl_demand_lazy_twin:
  \<open> impl_demand_lazy = impl_demand_lazy_twin \<close>
  unfolding impl_demand_lazy_def impl_demand_lazy_twin_def by (rule refl)
lemma impl_demand_pointer_twin:
  \<open> impl_demand_pointer = impl_demand_pointer_twin \<close>
  unfolding impl_demand_pointer_def impl_demand_pointer_twin_def by (rule refl)
lemma generic_pocket_inline_bound_twin:
  \<open> generic_pocket_inline_bound = generic_pocket_bound_control \<close>
  unfolding generic_pocket_inline_bound_def generic_pocket_bound_control_def by (rule refl)
lemma generic_pocket_where_bound_twin:
  \<open> generic_pocket_where_bound = generic_pocket_bound_control \<close>
  unfolding generic_pocket_where_bound_def generic_pocket_bound_control_def by (rule refl)

section\<open> Generic owner imports, explicit calls and locale transports \<close>

urust \<open>
  use GenericPocket as ImportedGenericPocket;
  fn GenericImplImported(owner: GenericPocket<u8>, value: bool) -> bool {
    ImportedGenericPocket::<u8>::replace::<bool>(owner, value)
  }
  impl<T> GenericPocket<T> {
    fn notation_choice(self) -> Self { self }
  }
\<close>
micro_rust_notation (call) generic_pocket_notation_choice ("notation_choice")
urust \<open>
  fn GenericImplExplicitNotation(owner: GenericPocket<u8>) -> GenericPocket<u8> {
    owner.notation_choice()
  }
  fn GenericImplExplicitNotationTwin(owner: GenericPocket<u8>) -> GenericPocket<u8> {
    \<epsilon>\<open>generic_pocket_notation_choice\<close>(owner)
  }
\<close>
lemma generic_impl_imported_twin:
  \<open> generic_impl_imported = generic_impl_call_twin \<close>
  unfolding generic_impl_imported_def generic_impl_call_twin_def by (rule refl)
lemma generic_impl_explicit_notation_twin:
  \<open> generic_impl_explicit_notation = generic_impl_explicit_notation_twin \<close>
  unfolding generic_impl_explicit_notation_def generic_impl_explicit_notation_twin_def by (rule refl)

urust_type "ImplLocalePair<'payload, 'ambient>" = \<open> 'payload * 'ambient \<close>
locale generic_impl_locale =
  fixes generic_impl_seed :: 'ambient
begin
urust \<open>
  impl<T> ImplLocalePair<T, \<tau>\<open>'ambient\<close>> {
    fn locale_replace<U>(self, value: U) -> U { value }
    fn ambient(self) -> \<tau>\<open>'ambient\<close> { generic_impl_seed }
  }
\<close>
end
interpretation generic_impl_nat: generic_impl_locale "0 :: nat" .
interpretation generic_impl_bool: generic_impl_locale False .
urust \<open>
  fn GenericImplLocaleNat(owner: ImplLocalePair<u8, \<tau>\<open>nat\<close>>, value: bool) -> bool {
    ImplLocalePair::<u8, \<tau>\<open>nat\<close>>::locale_replace::<bool>(owner, value)
  }
  fn GenericImplLocaleBool(owner: ImplLocalePair<u8, bool>, value: u8) -> u8 {
    owner.locale_replace::<u8>(value)
  }
  fn GenericImplLocaleAmbient(owner: ImplLocalePair<u8, \<tau>\<open>nat\<close>>) -> \<tau>\<open>nat\<close> {
    ImplLocalePair::<u8, \<tau>\<open>nat\<close>>::ambient(owner)
  }
  fn GenericImplLocaleNatTwin(owner: ImplLocalePair<u8, \<tau>\<open>nat\<close>>, value: bool) -> bool {
    \<epsilon>\<open>generic_impl_locale.impl_locale_pair_locale_replace\<close>(owner, value)
  }
  fn GenericImplLocaleBoolTwin(owner: ImplLocalePair<u8, bool>, value: u8) -> u8 {
    \<epsilon>\<open>generic_impl_locale.impl_locale_pair_locale_replace\<close>(owner, value)
  }
  fn GenericImplLocaleAmbientTwin(owner: ImplLocalePair<u8, \<tau>\<open>nat\<close>>) -> \<tau>\<open>nat\<close> {
    \<epsilon>\<open>generic_impl_nat.impl_locale_pair_ambient\<close>(owner)
  }
\<close>
lemma generic_impl_locale_nat_twin:
  \<open> generic_impl_locale_nat = generic_impl_locale_nat_twin \<close>
  unfolding generic_impl_locale_nat_def generic_impl_locale_nat_twin_def by (rule refl)
lemma generic_impl_locale_bool_twin:
  \<open> generic_impl_locale_bool = generic_impl_locale_bool_twin \<close>
  unfolding generic_impl_locale_bool_def generic_impl_locale_bool_twin_def by (rule refl)
lemma generic_impl_locale_ambient_twin:
  \<open> generic_impl_locale_ambient = generic_impl_locale_ambient_twin \<close>
  unfolding generic_impl_locale_ambient_def generic_impl_locale_ambient_twin_def by (rule refl)

section\<open> Pure source forwarding in an irrelevant member \<close>

text\<open>
An authoritative Rust body may forward an inherited source tag to another erased slot without
requesting its HOL witness. This member and its control have the same complete HOL type;
a body read that needs the absent witness is separately rejected.
\<close>
urust \<open>
  impl<T> ImplDemandBox<T> {
    fn source_forward(value: u8) -> u8 { ImplDemandBox::<T>::irrelevant(value) }
  }
  \<omega>\<open>register_notation = false\<close>
  fn ImplDemandSourceForwardTwin(value: u8) -> u8 { \<epsilon>\<open>impl_demand_box_irrelevant\<close>(value) }
\<close>
lemma impl_demand_source_forward_twin:
  \<open> impl_demand_box_source_forward = impl_demand_source_forward_twin \<close>
  unfolding impl_demand_box_source_forward_def impl_demand_source_forward_twin_def by (rule refl)

section\<open> Concrete owner selection through equivalent HOL types \<close>

urust \<open>
  fn GenericConcreteHOLChoice(owner: Duo<u8>) -> u8 {
    Duo::<\<tau>\<open>8 word\<close>>::sum(owner)
  }
  fn GenericConcreteHOLChoiceTwin(owner: Duo<u8>) -> u8 {
    \<epsilon>\<open>duo_byte_sum\<close>(owner)
  }
\<close>

lemma generic_concrete_hol_choice_twin:
  \<open> generic_concrete_hol_choice = generic_concrete_hol_choice_twin \<close>
  unfolding generic_concrete_hol_choice_def generic_concrete_hol_choice_twin_def
  by (rule refl)


section\<open> Outlives on generic impls and members \<close>

text\<open>
The impl and member lifetime environments are combined only while each header is checked.
Their relations erase; explicit receivers and ordinary calls retain their complete channels.
\<close>

urust \<open>
  struct OutlivesPocket<T> { value: T }
  impl<'a, 'b: 'a, T: 'b> OutlivesPocket<T>
  where Self: 'static, &'a Self: 'b {
    fn carry<'c: 'b, U: 'c>(&'a mut self, value: &'c mut U) -> &'c mut U
    where T: 'c { value }
    fn bare(value: u8) -> u8 { value }
  }
  \<omega>\<open>register_notation = false\<close>
  fn OutlivesPocketCarryPlain<'a, 'c, T, U>(owner: &'a mut OutlivesPocket<T>, value: &'c mut U)
    -> &'c mut U { value }
  fn OutlivesPocketCall<'a, 'c>(owner: &'a mut OutlivesPocket<u8>, value: &'c mut bool)
    -> &'c mut bool { OutlivesPocket::<u8>::carry::<bool>(owner, value) }
  fn OutlivesPocketMethod<'a, 'c>(owner: &'a mut OutlivesPocket<u8>, value: &'c mut bool)
    -> &'c mut bool { owner.carry::<bool>(value) }
  fn OutlivesPocketCallPlain<'a, 'c>(owner: &'a mut OutlivesPocket<u8>, value: &'c mut bool)
    -> &'c mut bool { \<epsilon>\<open>outlives_pocket_carry\<close>(owner, value) }
\<close>
lemma outlives_pocket_carry_erased:
  \<open> outlives_pocket_carry = outlives_pocket_carry_plain \<close>
  unfolding outlives_pocket_carry_def outlives_pocket_carry_plain_def by (rule refl)
lemma outlives_pocket_call_erased:
  \<open> outlives_pocket_call = outlives_pocket_call_plain \<close>
  unfolding outlives_pocket_call_def outlives_pocket_call_plain_def by (rule refl)
lemma outlives_pocket_method_erased:
  \<open> outlives_pocket_method = outlives_pocket_call_plain \<close>
  unfolding outlives_pocket_method_def outlives_pocket_call_plain_def by (rule refl)

urust \<open>
  struct OutlivesMixedOwner<T> { value: T }
  impl<'a, T: 'a> OutlivesMixedOwner<T> {
    fn ordered(self, value: T) -> T where T: 'a + impl_scope::Ordered + 'static { value }
    fn sibling(self, value: T) -> T where T: 'a { value }
  }
  fn OutlivesMixedOrderedPlain<T: impl_scope::Ordered>(owner: OutlivesMixedOwner<T>, value: T) -> T { value }
  fn OutlivesMixedSiblingPlain<T>(owner: OutlivesMixedOwner<T>, value: T) -> T { value }
\<close>
lemma outlives_mixed_ordered_erased:
  \<open> outlives_mixed_owner_ordered = outlives_mixed_ordered_plain \<close>
  unfolding outlives_mixed_owner_ordered_def outlives_mixed_ordered_plain_def by (rule refl)
lemma outlives_mixed_sibling_erased:
  \<open> outlives_mixed_owner_sibling = outlives_mixed_sibling_plain \<close>
  unfolding outlives_mixed_owner_sibling_def outlives_mixed_sibling_plain_def by (rule refl)

urust_type [erase = \<open>'tag\<close>] "OutlivesErasedBox<'tag>" = \<open> unit \<close>
urust \<open>
  impl<'a, T: 'a> OutlivesErasedBox<T> where Self: 'static, Unknown<T>: 'a {
    fn irrelevant(value: u8) -> u8 { value }
    fn source_forward<'b: 'a>(value: u8) -> u8 where T: 'b {
      OutlivesErasedBox::<T>::irrelevant(value)
    }
  }
  fn OutlivesErasedForwardPlain(value: u8) -> u8 {
    \<epsilon>\<open>outlives_erased_box_irrelevant\<close>(value)
  }
\<close>
lemma outlives_erased_forward_erased:
  \<open> outlives_erased_box_source_forward = outlives_erased_forward_plain \<close>
  unfolding outlives_erased_box_source_forward_def outlives_erased_forward_plain_def by (rule refl)

urust_type "OutlivesLocalePair<'payload, 'ambient>" = \<open> 'payload * 'ambient \<close>
locale outlives_impl_locale = fixes outlives_seed :: 'ambient
begin
urust \<open>
  impl<'a, T: 'a> OutlivesLocalePair<T, \<tau>\<open>'ambient\<close>> where Self: 'static {
    fn replace<'b: 'a, U: 'b>(self, value: U) -> U where T: 'b { value }
    fn ambient(self) -> \<tau>\<open>'ambient\<close> { outlives_seed }
  }
\<close>
end
interpretation outlives_nat: outlives_impl_locale "0 :: nat" .
interpretation outlives_bool: outlives_impl_locale False .
urust \<open>
  fn OutlivesLocaleCall(owner: OutlivesLocalePair<u8, \<tau>\<open>nat\<close>>, value: bool) -> bool {
    OutlivesLocalePair::<u8, \<tau>\<open>nat\<close>>::replace::<bool>(owner, value)
  }
  fn OutlivesLocaleCallPlain(owner: OutlivesLocalePair<u8, \<tau>\<open>nat\<close>>, value: bool) -> bool {
    \<epsilon>\<open>outlives_impl_locale.outlives_locale_pair_replace\<close>(owner, value)
  }
  fn OutlivesLocaleAmbient(owner: OutlivesLocalePair<u8, \<tau>\<open>nat\<close>>) -> \<tau>\<open>nat\<close> {
    OutlivesLocalePair::<u8, \<tau>\<open>nat\<close>>::ambient(owner)
  }
  fn OutlivesLocaleAmbientPlain(owner: OutlivesLocalePair<u8, \<tau>\<open>nat\<close>>) -> \<tau>\<open>nat\<close> {
    \<epsilon>\<open>outlives_nat.outlives_locale_pair_ambient\<close>(owner)
  }
\<close>
lemma outlives_locale_call_erased: \<open> outlives_locale_call = outlives_locale_call_plain \<close>
  unfolding outlives_locale_call_def outlives_locale_call_plain_def by (rule refl)
lemma outlives_locale_ambient_erased:
  \<open> outlives_locale_ambient = outlives_locale_ambient_plain \<close>
  unfolding outlives_locale_ambient_def outlives_locale_ambient_plain_def by (rule refl)

end
