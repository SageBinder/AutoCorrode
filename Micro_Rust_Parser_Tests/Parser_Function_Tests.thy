(* Readable urust_fn syntax examples; internal audits are in Parser_Function_Regression_Tests. *)

theory Parser_Function_Tests
  imports
    Parser_Iterator_Fixtures
    Parser_Logging_Fixtures
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]
declare [[urust_register_notation = true]]

chapter\<open> Function declaration syntax \<close>

text\<open>
Each declaration contains one complete Rust function item. Parameter and explicit result
types determine the HOL type. An outer name selects the HOL binding; omitting it derives
a snake-case name from the Rust name, and an outer underscore checks anonymously.
Start with these examples; the companion regression theory checks their artifacts,
diagnostics, type inference, registration, printer roundtrips and navigation.
\<close>


section\<open> Explicit, inferred and anonymous names \<close>

urust_fn explicit_hol_name
  \<open>
    fn RustAlias(x: u64, _: bool) -> u64 {
      x
    }
  \<close>

urust_fn
  \<open>
    fn HTTPServer() {
      ()
    }
  \<close>

urust_fn _
  \<open>
    fn AnonymousProbe(x: u64) -> bool {
      x == 0
    }
  \<close>


urust_fn registered_probe
  \<open>
    fn probe(x: u64) -> bool {
      x == 0
    }
  \<close>

urust_fn [register_notation = false] call_registered_probe
  \<open> fn call_registered_probe(x: u64) -> bool { probe(x) } \<close>

urust_fn
  \<open>
    fn HTTP2XMLParser() {
      ()
    }
  \<close>

urust_fn already_snake
  \<open>
    fn already_snake() {
      ()
    }
  \<close>


section\<open> Authoritative signatures and parameter forms \<close>

urust_fn authoritative_signature
  \<open>
    fn AuthoritativeSignature(x: u64) -> u64 {
      x + 1
    }
  \<close>

urust_fn mutable_parameter
  \<open>
    fn MutableParameter(mut x: u64) -> u64 {
      x
    }
  \<close>

urust_fn mixed_parameter_slots
  \<open>
    fn MixedParameterSlots(
      first: \<tau>\<open>nat\<close>,
      _: bool,
      mut retained: \<tau>\<open>nat\<close>,
      _: (),
    ) -> \<tau>\<open>nat\<close> {
      retained
    }
  \<close>

urust_fn empty_block
  \<open>
    fn EmptyBlock() {}
  \<close>

urust_fn commented_signature
  \<open>
    fn
    \<comment> \<open>A formal comment may occur while scanning the signature.\<close>
    /* before the function name */
    CommentedSignature(
      /* before the parameter */ value /* before the colon */ :
        /* outer /* nested */ comment */ u64, // trailing line comment
    )
    /* before the return arrow */ -> /* before the return type */ u64 {
      value
    }
  \<close>


section\<open> Abbreviations and application definitions \<close>

urust_fn [abbrev] abbreviated_hol_name
  \<open>
    fn AbbreviatedRustName(x: u64) -> u64 {
      x
    }
  \<close>

urust_fn [register_notation = false] call_abbreviated_rust_name
  \<open> fn call_abbreviated_rust_name(x: u64) -> u64 { AbbreviatedRustName(x) } \<close>

urust_fn [application_def, attrs = [micro_rust_simps]]
  attributed_application_function
  \<open>
    fn AttributedApplication(x: u64) -> u64 {
      x
    }
  \<close>


section\<open> Registered calls and argument boundaries \<close>

urust_fn rust_maximum_call_arity
  \<open>
    fn RustMaximumCallArity(
      p01: \<tau>\<open>nat\<close>, p02: \<tau>\<open>nat\<close>, p03: \<tau>\<open>nat\<close>, p04: \<tau>\<open>nat\<close>,
      p05: \<tau>\<open>nat\<close>, p06: \<tau>\<open>nat\<close>, p07: \<tau>\<open>nat\<close>, p08: \<tau>\<open>nat\<close>,
      p09: \<tau>\<open>nat\<close>, p10: \<tau>\<open>nat\<close>, p11: \<tau>\<open>nat\<close>, p12: \<tau>\<open>nat\<close>,
      p13: \<tau>\<open>nat\<close>, p14: \<tau>\<open>nat\<close>,
    ) -> \<tau>\<open>nat\<close> {
      p14
    }
  \<close>

urust_fn invoke_rust_maximum_call_arity
  \<open>
    fn InvokeRustMaximumCallArity() -> \<tau>\<open>nat\<close> {
      RustMaximumCallArity(
        1, 2, 3, 4, 5, 6, 7,
        8, 9, 10, 11, 12, 13, 14,
      )
    }
  \<close>

urust_fn
  [pp_test, pretty, verbosity = 2]
  configured_function
  \<open>
    fn ConfiguredFunction(x: u64) -> u64 {
      x
    }
  \<close>

urust_fn completed_result_type
  \<open>
    fn CompletedResultType(x: u64,) {
      x
    }
  \<close>

urust_fn omitted_rust_return_type
  \<open>
    fn InferredReturn(x: u64) {
      x
    }
  \<close>


section\<open> Lexical parameters and Rust callable names \<close>

urust_fn lexical_function_shadow
  \<open>
    fn LexicalFunctionShadow(RustAlias: \<tau>\<open>(64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body)\<close>, x: u64) -> u64 {
      RustAlias(x)
    }
  \<close>

urust_fn [register_notation = false] call_registered_function
  \<open> fn call_registered_function(x: u64) -> u64 { RustAlias(x, true) } \<close>

urust_fn _
  \<open>
    fn RustAlias(x: u64, _: bool) -> u64 {
      x
    }
  \<close>


urust_fn [register_notation = false] call_inferred_function
  \<open> fn call_inferred_function() -> () { HTTPServer() } \<close>


section\<open> Locale scope \<close>

locale rust_function_item_locale =
  fixes offset :: nat
begin

urust_fn locale_scoped_function
  \<open>
    fn LocaleScopedFunction(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>value + offset\<rrangle>
    }
  \<close>

urust_fn locale_scoped_client
  \<open>
    fn LocaleScopedClient(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      LocaleScopedFunction(value)
    }
  \<close>

end


urust_fn global_after_locale_scope
  \<open>
    fn LocaleScopedFunction(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      value
    }
  \<close>


section\<open> Inline and scoped registration options \<close>

text\<open>
Named functions register their Rust name by default. Inline options override the scoped
setting. Disabling registration still creates the named HOL definition.
\<close>

urust_fn [register_notation] bare_registered \<open>
  fn BareRegistered(value: u32) -> u32 { value }
\<close>

urust_fn [register_notation = true] explicitly_registered \<open>
  fn ExplicitlyRegistered(value: u32) -> u32 { BareRegistered(value) }
\<close>

urust_fn [register_notation = false] unregistered_helper \<open>
  fn UnregisteredHelper(value: u32) -> u32 { value }
\<close>

context notes [[urust_register_notation = false]]
begin

urust_fn scoped_unregistered_helper \<open>
  fn ScopedUnregisteredHelper(value: u32) -> u32 { value }
\<close>

urust_fn [register_notation] scoped_registered_override \<open>
  fn ScopedRegisteredOverride(value: u32) -> u32 { ExplicitlyRegistered(value) }
\<close>

end

chapter\<open> Function bodies and lexical binding \<close>

section\<open> Function bodies \<close>

urust_fn [register_notation = false] answer
  \<open> fn answer() -> u32 { \<llangle>42 :: 32 word\<rrangle> } \<close>
urust_fn [register_notation = false] inc
  \<open> fn inc(x: u32) -> u32 { x + \<llangle>1 :: 32 word\<rrangle> } \<close>

urust_fn [register_notation = false] add3
  \<open> fn add3(a: u32, b: u32, c: u32) -> u32 { a + b + c } \<close>

urust_fn [register_notation = false] is_zero
  \<open> fn is_zero(x: u32) -> bool { x == \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_fn [register_notation = false] safe_div
  \<open>
    fn safe_div(a: u32, b: u32) -> \<tau>\<open>(32 word, unit) result\<close> {
      if b == \<llangle>0 :: 32 word\<rrangle> { Err(()) } else { Ok(a / b) }
    }
  \<close>

urust_fn [register_notation = false] discard
  \<open> fn discard(x: u32) -> () { () } \<close>

urust_fn [register_notation = false] test
  \<open>
    fn test() -> () {
      let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return;
    }
  \<close>
hide_const test


section\<open> Signature surface \<close>

urust_fn [register_notation = false] fun_heterogeneous
  \<open>
    fn fun_heterogeneous(number: \<tau>\<open>nat\<close>, flag: bool, word: u32) -> \<tau>\<open>nat * bool * 32 word\<close> {
      \<llangle>(number, flag, word)\<rrangle>
    }
  \<close>

urust_fn [register_notation = false] fun_polymorphic
  \<open> fn fun_polymorphic(item: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { item } \<close>

urust_fn [register_notation = false] fun_sort_constrained
  \<open>
    fn fun_sort_constrained(item: \<tau>\<open>'a::len word\<close>) -> \<tau>\<open>'a word\<close> {
      item
    }
  \<close>

urust_fn [register_notation = false] fun_type_placeholders
  \<open> fn fun_type_placeholders(item: \<tau>\<open>_\<close>) { item } \<close>

urust_fn [register_notation = false] fun_higher_order
  \<open>
    fn fun_higher_order(f: \<tau>\<open>(nat \<Rightarrow> nat)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>f item\<rrangle>
    }
  \<close>

urust_fn [register_notation = false] fun_nested_result
  \<open>
    fn fun_nested_result() -> \<tau>\<open>(nat option, (bool, unit) result) result\<close> {
      Ok(Some(\<llangle>1 :: nat\<rrangle>))
    }
  \<close>

urust_fn [register_notation = false] fun_generalized_effects
  \<open>
    fn fun_generalized_effects(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>


section\<open> Argument-list boundaries \<close>

urust_fn [register_notation = false] fun_zero_arguments
  \<open> fn fun_zero_arguments() -> () { () } \<close>

urust_fn [register_notation = false] fun_one_argument
  \<open>
    fn fun_one_argument(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn [register_notation = false] fun_trailing_comma
  \<open>
    fn fun_trailing_comma(item: \<tau>\<open>nat\<close>, flag: bool,) -> \<tau>\<open>nat * bool\<close> {
      \<llangle>(item, flag)\<rrangle>
    }
  \<close>

urust_fn [register_notation = false] fun_multiline_arguments
  \<open>
    fn fun_multiline_arguments(
      number: \<tau>\<open>nat\<close>,
      flag: bool,
      word: u32,
    ) -> u32 {
      if flag { word } else { \<llangle>of_nat number\<rrangle> }
    }
  \<close>

urust_fn [register_notation = false] fun_sixteen_arguments
  \<open>
    fn fun_sixteen_arguments(
      p01: \<tau>\<open>nat\<close>, p02: \<tau>\<open>nat\<close>,
      p03: \<tau>\<open>nat\<close>, p04: \<tau>\<open>nat\<close>,
      p05: \<tau>\<open>nat\<close>, p06: \<tau>\<open>nat\<close>,
      p07: \<tau>\<open>nat\<close>, p08: \<tau>\<open>nat\<close>,
      p09: \<tau>\<open>nat\<close>, p10: \<tau>\<open>nat\<close>,
      p11: \<tau>\<open>nat\<close>, p12: \<tau>\<open>nat\<close>,
      p13: \<tau>\<open>nat\<close>, p14: \<tau>\<open>nat\<close>,
      p15: \<tau>\<open>nat\<close>, p16: \<tau>\<open>nat\<close>,
    ) -> \<tau>\<open>nat\<close> {
      \<llangle>
        p01 + p02 + p03 + p04 + p05 + p06 + p07 + p08 +
        p09 + p10 + p11 + p12 + p13 + p14 + p15 + p16
      \<rrangle>
    }
  \<close>


section\<open> Ambient binding and scope \<close>

urust_fn [register_notation = false] fun_plain_parameter
  \<open>
    fn fun_plain_parameter(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn [register_notation = false] fun_prime_parameter
  \<open>
    fn fun_prime_parameter(item': \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item'
    }
  \<close>

urust_fn [register_notation = false] fun_value_antiquotation
  \<open>
    fn fun_value_antiquotation(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>item + 1\<rrangle>
    }
  \<close>

urust_fn [register_notation = false] fun_expression_antiquotation
  \<open>
    fn fun_expression_antiquotation(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<epsilon>\<open>literal (item + 1)\<close>
    }
  \<close>

urust_fn [register_notation = false] fun_parameter_call
  \<open>
    fn fun_parameter_call(callee: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      callee(item)
    }
  \<close>

urust_fn [register_notation = false] fun_parameter_in_match_guard
  \<open>
  fn fun_parameter_in_match_guard(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    match Some(item) {
      Some(inner) if inner == item \<Rightarrow> inner,
      _ \<Rightarrow> item
    }
  }
  \<close>

urust_fn [register_notation = false] fun_parameter_in_loop
  \<open>
  fn fun_parameter_in_loop(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) {
      let observed = item;
      ()
    }
    item
  }
  \<close>

urust_fn [register_notation = false] fun_parameter_in_closure
  \<open>
    fn fun_parameter_in_closure(outer: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> {
      |inner| \<llangle>outer + inner\<rrangle>
    }
  \<close>

datatype fun_struct_fixture = FunStructFixture nat bool

definition fun_struct_fixture_lift ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, fun_struct_fixture, unit, unit, unit) function_body\<close>
  where \<open>fun_struct_fixture_lift \<equiv> lift_fun2 FunStructFixture\<close>

micro_rust_notation (call) fun_struct_fixture_lift ("FunStructFixture")

urust_fn [register_notation = false] fun_parameter_in_struct
  \<open>
    fn fun_parameter_in_struct(item: \<tau>\<open>nat\<close>, flag: bool) -> \<tau>\<open>fun_struct_fixture\<close> {
      FunStructFixture { item: item, flag: flag }
    }
  \<close>

urust_fn [register_notation = false] fun_nested_let_shadow
  \<open>
    fn fun_nested_let_shadow(item: \<tau>\<open>nat\<close>) -> bool {
      let item = true; item
    }
  \<close>

urust_fn [register_notation = false] fun_nested_pattern_shadow
  \<open>
  fn fun_nested_pattern_shadow(item: \<tau>\<open>nat\<close>) -> bool {
    let (item, retained) = (true, \<llangle>item\<rrangle>);
    item
  }
  \<close>

urust_fn [register_notation = false] fun_closure_shadow
  \<open>
    fn fun_closure_shadow(item: bool) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> {
      |item| \<llangle>item :: nat\<rrangle>
    }
  \<close>

context
  fixes item :: bool
begin

urust_fn [register_notation = false] fun_parameter_shadows_context
  \<open>
    fn fun_parameter_shadows_context(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>item :: nat\<rrangle>
    }
  \<close>

end

urust_fn [register_notation = false] fun_distinct_heterogeneous
  \<open>
    fn fun_distinct_heterogeneous(number: \<tau>\<open>nat\<close>, flag: bool, message: \<tau>\<open>String.literal\<close>) -> \<tau>\<open>nat * bool * String.literal\<close> {
      \<llangle>(number, flag, message)\<rrangle>
    }
  \<close>


section\<open> Role-specific notation precedence \<close>

definition fun_registered_literal :: nat
  where \<open>fun_registered_literal = 99\<close>

definition fun_registered_call ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open>fun_registered_call \<equiv> lift_fun1 (\<lambda>x. x + 10)\<close>

datatype_record fun_field_record =
  fun_field_value :: nat
micro_rust_record fun_field_record
  (fun_field_value = "funFieldCollision")

micro_rust_notation (literal) fun_registered_literal ("funCollision")
micro_rust_notation (call) fun_registered_call ("funCollision")

urust_fn [register_notation = false] fun_parameter_call_wins
  \<open>
    fn fun_parameter_call_wins(funCollision: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      funCollision(item)
    }
  \<close>

urust_fn [register_notation = false] fun_registered_field_wins
  \<open>
    fn fun_registered_field_wins(item: \<tau>\<open>fun_field_record\<close>, funFieldCollision: \<tau>\<open>(fun_field_record, nat) lens\<close>) -> \<tau>\<open>nat\<close> {
      item.funFieldCollision
    }
  \<close>

section\<open> Isabelle declaration integration \<close>

context
begin

qualified urust_fn [register_notation = false] qualified_identity
  \<open>
    fn qualified_identity(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

end

locale fun_command_locale =
  fixes offset :: nat
begin

urust_fn [register_notation = false] local_add
  \<open>
    fn local_add(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>item + offset\<rrangle>
    }
  \<close>

end

section\<open> Iterator calls \<close>

text\<open>
The direct, method, and chained forms all use the normal call pipeline. The method form contributes
exactly one receiver and one explicit argument.
\<close>

urust_fn [register_notation = false] iterator_zip_direct
  \<open>
    fn iterator_zip_direct(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> {
      zip(left, right)
    }
  \<close>

urust_fn [register_notation = false] iterator_zip_method
  \<open>
    fn iterator_zip_method(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> {
      left.zip(right)
    }
  \<close>

urust_fn [register_notation = false] iterator_zip_chained
  \<open>
    fn iterator_zip_chained(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> {
      left.into_iter().zip(right.into_iter())
    }
  \<close>

chapter\<open> Declaration options and parameter slots \<close>


section\<open> Application equations and attributes \<close>

urust_fn [application_def, register_notation = false]
  typed_application_function
  \<open>
    fn typed_application_function(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn [register_notation = false] typed_zero_function_default
  \<open>
    fn typed_zero_function_default() -> \<tau>\<open>nat\<close> {
      \<llangle>7 :: nat\<rrangle>
    }
  \<close>

urust_fn [application_def, register_notation = false] typed_zero_function_application
  \<open>
    fn typed_zero_function_application() -> \<tau>\<open>nat\<close> {
      \<llangle>7 :: nat\<rrangle>
    }
  \<close>

section\<open> Parameter names and notation precedence \<close>

definition command_parameter_collision :: nat
  where \<open> command_parameter_collision = 17 \<close>

urust_notation (literal)
  command_parameter_collision ("command_parameter_collision")

definition command_registered_zip ::
    \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> command_registered_zip \<equiv> lift_fun1 (\<lambda>item. item + 1) \<close>

urust_notation (call) command_registered_zip ("zip")

urust_fn [attrs = [], register_notation = false]
  partial_collision_function
  \<open>
    fn partial_collision_function(command_parameter_collision: \<tau>\<open>nat\<close>) {
      command_parameter_collision
    }
  \<close>

urust_fn [attrs = [micro_rust_simps], register_notation = false]
  partial_internal_placeholder
  \<open>
    fn partial_internal_placeholder(item: \<tau>\<open>_\<close>) {
      \<llangle>item :: nat\<rrangle>
    }
  \<close>

urust_fn [register_notation = false] zip_parameter_value
  \<open> fn zip_parameter_value(zip: \<tau>\<open>nat\<close>) { zip } \<close>

urust_fn [register_notation = false] zip_callable_parameter
  \<open>
    fn zip_callable_parameter(zip: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) {
      zip(item)
    }
  \<close>

urust_fn [register_notation = false] zip_method_registration
  \<open>
    fn zip_method_registration(zip: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) {
      item.zip()
    }
  \<close>

urust_fn [register_notation = false] quoted_major_parameter
  \<open> fn quoted_major_parameter(lemma: \<tau>\<open>nat\<close>) { lemma } \<close>

section\<open> Wildcard parameter slots \<close>

urust_fn [register_notation = false] wildcard_function_single
  \<open> fn wildcard_function_single(_: \<tau>\<open>nat\<close>) -> () { () } \<close>

urust_fn [register_notation = false] wildcard_function_mixed
  \<open>
    fn wildcard_function_mixed(_: \<tau>\<open>nat\<close>, kept: bool, _: u32) -> bool {
      kept
    }
  \<close>

urust_fn [register_notation = false] wildcard_function_inferred
  \<open>
    fn wildcard_function_inferred(_: \<tau>\<open>_\<close>) {
      \<llangle>0 :: nat\<rrangle>
    }
  \<close>

urust_fn [application_def, register_notation = false] wildcard_function_application
  \<open> fn wildcard_function_application(_: \<tau>\<open>nat\<close>) -> () { () } \<close>

urust_fn [abbrev, register_notation = false] wildcard_function_abbreviation
  \<open>
    fn wildcard_function_abbreviation(_: \<tau>\<open>nat\<close>, kept: bool) -> bool {
      kept
    }
  \<close>

section\<open> Anonymous checks and abbreviations \<close>

urust_fn [application_def, register_notation = false] _
  \<open>
    fn AnonymousFunction(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn
  [abbrev, verbosity = 2, register_notation = false]
  typed_function_abbrev_command
  \<open>
    fn typed_function_abbrev_command(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

section\<open> Pretty-printer options \<close>

urust_fn [pp_test = false, register_notation = false] pp_fun_disabled
  \<open>
    fn pp_fun_disabled(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn [pp_test, register_notation = false] pp_fun_enabled
  \<open> fn pp_fun_enabled(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>

lemma pp_fun_enabled_same:
  \<open>pp_fun_enabled = pp_fun_disabled\<close>
  unfolding pp_fun_enabled_def pp_fun_disabled_def
  by (rule refl)


chapter\<open> Mapped signatures, HOL types and inferred effects \<close>


section\<open> Custom and generated Rust type mappings \<close>

urust_type "SignatureCount" = \<open> nat \<close>
urust_type "signature::Flag" = \<open> bool \<close>
urust_type "SignatureOption<'value>" = \<open> 'value option \<close>
urust_type "SignatureResult<'ok, 'err>" = \<open> ('ok, 'err) result \<close>
urust_type "SignatureOrdered<'value>" = \<open> 'value::linorder list \<close>
urust_type "SignatureFinite<'value>" = \<open> 'value::finite list \<close>
urust_type "SignatureFunction" = \<open> nat \<Rightarrow> nat \<close>
urust_type "signature::Header<'first>::Body<'second>" =
  \<open> ('first, 'second) result \<close>

urust_datatype \<open>
  struct SignaturePacket {
    count: SignatureCount,
    flag: signature::Flag,
  }
\<close>

urust_datatype signature_choice_hol \<open>
  enum SignatureChoice {
    Empty,
    Payload(SignatureCount),
  }
\<close>

datatype signature_unregistered_hol = Signature_Unregistered_HOL

section\<open> Authoritative parameter and result types \<close>

urust_fn signature_primitive \<open>
  fn SignaturePrimitive(value: u8) -> u8 { value }
\<close>

urust_fn signature_custom \<open>
  fn SignatureCustom(value: SignatureCount) -> SignatureCount { value }
\<close>

urust_fn signature_qualified \<open>
  fn SignatureQualified(value: signature::Flag) -> signature::Flag { value }
\<close>

urust_fn signature_generic \<open>
  fn SignatureGeneric(
    value: SignatureResult<SignatureOption<u8>, signature::Flag>,
  ) -> SignatureResult<SignatureOption<u8>, signature::Flag> { value }
\<close>

urust_fn signature_segmented \<open>
  fn SignatureSegmented(
    value: signature::Header<u16>::Body<SignatureOption<bool>>,
  ) -> signature::Header<u16>::Body<SignatureOption<bool>> { value }
\<close>

urust_fn signature_generated_struct \<open>
  fn SignatureGeneratedStruct(value: SignaturePacket) -> SignaturePacket { value }
\<close>

urust_fn signature_generated_enum \<open>
  fn SignatureGeneratedEnum(value: SignatureChoice) -> SignatureChoice { value }
\<close>

urust_fn signature_grouped \<open>
  fn SignatureGrouped(value: (u8)) -> (u8) { value }
\<close>

urust_fn signature_tuple \<open>
  fn SignatureTuple(
    value: (u8, (bool, SignatureCount), SignatureOption<u16>),
  ) -> (u8, (bool, SignatureCount), SignatureOption<u16>) { value }
\<close>

urust_fn signature_constructed_tuple \<open>
  fn SignatureConstructedTuple(value: u8, flag: bool) -> (u8, bool) {
    (value, flag)
  }
\<close>

urust_fn signature_hol_escape \<open>
  fn SignatureHOLEscape(
    value: \<tau>\<open>nat option\<close>,
  ) -> \<tau>\<open>nat option\<close> { value }
\<close>

urust_fn signature_shared_variables \<open>
  fn SignatureSharedVariables(
    left: \<tau>\<open>'a\<close>,
    right: \<tau>\<open>'a\<close>,
  ) -> \<tau>\<open>'a\<close> { left }
\<close>

urust_fn signature_plain_identity \<open>
  fn SignaturePlainIdentity(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> {
    value
  }
\<close>

urust_fn signature_identity_two_instantiations \<open>
  fn SignatureIdentityTwoInstantiations(value: u8, flag: bool) -> (u8, bool) {
    (SignaturePlainIdentity(value), SignaturePlainIdentity(flag))
  }
\<close>

urust_fn signature_shared_sorts \<open>
  fn SignatureSharedSorts(
    values: SignatureOrdered<\<tau>\<open>'a\<close>>,
    value: \<tau>\<open>'a\<close>,
  ) -> SignatureOrdered<\<tau>\<open>'a::linorder\<close>> { values }
\<close>

urust_fn signature_higher_order \<open>
  fn SignatureHigherOrder(
    operation: \<tau>\<open>'a \<Rightarrow> 'b\<close>,
    value: \<tau>\<open>'a\<close>,
  ) -> \<tau>\<open>'b\<close> { \<llangle>operation value\<rrangle> }
\<close>

urust_fn signature_function_result \<open>
  fn SignatureFunctionResult(
    operation: SignatureFunction,
  ) -> SignatureFunction { operation }
\<close>

urust_fn signature_holes \<open>
  fn SignatureHoles(
    value: \<tau>\<open>_\<close>,
    flag: \<tau>\<open>_\<close>,
  ) -> (u8, bool) { (value, flag) }
\<close>

urust_fn signature_nested_hole \<open>
  fn SignatureNestedHole(
    value: SignatureOption<\<tau>\<open>_\<close>>,
  ) -> SignatureOption<u16> { value }
\<close>

urust_fn signature_result_hole \<open>
  fn SignatureResultHole(value: u32) -> \<tau>\<open>_\<close> { value }
\<close>

urust_fn signature_omitted_return \<open>
  fn SignatureOmittedReturn(value: u8) {}
\<close>

urust_fn signature_inferred_result \<open>
  fn SignatureInferredResult(value: u64) { value }
\<close>

urust_fn signature_inferred_polymorphic_result \<open>
  fn SignatureInferredPolymorphicResult(value: \<tau>\<open>'a\<close>) { value }
\<close>

urust_fn signature_explicit_unit \<open>
  fn SignatureExplicitUnit() -> () { () }
\<close>

urust_fn signature_inferred_state \<open>
  fn SignatureInferredState() -> SignatureCount {
    \<epsilon>\<open>get (\<lambda>state::nat. state)\<close>
  }
\<close>

urust_fn signature_inferred_write \<open>
  fn SignatureInferredWrite() {
    \<epsilon>\<open>put (\<lambda>state::nat. Suc state)\<close>
  }
\<close>

urust_fn signature_inferred_abort \<open>
  fn SignatureInferredAbort() -> bool {
    \<epsilon>\<open>abort (CustomAbort (0 :: nat))\<close>
  }
\<close>

urust_fn signature_inferred_prompt \<open>
  fn SignatureInferredPrompt(value: u8) -> u8 {
    \<y>\<i>\<e>\<l>\<d>;
    value
  }
\<close>

urust_fn signature_mixed_slots \<open>
  fn SignatureMixedSlots(first: u8, _: bool, mut retained: u16, _: ()) -> u16 {
    retained
  }
\<close>


chapter\<open> Repeated locale interpretations \<close>

text\<open>
Helpers with registration disabled can be interpreted repeatedly. Enabled registrations
retain their conflict checks, including interpretations that differ only in type;
the companion regression theory exercises those rejected interpretations.
\<close>

locale signature_registration_disabled =
  fixes offset :: nat
begin

urust_fn [register_notation = false] signature_locale_function \<open>
  fn SignatureRepeatedLocale(value: SignatureCount) -> SignatureCount {
    \<llangle>value + offset\<rrangle>
  }
\<close>


end

interpretation signature_disabled_first: signature_registration_disabled 1
  by unfold_locales

interpretation signature_disabled_second: signature_registration_disabled 2
  by unfold_locales

lemma signature_disabled_interpretations:
  \<open>signature_disabled_first.signature_locale_function value =
      FunctionBody (literal (value + 1))\<close>
  \<open>signature_disabled_second.signature_locale_function value =
      FunctionBody (literal (value + 2))\<close>
  by (simp_all only:
      signature_disabled_first.signature_locale_function_def
      signature_disabled_second.signature_locale_function_def)

locale signature_registration_enabled =
  fixes offset :: nat
begin

urust_fn [register_notation] signature_locale_function_enabled \<open>
  fn SignatureRepeatedEnabled(value: SignatureCount) -> SignatureCount {
    \<llangle>value + offset\<rrangle>
  }
\<close>

end

locale signature_type_only_registration =
  fixes witness :: \<open> 'a itself \<close>
begin

urust_fn [register_notation] signature_type_only_function \<open>
  fn SignatureTypeOnlyFunction(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> {
    value
  }
\<close>

end

locale signature_ordered_ambient =
  fixes witness :: \<open> 'a::linorder itself \<close>


end
