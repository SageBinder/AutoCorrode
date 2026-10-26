(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Readable urust_fn examples: declaration syntax, signatures, semantic types, channel
   defaults, receivers and datatype composition. The ML audits are in Parser_Function_ML_Tests. *)

theory Parser_Function_Examples
  imports
    Parser_Test_Fixtures
    Micro_Rust_Std_Lib.StdLib_Logging
    Shallow_Separation_Logic.Separation_Algebra
    Micro_Rust_Std_Lib.StdLib_Contracts
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
begin

section\<open>Logging parser fixture\<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

text\<open>
The dedicated parser reads logging macros directly from the neutral notation
registry supplied by the production standard library.
\<close>

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

urust_fn \<open> fn call_registered_probe(x: u64) -> bool { probe(x) } \<close>

urust_fn
  \<open>
    fn HTTP2XMLParser() {
      ()
    }
  \<close>

urust_fn \<open>
    fn already_snake() {
      ()
    }
  \<close>

section\<open> Authoritative signatures and parameter forms \<close>

urust_fn \<open>
    fn AuthoritativeSignature(x: u64) -> u64 {
      x + 1
    }
  \<close>

urust_fn \<open>
    fn MutableParameter(mut x: u64) -> u64 {
      x
    }
  \<close>

urust_fn \<open>
    fn MixedParameterSlots(
      first: \<tau>\<open>nat\<close>,
      _: bool,
      mut retained: \<tau>\<open>nat\<close>,
      _: (),
    ) -> \<tau>\<open>nat\<close> {
      retained
    }
  \<close>

urust_fn \<open>
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

section\<open> Semantic declaration types \<close>

text\<open>
Rust signatures describe parameter and returned values; an omitted return means unit.
Optional HOL channel types retain the computation's state and effects, including
relationships with an unused callback. Named variables and sorts are shared across
the channel options and the signature's HOL escapes.
\<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open> fn SemanticIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>'abort\<close>,
   input = \<open>'i\<close>, output = \<open>'o\<close>] \<open>
    fn SemanticUnusedCallback(
      value: \<tau>\<open>nat\<close>,
      callback: \<tau>\<open>nat \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>,
    ) -> \<tau>\<open>nat\<close> {
      value
    }
  \<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
    fn SemanticCallbackClient(
      value: \<tau>\<open>nat\<close>,
      callback: \<tau>\<open>nat \<Rightarrow> ('s, unit, bool, nat prompt, unit prompt_output) function_body\<close>,
    ) -> \<tau>\<open>nat\<close> {
      SemanticUnusedCallback(value, callback)
    }
  \<close>

urust_notation (call) semantic_unused_callback ("semantic_unused")

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
    fn SemanticCallbackMethodClient(
      value: \<tau>\<open>nat\<close>,
      callback: \<tau>\<open>nat \<Rightarrow> ('s, unit, bool, nat prompt, unit prompt_output) function_body\<close>,
    ) -> \<tau>\<open>nat\<close> {
      value.semantic_unused(callback)
    }
  \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open> fn SemanticFixedCaller(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { SemanticIdentity(value) } \<close>

urust_fn \<open> fn SemanticPolymorphicIdentity(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { value } \<close>

text\<open>
The scoped attributes \<open>urust_state\<close>, \<open>urust_abort\<close>, \<open>urust_input\<close> and \<open>urust_output\<close>
set the default of each channel for later functions in the same context. An inline option
overrides its channel, and an exact \<open>_\<close> leaves it unconstrained.
\<close>

context
  notes [[urust_state = \<open>'s::cancellative_sepalg\<close>, urust_abort = \<open>bool\<close>,
          urust_input = \<open>nat prompt\<close>, urust_output = \<open>unit prompt_output\<close>]]
begin

urust_fn \<open> fn ScopedIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn [abort = \<open>unit\<close>] \<open> fn ScopedUnitAbortIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn [state = \<open>_\<close>] \<open> fn ScopedAnyStateIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

end

section\<open> Declared HOL types \<close>

text\<open>
An optional \<open>:: TYPE\<close> after the HOL name declares the complete curried HOL type, exactly as
for \<open>urust_expr\<close>. The Rust parameter and return types are then ignored: they are neither
resolved nor checked, so here \<open>u64\<close> stands for \<open>nat\<close>, and types without a mapping, shared
references and slices are accepted. The declared type also fixes every channel.
\<close>

urust_fn declared_identity
  :: \<open>nat \<Rightarrow> ('s::cancellative_sepalg, nat, bool, nat prompt, unit prompt_output) function_body\<close>
  \<open> fn DeclaredIdentity(value: u64) -> u64 { value } \<close>

urust_fn :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close> \<open>
    fn DeclaredUnsupportedTypes(value: &Unregistered, rest: &[u8]) -> Unregistered {
      value
    }
  \<close>

text\<open>
An omitted Rust return no longer means unit, and an exact terminal \<open>_\<close> infers every channel.
Calls to a declared function resolve like any other registered function.
\<close>

urust_fn :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  \<open> fn DeclaredOmittedReturn(value: u64) { value } \<close>

urust_fn :: \<open>nat \<Rightarrow> _\<close> \<open> fn DeclaredInferredChannels(value: u64) -> u64 { value } \<close>

urust_fn \<open> fn DeclaredCaller(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { DeclaredInferredChannels(value) } \<close>

section\<open> Abbreviations and application definitions \<close>

urust_fn [abbrev] abbreviated_hol_name
  \<open>
    fn AbbreviatedRustName(x: u64) -> u64 {
      x
    }
  \<close>

urust_fn \<open> fn call_abbreviated_rust_name(x: u64) -> u64 { AbbreviatedRustName(x) } \<close>

urust_fn [application_def, attrs = [micro_rust_simps]]
  attributed_application_function
  \<open>
    fn AttributedApplication(x: u64) -> u64 {
      x
    }
  \<close>

section\<open> Registered calls and argument boundaries \<close>

urust_fn \<open>
    fn RustMaximumCallArity(
      p01: \<tau>\<open>nat\<close>, p02: \<tau>\<open>nat\<close>, p03: \<tau>\<open>nat\<close>, p04: \<tau>\<open>nat\<close>,
      p05: \<tau>\<open>nat\<close>, p06: \<tau>\<open>nat\<close>, p07: \<tau>\<open>nat\<close>, p08: \<tau>\<open>nat\<close>,
      p09: \<tau>\<open>nat\<close>, p10: \<tau>\<open>nat\<close>, p11: \<tau>\<open>nat\<close>, p12: \<tau>\<open>nat\<close>,
      p13: \<tau>\<open>nat\<close>, p14: \<tau>\<open>nat\<close>,
    ) -> \<tau>\<open>nat\<close> {
      p14
    }
  \<close>

urust_fn \<open>
    fn InvokeRustMaximumCallArity() -> \<tau>\<open>nat\<close> {
      RustMaximumCallArity(
        1, 2, 3, 4, 5, 6, 7,
        8, 9, 10, 11, 12, 13, 14,
      )
    }
  \<close>

urust_fn
  [pp_test, pretty, verbosity = 2] \<open>
    fn ConfiguredFunction(x: u64) -> u64 {
      x
    }
  \<close>

urust_fn \<open>
    fn CompletedResultType(x: u64,) -> u64 {
      x
    }
  \<close>

urust_fn omitted_rust_return_type
  \<open>
    fn InferredReturn(x: u64) -> u64 {
      x
    }
  \<close>

section\<open> Lexical parameters and Rust callable names \<close>

urust_fn \<open>
    fn LexicalFunctionShadow(RustAlias: \<tau>\<open>(64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body)\<close>, x: u64) -> u64 {
      RustAlias(x)
    }
  \<close>

urust_fn \<open> fn call_registered_function(x: u64) -> u64 { RustAlias(x, true) } \<close>

urust_fn _
  \<open>
    fn RustAlias(x: u64, _: bool) -> u64 {
      x
    }
  \<close>

urust_fn \<open> fn call_inferred_function() -> () { HTTPServer() } \<close>

section\<open> Locale scope \<close>

locale rust_function_item_locale =
  fixes offset :: nat
begin

urust_fn \<open>
    fn LocaleScopedFunction(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>value + offset\<rrangle>
    }
  \<close>

urust_fn \<open>
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

urust_fn [register_notation] \<open>
  fn BareRegistered(value: u32) -> u32 { value }
\<close>

urust_fn [register_notation = true] \<open>
  fn ExplicitlyRegistered(value: u32) -> u32 { BareRegistered(value) }
\<close>

urust_fn [register_notation = false] \<open>
  fn UnregisteredHelper(value: u32) -> u32 { value }
\<close>

context notes [[urust_register_notation = false]]
begin

urust_fn \<open>
  fn ScopedUnregisteredHelper(value: u32) -> u32 { value }
\<close>

urust_fn [register_notation] \<open>
  fn ScopedRegisteredOverride(value: u32) -> u32 { ExplicitlyRegistered(value) }
\<close>

end

chapter\<open> Function bodies and lexical binding \<close>

section\<open> Function bodies \<close>

urust_fn \<open> fn answer() -> u32 { \<llangle>42 :: 32 word\<rrangle> } \<close>

urust_fn \<open> fn inc(x: u32) -> u32 { x + \<llangle>1 :: 32 word\<rrangle> } \<close>

urust_fn \<open> fn add3(a: u32, b: u32, c: u32) -> u32 { a + b + c } \<close>

urust_fn \<open> fn is_zero(x: u32) -> bool { x == \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_fn \<open>
    fn safe_div(a: u32, b: u32) -> \<tau>\<open>(32 word, unit) result\<close> {
      if b == \<llangle>0 :: 32 word\<rrangle> { Err(()) } else { Ok(a / b) }
    }
  \<close>

urust_fn \<open> fn discard(x: u32) -> () { () } \<close>

urust_fn \<open>
    fn test() -> () {
      let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return;
    }
  \<close>
hide_const test

section\<open> Signature surface \<close>

urust_fn \<open>
    fn fun_heterogeneous(number: \<tau>\<open>nat\<close>, flag: bool, word: u32) -> \<tau>\<open>nat * bool * 32 word\<close> {
      \<llangle>(number, flag, word)\<rrangle>
    }
  \<close>

urust_fn \<open> fn fun_polymorphic(item: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { item } \<close>

urust_fn \<open>
    fn fun_sort_constrained(item: \<tau>\<open>'a::len word\<close>) -> \<tau>\<open>'a word\<close> {
      item
    }
  \<close>

urust_fn \<open> fn fun_type_placeholders(item: \<tau>\<open>_\<close>) -> \<tau>\<open>_\<close> { item } \<close>

urust_fn \<open>
    fn fun_higher_order(f: \<tau>\<open>(nat \<Rightarrow> nat)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>f item\<rrangle>
    }
  \<close>

urust_fn \<open>
    fn fun_nested_result() -> \<tau>\<open>(nat option, (bool, unit) result) result\<close> {
      Ok(Some(\<llangle>1 :: nat\<rrangle>))
    }
  \<close>

urust_fn \<open>
    fn fun_generalized_effects(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

section\<open> Argument-list boundaries \<close>

urust_fn \<open> fn fun_zero_arguments() -> () { () } \<close>

urust_fn \<open>
    fn fun_one_argument(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn \<open>
    fn fun_trailing_comma(item: \<tau>\<open>nat\<close>, flag: bool,) -> \<tau>\<open>nat * bool\<close> {
      \<llangle>(item, flag)\<rrangle>
    }
  \<close>

urust_fn \<open>
    fn fun_multiline_arguments(
      number: \<tau>\<open>nat\<close>,
      flag: bool,
      word: u32,
    ) -> u32 {
      if flag { word } else { \<llangle>of_nat number\<rrangle> }
    }
  \<close>

urust_fn \<open>
  fn fun_sixteen_arguments(p01: \<tau>\<open>nat\<close>, p02: \<tau>\<open>nat\<close>, p03: \<tau>\<open>nat\<close>, p04: \<tau>\<open>nat\<close>, p05: \<tau>\<open>nat\<close>, p06: \<tau>\<open>nat\<close>, p07: \<tau>\<open>nat\<close>, p08: \<tau>\<open>nat\<close>, p09: \<tau>\<open>nat\<close>, p10: \<tau>\<open>nat\<close>, p11: \<tau>\<open>nat\<close>, p12: \<tau>\<open>nat\<close>, p13: \<tau>\<open>nat\<close>, p14: \<tau>\<open>nat\<close>, p15: \<tau>\<open>nat\<close>, p16: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    \<llangle>
      p01 + p02 + p03 + p04 + p05 + p06 + p07 + p08 +
      p09 + p10 + p11 + p12 + p13 + p14 + p15 + p16
    \<rrangle>
  }
  \<close>

section\<open> Ambient binding and scope \<close>

urust_fn \<open>
    fn fun_plain_parameter(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn \<open>
    fn fun_prime_parameter(item': \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item'
    }
  \<close>

urust_fn \<open>
    fn fun_value_antiquotation(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>item + 1\<rrangle>
    }
  \<close>

urust_fn \<open>
    fn fun_expression_antiquotation(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<epsilon>\<open>literal (item + 1)\<close>
    }
  \<close>

urust_fn \<open>
    fn fun_parameter_call(callee: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      callee(item)
    }
  \<close>

urust_fn \<open>
  fn fun_parameter_in_match_guard(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    match Some(item) {
      Some(inner) if inner == item \<Rightarrow> inner,
      _ \<Rightarrow> item
    }
  }
  \<close>

urust_fn \<open>
  fn fun_parameter_in_loop(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) {
      let observed = item;
      ()
    }
    item
  }
  \<close>

urust_fn \<open>
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

urust_fn \<open>
    fn fun_parameter_in_struct(item: \<tau>\<open>nat\<close>, flag: bool) -> \<tau>\<open>fun_struct_fixture\<close> {
      FunStructFixture { item: item, flag: flag }
    }
  \<close>

urust_fn \<open>
    fn fun_nested_let_shadow(item: \<tau>\<open>nat\<close>) -> bool {
      let item = true; item
    }
  \<close>

urust_fn \<open>
  fn fun_nested_pattern_shadow(item: \<tau>\<open>nat\<close>) -> bool {
    let (item, retained) = (true, \<llangle>item\<rrangle>);
    item
  }
  \<close>

urust_fn \<open>
    fn fun_closure_shadow(item: bool) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> {
      |item| \<llangle>item :: nat\<rrangle>
    }
  \<close>

context
  fixes item :: bool
begin

urust_fn \<open>
    fn fun_parameter_shadows_context(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>item :: nat\<rrangle>
    }
  \<close>

end

urust_fn \<open>
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

urust_fn \<open>
    fn fun_parameter_call_wins(funCollision: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      funCollision(item)
    }
  \<close>

urust_fn \<open>
    fn fun_registered_field_wins(item: \<tau>\<open>fun_field_record\<close>, funFieldCollision: \<tau>\<open>(fun_field_record, nat) lens\<close>) -> \<tau>\<open>nat\<close> {
      item.funFieldCollision
    }
  \<close>

section\<open> Isabelle declaration integration \<close>

context
begin

qualified urust_fn \<open>
    fn qualified_identity(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

end

locale fun_command_locale =
  fixes offset :: nat
begin

urust_fn \<open>
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

urust_fn \<open>
    fn iterator_zip_direct(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> {
      zip(left, right)
    }
  \<close>

urust_fn \<open>
    fn iterator_zip_method(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> {
      left.zip(right)
    }
  \<close>

urust_fn \<open>
    fn iterator_zip_chained(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> {
      left.into_iter().zip(right.into_iter())
    }
  \<close>

chapter\<open> Declaration options and parameter slots \<close>

section\<open> Application equations and attributes \<close>

urust_fn [application_def] \<open>
    fn typed_application_function(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn \<open>
    fn typed_zero_function_default() -> \<tau>\<open>nat\<close> {
      \<llangle>7 :: nat\<rrangle>
    }
  \<close>

urust_fn [application_def] \<open>
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

urust_fn [attrs = []] \<open>
    fn partial_collision_function(command_parameter_collision: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      command_parameter_collision
    }
  \<close>

urust_fn [attrs = [micro_rust_simps]] \<open>
    fn partial_internal_placeholder(item: \<tau>\<open>_\<close>) -> \<tau>\<open>_\<close> {
      \<llangle>item :: nat\<rrangle>
    }
  \<close>

urust_fn \<open> fn zip_parameter_value(zip: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { zip } \<close>

urust_fn \<open>
    fn zip_callable_parameter(zip: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      zip(item)
    }
  \<close>

urust_fn \<open>
    fn zip_method_registration(zip: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item.zip()
    }
  \<close>

urust_fn \<open> fn quoted_major_parameter(lemma: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { lemma } \<close>

section\<open> Wildcard parameter slots \<close>

urust_fn \<open> fn wildcard_function_single(_: \<tau>\<open>nat\<close>) -> () { () } \<close>

urust_fn \<open>
    fn wildcard_function_mixed(_: \<tau>\<open>nat\<close>, kept: bool, _: u32) -> bool {
      kept
    }
  \<close>

urust_fn \<open>
    fn wildcard_function_inferred(_: \<tau>\<open>_\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>0 :: nat\<rrangle>
    }
  \<close>

urust_fn [application_def] \<open> fn wildcard_function_application(_: \<tau>\<open>nat\<close>) -> () { () } \<close>

urust_fn [abbrev] \<open>
    fn wildcard_function_abbreviation(_: \<tau>\<open>nat\<close>, kept: bool) -> bool {
      kept
    }
  \<close>

text\<open>
Application definitions put source-spelled parameters on the left-hand side. A Rust parameter that
is not an Isabelle identifier is desymbolized; \<open>Parser_Syntax_ML_Tests\<close> audits the
resulting names.
\<close>

urust_fn [application_def] \<open> fn underscore_function_application(_unused: u64, kept: u64) -> u64 { kept } \<close>

section\<open> Anonymous checks and abbreviations \<close>

urust_fn [application_def] _
  \<open>
    fn AnonymousFunction(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn [abbrev, verbosity = 2] \<open>
    fn typed_function_abbrev_command(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

section\<open> Pretty-printer options \<close>

urust_fn [pp_test = false] \<open>
    fn pp_fun_disabled(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      item
    }
  \<close>

urust_fn [pp_test] \<open> fn pp_fun_enabled(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>

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

urust_fn \<open>
  fn SignaturePrimitive(value: u8) -> u8 { value }
\<close>

urust_fn \<open>
  fn SignatureCustom(value: SignatureCount) -> SignatureCount { value }
\<close>

urust_fn \<open>
  fn SignatureQualified(value: signature::Flag) -> signature::Flag { value }
\<close>

urust_fn \<open>
  fn SignatureGeneric(
    value: SignatureResult<SignatureOption<u8>, signature::Flag>,
  ) -> SignatureResult<SignatureOption<u8>, signature::Flag> { value }
\<close>

urust_fn \<open>
  fn SignatureSegmented(
    value: signature::Header<u16>::Body<SignatureOption<bool>>,
  ) -> signature::Header<u16>::Body<SignatureOption<bool>> { value }
\<close>

urust_fn \<open>
  fn SignatureGeneratedStruct(value: SignaturePacket) -> SignaturePacket { value }
\<close>

urust_fn \<open>
  fn SignatureGeneratedEnum(value: SignatureChoice) -> SignatureChoice { value }
\<close>

urust_fn \<open>
  fn SignatureGrouped(value: (u8)) -> (u8) { value }
\<close>

urust_fn \<open>
  fn SignatureTuple(
    value: (u8, (bool, SignatureCount), SignatureOption<u16>),
  ) -> (u8, (bool, SignatureCount), SignatureOption<u16>) { value }
\<close>

urust_fn \<open>
  fn SignatureConstructedTuple(value: u8, flag: bool) -> (u8, bool) {
    (value, flag)
  }
\<close>

urust_fn \<open>
  fn SignatureHOLEscape(
    value: \<tau>\<open>nat option\<close>,
  ) -> \<tau>\<open>nat option\<close> { value }
\<close>

urust_fn \<open>
  fn SignatureSharedVariables(
    left: \<tau>\<open>'a\<close>,
    right: \<tau>\<open>'a\<close>,
  ) -> \<tau>\<open>'a\<close> { left }
\<close>

urust_fn \<open>
  fn SignaturePlainIdentity(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> {
    value
  }
\<close>

urust_fn \<open>
  fn SignatureIdentityTwoInstantiations(value: u8, flag: bool) -> (u8, bool) {
    (SignaturePlainIdentity(value), SignaturePlainIdentity(flag))
  }
\<close>

urust_fn \<open>
  fn SignatureSharedSorts(
    values: SignatureOrdered<\<tau>\<open>'a\<close>>,
    value: \<tau>\<open>'a\<close>,
  ) -> SignatureOrdered<\<tau>\<open>'a::linorder\<close>> { values }
\<close>

urust_fn \<open>
  fn SignatureHigherOrder(
    operation: \<tau>\<open>'a \<Rightarrow> 'b\<close>,
    value: \<tau>\<open>'a\<close>,
  ) -> \<tau>\<open>'b\<close> { \<llangle>operation value\<rrangle> }
\<close>

urust_fn \<open>
  fn SignatureFunctionResult(
    operation: SignatureFunction,
  ) -> SignatureFunction { operation }
\<close>

urust_fn \<open>
  fn SignatureHoles(
    value: \<tau>\<open>_\<close>,
    flag: \<tau>\<open>_\<close>,
  ) -> (u8, bool) { (value, flag) }
\<close>

urust_fn \<open>
  fn SignatureNestedHole(
    value: SignatureOption<\<tau>\<open>_\<close>>,
  ) -> SignatureOption<u16> { value }
\<close>

urust_fn \<open>
  fn SignatureResultHole(value: u32) -> \<tau>\<open>_\<close> { value }
\<close>

urust_fn \<open>
  fn SignatureOmittedReturn(value: u8) {}
\<close>

urust_fn \<open>
  fn SignatureInferredResult(value: u64) -> u64 { value }
\<close>

urust_fn \<open>
  fn SignatureInferredPolymorphicResult(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { value }
\<close>

urust_fn \<open>
  fn SignatureExplicitUnit() -> () { () }
\<close>

urust_fn \<open>
  fn SignatureInferredState() -> SignatureCount {
    \<epsilon>\<open>get (\<lambda>state::nat. state)\<close>
  }
\<close>

urust_fn \<open>
  fn SignatureInferredWrite() {
    \<epsilon>\<open>put (\<lambda>state::nat. Suc state)\<close>
  }
\<close>

urust_fn \<open>
  fn SignatureInferredAbort() -> bool {
    \<epsilon>\<open>abort (CustomAbort (0 :: nat))\<close>
  }
\<close>

urust_fn \<open>
  fn SignatureInferredPrompt(value: u8) -> u8 {
    \<y>\<i>\<e>\<l>\<d>;
    value
  }
\<close>

urust_fn \<open>
  fn SignatureMixedSlots(first: u8, _: bool, mut retained: u16, _: ()) -> u16 {
    retained
  }
\<close>

section\<open> Built-in prelude mappings \<close>

text\<open>
\<^verbatim>\<open>Option<T>\<close> and \<^verbatim>\<open>Result<T, E>\<close> are built-in generic mappings. Each mapped
signature is identical to the same function written with HOL type escapes.
\<close>

urust_fn \<open>
  fn SignaturePreludeOption(value: Option<u8>) -> Option<u8> { value }
\<close>

urust_fn \<open>
  fn SignaturePreludeOptionEscaped(value: \<tau>\<open>8 word option\<close>) -> \<tau>\<open>8 word option\<close> {
    value
  }
\<close>

lemma signature_prelude_option_same:
  \<open> signature_prelude_option = signature_prelude_option_escaped \<close>
  unfolding signature_prelude_option_def signature_prelude_option_escaped_def
  by (rule refl)

urust_fn \<open>
  fn SignaturePreludeResult(value: Result<u32, bool>) -> Result<u32, bool> { value }
\<close>

urust_fn \<open>
  fn SignaturePreludeResultEscaped(value: \<tau>\<open>(32 word, bool) result\<close>)
    -> \<tau>\<open>(32 word, bool) result\<close> { value }
\<close>

lemma signature_prelude_result_same:
  \<open> signature_prelude_result = signature_prelude_result_escaped \<close>
  unfolding signature_prelude_result_def signature_prelude_result_escaped_def
  by (rule refl)

urust_fn \<open>
  fn SignaturePreludeNested(
    value: Option<Result<(Option<u16>, ()), SignatureCount>>,
  ) -> Option<Result<(Option<u16>, ()), SignatureCount>> { value }
\<close>

urust_fn \<open>
  fn SignaturePreludeNestedEscaped(
    value: \<tau>\<open>((16 word option \<times> unit \<times> tnil), nat) result option\<close>,
  ) -> \<tau>\<open>((16 word option \<times> unit \<times> tnil), nat) result option\<close> { value }
\<close>

lemma signature_prelude_nested_same:
  \<open> signature_prelude_nested = signature_prelude_nested_escaped \<close>
  unfolding signature_prelude_nested_def signature_prelude_nested_escaped_def
  by (rule refl)

urust_fn \<open>
  fn SignaturePreludeGeneric(value: Result<\<tau>\<open>'a\<close>, \<tau>\<open>'e\<close>>) -> Option<\<tau>\<open>'a\<close>> {
    match value {
      Ok(ok) => Some(ok),
      Err(_) => None,
    }
  }
\<close>

urust_fn \<open>
  fn SignaturePreludeGenericEscaped(value: \<tau>\<open>('a, 'e) result\<close>) -> \<tau>\<open>'a option\<close> {
    match value {
      Ok(ok) => Some(ok),
      Err(_) => None,
    }
  }
\<close>

lemma signature_prelude_generic_same:
  \<open> signature_prelude_generic = signature_prelude_generic_escaped \<close>
  unfolding signature_prelude_generic_def signature_prelude_generic_escaped_def
  by (rule refl)

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

urust_fn [register_notation] \<open>
  fn SignatureTypeOnlyFunction(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> {
    value
  }
\<close>

end

locale signature_ordered_ambient =
  fixes witness :: \<open> 'a::linorder itself \<close>

section\<open> Delivery-line declaration compatibility \<close>

urust_fn [application_def] _
  \<open> fn AnonymousFunction(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>

urust_fn \<open> fn fun_explicit_prompt_output(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>

chapter\<open> Function items, artifacts and parser recovery \<close>

section\<open> Generated equations and declaration artifacts \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

lemma explicit_hol_name_shape:
  \<open>explicit_hol_name =
    (\<lambda>x _. FunctionBody (literal x))\<close>
  by (simp add: explicit_hol_name_def)

lemma inferred_hol_name_shape:
  \<open>http_server = FunctionBody (literal ())\<close>
  by (simp add: http_server_def)

lemma mixed_parameter_slots_shape:
  \<open>mixed_parameter_slots =
    (\<lambda>_ _ retained _. FunctionBody (literal retained))\<close>
  by (simp add: mixed_parameter_slots_def)

lemma empty_block_shape:
  \<open>empty_block = FunctionBody (literal ())\<close>
  by (simp add: empty_block_def)

lemma commented_signature_shape:
  \<open>commented_signature =
    (\<lambda>value. FunctionBody (literal value))\<close>
  by (simp add: commented_signature_def)

thm authoritative_signature_def

thm attributed_application_function_def

thm configured_function_def

thm http2_xml_parser_def

thm already_snake_def

section\<open> AST structure and signature printer roundtrips \<close>

urust_datatype shared_item \<open> struct SharedItem; \<close>

definition notation_function_target ::
    \<open>64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where
    \<open>notation_function_target =
      (\<lambda>x. FunctionBody (literal x))\<close>

urust_notation (call)
  notation_function_target ("NotationClash")

chapter\<open> Iterator semantic regressions \<close>

lemma iterator_zip_empty:
  shows \<open>iterator_zip zip_left_empty zip_right_two =
    fun_literal (make_iterator [])\<close>
  by (simp add: iterator_zip_def zip_left_empty_def zip_right_two_def)

lemma iterator_zip_empty_right:
  shows \<open>iterator_zip zip_left_two
    (make_iterator [] :: zip_right_iterator) =
    fun_literal (make_iterator [])\<close>
  by (simp add: iterator_zip_def zip_left_two_def)

lemma iterator_zip_equal_length:
  shows \<open>iterator_zip zip_left_two zip_right_two =
    fun_literal (make_iterator
      [iterator_zip_thunk (fun_literal 1) (fun_literal True),
       iterator_zip_thunk (fun_literal 2) (fun_literal False)])\<close>
  by (simp add: iterator_zip_def zip_left_two_def zip_right_two_def)

lemma iterator_zip_truncates_to_shorter:
  shows \<open>iterator_zip zip_left_two zip_right_one =
    fun_literal (make_iterator
      [iterator_zip_thunk (fun_literal 1) (fun_literal True)])\<close>
  by (simp add: iterator_zip_def zip_left_two_def zip_right_one_def)

lemma iterator_zip_truncates_when_left_is_shorter:
  shows \<open>iterator_zip zip_left_one zip_right_two =
    fun_literal (make_iterator
      [iterator_zip_thunk (fun_literal 1) (fun_literal True)])\<close>
  by (simp add: iterator_zip_def zip_left_one_def zip_right_two_def)

lemma iterator_zip_effect_order_and_single_evaluation:
  shows \<open>evaluate
    (call (iterator_zip_thunk
      (zip_effect_thunk 1 (10 :: nat))
      (zip_effect_thunk 2 True))) [] =
    Success (10, True, TNil) [1, 2]\<close>
  by (simp add: iterator_zip_thunk_def zip_effect_thunk_def call_def
      evaluate_call_function_body bind_evaluate put_def literal_def
      Core_Expression.bind.simps Core_Expression.call_function_body.simps
      evaluate_def)

lemma hol_list_zip_is_unchanged:
  shows \<open>List.zip [1 :: nat, 2] [True] = [(1, True)]\<close>
  by simp

chapter\<open> Signature inference and registration regressions \<close>

section\<open> Types, effect channels and wrapper shape \<close>

lemma signature_custom_shape:
  \<open> signature_custom = (\<lambda>value. FunctionBody (literal value)) \<close>
  by (simp only: signature_custom_def)

lemma signature_mixed_slots_shape:
  \<open> signature_mixed_slots = (\<lambda>_ _ retained _. FunctionBody (literal retained)) \<close>
  by (simp only: signature_mixed_slots_def)

section\<open> Occupied paths, atomic rejection, and recovery \<close>

definition signature_existing_call ::
  \<open> 8 word \<Rightarrow> ('s, 8 word, 'abort, 'i, 'o) function_body \<close>
  where \<open> signature_existing_call value = FunctionBody (literal value) \<close>

urust_notation (call) signature_existing_call ("SignatureExistingCall")

chapter\<open> Semantic function types \<close>

section\<open> Full declaration types and kernel equalities \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

lemma semantic_identity_former_instance:
  \<open>semantic_identity = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding semantic_identity_def by (rule refl)

lemma semantic_callback_client_equivalent:
  \<open>semantic_callback_client = semantic_callback_method_client\<close>
  unfolding semantic_callback_client_def semantic_callback_method_client_def by (rule refl)

lemma semantic_fixed_caller_folding:
  \<open>function_body (semantic_fixed_caller value) =
    (funcall1 semantic_identity (literal value) ::
      (unit, nat, nat, bool, nat prompt, unit prompt_output) expression)\<close>
  unfolding semantic_fixed_caller_def by simp

lemma semantic_local_expression_folding:
  fixes x :: nat
  defines D_def: \<open>D \<equiv> (funcall1 semantic_identity (literal x) ::
    (unit, nat, nat, bool, nat prompt, unit prompt_output) expression)\<close>
  shows \<open>function_body (semantic_fixed_caller x) = D\<close>
  unfolding semantic_fixed_caller_def
  by (simp only: function_body_simp D_def[symmetric])

lemma semantic_identity_contract:
  fixes \<Gamma> :: \<open>('s::cancellative_sepalg, bool, nat, unit) striple_context\<close>
  shows \<open>\<Gamma>; semantic_identity value \<Turnstile>\<^sub>F lift_pure_to_contract value\<close>
  by (crush_boot f: semantic_identity_def contract: lift_pure_to_contract_def; crush_base)

lemma semantic_fixed_caller_contract:
  fixes \<Gamma> :: \<open>(unit, bool, nat, unit) striple_context\<close>
  shows \<open>\<Gamma>; semantic_fixed_caller value \<Turnstile>\<^sub>F lift_pure_to_contract value\<close>
  apply (crush_boot f: semantic_fixed_caller_def contract: lift_pure_to_contract_def)
  by (crush_base specs add: semantic_identity_contract contracts add: lift_pure_to_contract_def)

lemma semantic_polymorphic_identity_contract:
  fixes \<Gamma> :: \<open>('s::sepalg, 'abort, 'i, 'o) striple_context\<close>
  shows \<open>\<Gamma>; semantic_polymorphic_identity value \<Turnstile>\<^sub>F lift_pure_to_contract value\<close>
  by (crush_boot f: semantic_polymorphic_identity_def contract: lift_pure_to_contract_def; crush_base)

section\<open> Holes, shared names and independent call instances \<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>'value::linorder\<close>,
   input = \<open>'channel\<close>, output = \<open>'channel\<close>] \<open>
    fn SemanticChannelSharing(value: \<tau>\<open>'value\<close>) -> \<tau>\<open>'value\<close> { value }
  \<close>

urust_fn
  [state = \<open>_::cancellative_sepalg\<close>, abort = \<open>_::linorder\<close>,
   input = \<open>_::finite\<close>, output = \<open>_::order\<close>] \<open> fn SemanticSortedHoles(left: \<tau>\<open>_\<close>, right: \<tau>\<open>_\<close>) {} \<close>

type_synonym 'v semantic_input_type = \<open>'v prompt\<close>

type_synonym 'v semantic_output_type = \<open>'v prompt_output\<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat semantic_input_type\<close>, output = \<open>unit semantic_output_type\<close>] \<open> fn SemanticSynonymIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open> fn SemanticPointerIdentity(value: *const u8) -> *const u8 { value } \<close>

urust_fn
  [state = \<open>'s::cancellative_sepalg\<close>] \<open> fn SemanticSharedNames(value: \<tau>\<open>'inner\<close>) -> \<tau>\<open>'inner\<close> { value } \<close>

urust_fn
  [state = \<open>_\<close>, abort = \<open>bool\<close>, input = \<open>_\<close>, output = \<open>_\<close>] \<open> fn SemanticIndependentHoles(left: \<tau>\<open>_\<close>, right: \<tau>\<open>_\<close>) -> \<tau>\<open>_\<close> { left } \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>bool\<close>] \<open> fn SemanticSpecializedName(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>bool\<close>] \<open>
    fn SemanticTwoInstances(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      let ignored = SemanticSharedNames(true);
      SemanticSharedNames(value)
    }
  \<close>

urust_fn
  [state = \<open>'s\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open> fn SemanticOmittedResult() -> \<tau>\<open>nat\<close> { 7 } \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>bool\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>] \<open>
    fn SemanticReturnedComputation() -> \<tau>\<open>(unit, nat, bool, unit, unit) function_body\<close> {
      \<llangle>fun_literal (7::nat)\<rrangle>
    }
  \<close>

section\<open> Locale fixes and interpreted contexts \<close>

locale semantic_type_locale =
  fixes seed :: \<open>'s::cancellative_sepalg\<close>
begin

(* Interpreting the locale changes the registered terms or their fixed state type. *)
urust_fn
  [state = \<open>'s\<close>, abort = \<open>bool\<close>,
   input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>,
   register_notation = false] \<open>
    fn SemanticLocaleCallback(
    ) -> () {
      \<llangle>let _ = seed in ()\<rrangle>
    }
  \<close>

urust_fn
  [state = \<open>'s\<close>, abort = \<open>bool\<close>, input = \<open>'i\<close>, output = \<open>'o\<close>,
   register_notation = false] \<open>
    fn SemanticLocaleUnused(callback: \<tau>\<open>'s \<Rightarrow> ('s, unit, bool, 'i, 'o) function_body\<close>) {}
  \<close>

end

interpretation semantic_unit: semantic_type_locale \<open>()\<close> .

lemma semantic_interpreted_channels:
  \<open>function_body semantic_unit.semantic_locale_callback =
    (literal () :: (unit, unit, unit, bool, nat prompt, unit prompt_output) expression)\<close>
  unfolding semantic_unit.semantic_locale_callback_def by simp

section\<open> Every channel combination and default unit results \<close>

urust_fn [abort = \<open>bool\<close>] \<open> fn SemanticDefaultUnit(value: \<tau>\<open>nat\<close>) { () } \<close>

urust_fn [abort = \<open>bool\<close>] \<open> fn SemanticExplicitUnit(value: \<tau>\<open>nat\<close>) -> () { () } \<close>

lemma semantic_default_unit_equivalent:
  \<open>semantic_default_unit = semantic_explicit_unit\<close>
  unfolding semantic_default_unit_def semantic_explicit_unit_def by (rule refl)

chapter\<open> Scoped channel defaults \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

text\<open>
The scoped attributes \<open>urust_state\<close>, \<open>urust_abort\<close>, \<open>urust_input\<close> and \<open>urust_output\<close>
supply the channel types of every later function that omits the corresponding option. An inline
option or \<omega> annotation overrides one channel; an exact \<open>_\<close> removes a default. Each inheriting
function rereads the default with its own signature, exactly as if the option were written inline.
\<close>

section\<open> Inherited and overridden channels \<close>

context
  notes [[urust_state = \<open>'s::cancellative_sepalg\<close>, urust_abort = \<open>bool\<close>,
          urust_input = \<open>nat prompt\<close>, urust_output = \<open>unit prompt_output\<close>]]
begin

urust_fn \<open> fn DefaultIdentity(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn [abort = \<open>unit\<close>] \<open> fn DefaultAbortOverride(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

urust_fn \<open> fn DefaultFixedCaller(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { DefaultIdentity(value) } \<close>

end

urust_fn \<open> fn DefaultOutsideScope(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value } \<close>

lemma default_identity_equivalent:
  \<open>default_identity = semantic_identity\<close>
  unfolding default_identity_def semantic_identity_def by (rule refl)

chapter\<open> Typed receivers \<close>

section\<open> Explicit receiver types and ordinary parameter bindings \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

urust_fn \<open> fn TypedSelfPrimitive(self: u64) -> u64 { self } \<close>

urust_fn \<open> fn TypedSelfValuePrimitive(self_value: u64) -> u64 { self_value } \<close>

urust_fn \<open> fn TypedMutSelf(mut self: u64) -> u64 { self } \<close>

lemma typed_self_primitive_equivalent:
  \<open>typed_self_primitive = typed_self_value_primitive\<close>
  unfolding typed_self_primitive_def typed_self_value_primitive_def by (rule refl)

lemma typed_mut_self_equivalent:
  \<open>typed_mut_self = typed_self_value_primitive\<close>
  unfolding typed_mut_self_def typed_self_value_primitive_def by (rule refl)

type_synonym widget_ref = \<open>(nat, unit, 8 word) Global_Store.ref\<close>

urust_fn \<open> fn TypedSelfHOLRef(self: \<tau>\<open>widget_ref\<close>) -> \<tau>\<open>widget_ref\<close> { self } \<close>

urust_fn \<open> fn TypedSelfValueHOLRef(self_value: \<tau>\<open>widget_ref\<close>) -> \<tau>\<open>widget_ref\<close> { self_value } \<close>

lemma typed_self_hol_ref_equivalent:
  \<open>typed_self_hol_ref = typed_self_value_hol_ref\<close>
  unfolding typed_self_hol_ref_def typed_self_value_hol_ref_def by (rule refl)

urust_type "ReceiverWidget" = \<open> fun_field_record \<close>

urust_fn \<open> fn TypedSelfField(self: ReceiverWidget) -> \<tau>\<open>nat\<close> { self.funFieldCollision } \<close>

urust_fn \<open> fn TypedSelfValueField(self_value: ReceiverWidget) -> \<tau>\<open>nat\<close> { self_value.funFieldCollision } \<close>

lemma typed_self_field_equivalent:
  \<open>typed_self_field = typed_self_value_field\<close>
  unfolding typed_self_field_def typed_self_value_field_def by (rule refl)

section\<open> HOL value and expression escapes \<close>

urust_fn \<open> fn TypedSelfHOLValue(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self + 1\<rrangle> } \<close>

urust_fn \<open> fn TypedSelfValueHOLValue(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self_value + 1\<rrangle> } \<close>

urust_fn \<open> fn TypedSelfHOLExpression(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<epsilon>\<open>literal (self + 1)\<close> } \<close>

urust_fn \<open> fn TypedSelfValueHOLExpression(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<epsilon>\<open>literal (self_value + 1)\<close> } \<close>

lemma typed_self_hol_value_equivalent:
  \<open>typed_self_hol_value = typed_self_value_hol_value\<close>
  unfolding typed_self_hol_value_def typed_self_value_hol_value_def by (rule refl)

lemma typed_self_hol_expression_equivalent:
  \<open>typed_self_hol_expression = typed_self_value_hol_expression\<close>
  unfolding typed_self_hol_expression_def typed_self_value_hol_expression_def by (rule refl)

section\<open> Typed receiver declarations and method dispatch \<close>

urust_fn
  [state = \<open>unit\<close>, abort = \<open>unit\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>]
  typed_self_add
  \<open>
    fn ReceiverAdd(self: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>self + delta\<rrangle>
    }
  \<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>unit\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>]
  typed_self_value_add
  \<open>
    fn ReceiverAddValue(self_value: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>self_value + delta\<rrangle>
    }
  \<close>

urust_notation (call) typed_self_add ("receiver_add")

urust_fn \<open>
    fn TypedSelfMethod(self: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      self.receiver_add(delta)
    }
  \<close>

urust_fn \<open>
    fn TypedSelfValueMethod(self_value: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      self_value.receiver_add(delta)
    }
  \<close>

urust_fn \<open>
    fn TypedSelfDirect(self: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      ReceiverAdd(self, delta)
    }
  \<close>

urust_fn \<open>
    fn TypedSelfFieldMethod(self: ReceiverWidget, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      self.funFieldCollision.receiver_add(delta)
    }
  \<close>

urust_fn \<open>
    fn TypedSelfValueFieldMethod(self_value: ReceiverWidget, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      self_value.funFieldCollision.receiver_add(delta)
    }
  \<close>

lemma typed_self_add_equivalent:
  \<open>typed_self_add = typed_self_value_add\<close>
  unfolding typed_self_add_def typed_self_value_add_def by (rule refl)

lemma typed_self_method_equivalent:
  \<open>typed_self_method = typed_self_value_method\<close>
  unfolding typed_self_method_def typed_self_value_method_def by (rule refl)

lemma typed_self_method_dispatch:
  \<open>typed_self_method = typed_self_direct\<close>
  unfolding typed_self_method_def typed_self_direct_def by (rule refl)

lemma typed_self_field_method_equivalent:
  \<open>typed_self_field_method = typed_self_value_field_method\<close>
  unfolding typed_self_field_method_def typed_self_value_field_method_def by (rule refl)

chapter\<open> Mutable references and erased lifetimes \<close>

section\<open> Mutable references and lifetimes in function signatures \<close>

text\<open>
A Rust mutable reference \<open>&mut T\<close> in a function signature resolves to the same
\<open>Global_Store.ref\<close> model as a raw pointer and shares the signature's address/global backend.
Lifetimes, including \<open>'static\<close> and \<open>'_\<close>, are parsed and checked against the function's
lifetime parameters, then erased: they never change the declared term.
\<close>

urust_fn \<open> fn MutRefIdentity(value: &mut u8) -> &mut u8 { value } \<close>

urust_fn \<open>
  fn MutRefEscapeControl(value: \<tau>\<open>('a, 'b, 8 word) Global_Store.ref\<close>)
      -> \<tau>\<open>('a, 'b, 8 word) Global_Store.ref\<close> {
    value
  }
\<close>

urust_fn \<open> fn LifetimeRefIdentity<'a>(value: &'a mut u8) -> &'a mut u8 { value } \<close>

urust_fn \<open> fn ReservedLifetimeIdentity(value: &'static mut u8) -> &'_ mut u8 { value } \<close>

urust_fn \<open> fn TypedSelfMutRef(self: &mut u8) -> &mut u8 { self } \<close>

urust_fn \<open> fn TypedMutSelfMutRef(mut self: &mut u8) -> &mut u8 { self } \<close>

lemma mut_ref_escape_equivalent:
  \<open>mut_ref_identity = mut_ref_escape_control\<close>
  unfolding mut_ref_identity_def mut_ref_escape_control_def by (rule refl)

lemma lifetime_erasure_equivalent:
  \<open>lifetime_ref_identity = mut_ref_identity\<close>
  unfolding lifetime_ref_identity_def mut_ref_identity_def by (rule refl)

lemma reserved_lifetime_erasure_equivalent:
  \<open>reserved_lifetime_identity = mut_ref_identity\<close>
  unfolding reserved_lifetime_identity_def mut_ref_identity_def by (rule refl)

lemma typed_self_mut_ref_equivalent:
  \<open>typed_self_mut_ref = mut_ref_identity\<close>
  unfolding typed_self_mut_ref_def mut_ref_identity_def by (rule refl)

lemma typed_mut_self_mut_ref_equivalent:
  \<open>typed_mut_self_mut_ref = mut_ref_identity\<close>
  unfolding typed_mut_self_mut_ref_def mut_ref_identity_def by (rule refl)

urust_type "RefOption<'t>" = \<open> 't option \<close>

urust_fn \<open>
  fn MixedReferenceShapes<'a, 'b,>(
    option: RefOption<&'a mut u8>,
    nested: &'b mut &'static mut u16,
    tuple: &mut (u8, bool),
    pointer: *mut u32,
    escape: &mut \<tau>\<open>'x list\<close>,
    element: \<tau>\<open>'x\<close>
  ) -> &'a mut u8 {
    \<llangle>undefined\<rrangle>
  }
\<close>

urust_fn \<open>
  fn ReferenceBodyConstraint(value: &mut u8) -> &mut u8 {
    \<llangle>value :: (nat, bool, 8 word) Global_Store.ref\<rrangle>
  }
\<close>

section\<open> Body and call-site semantics \<close>

text\<open>
Unit-backed store fixtures tie dereferences to the referenced value type, as the showcase does.
Reads through a reference use an explicit \<open>*\<close>, \<open>&mut local\<close> passes a mutable local,
and an existing reference parameter is passed on unchanged.
\<close>

definition reference_test_allocate ::
    \<open>'v \<Rightarrow> (unit, (unit, unit, 'v) Global_Store.ref, unit, unit, unit) function_body\<close>
  where \<open> reference_test_allocate \<equiv> undefined \<close>

definition reference_test_read ::
    \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> (unit, 'v, unit, unit, unit) function_body\<close>
  where \<open> reference_test_read \<equiv> undefined \<close>

definition reference_test_write ::
    \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      (unit, unit, unit, unit, unit) function_body\<close>
  where \<open> reference_test_write \<equiv> undefined \<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> reference_test_read
adhoc_overloading store_reference_const \<rightleftharpoons> reference_test_allocate
adhoc_overloading store_update_const \<rightleftharpoons> reference_test_write

urust_datatype \<open> struct RefCounter { count: u32 } \<close>

urust_fn \<open> fn ReadThrough<'a>(value: &'a mut u32) -> u32 { *value } \<close>

urust_fn \<open>
  fn ReadThroughControl(value: \<tau>\<open>(unit, unit, 32 word) Global_Store.ref\<close>) -> u32 {
    *value
  }
\<close>

urust_fn \<open> fn WriteThrough(value: &mut u32, next: u32) { *value = next; } \<close>

urust_fn \<open> fn IncrementThrough(value: &mut u32) { *value += 1_u32; } \<close>

urust_fn \<open> fn ResetCounter(counter: &mut RefCounter) { counter.count = 0_u32; } \<close>

urust_fn \<open> fn ReadCounter(counter: &mut RefCounter) -> u32 { *counter.count } \<close>

urust_fn \<open>
  fn TouchCounter(self: &mut RefCounter) -> u32 {
    self.count = 1_u32;
    *self.count
  }
\<close>

urust_notation (call) touch_counter ("touch")

urust_fn \<open> fn TouchViaMethod(counter: &mut RefCounter) -> u32 { counter.touch() } \<close>

urust_fn \<open>
  fn BumpLocal() -> u32 {
    let mut local = 0_u32;
    IncrementThrough(&mut local);
    *local
  }
\<close>

urust_fn \<open> fn ForwardReference(value: &mut u32) { IncrementThrough(value) } \<close>

urust \<open>
  fn ChunkIncrement<'a>(value: &'a mut u32) { *value += 1_u32; }

  fn ChunkCaller() -> u32 {
    let mut local = 0_u32;
    ChunkIncrement(&mut local);
    *local
  }
\<close>

lemma read_through_equivalent:
  \<open>read_through = read_through_control\<close>
  unfolding read_through_def read_through_control_def by (rule refl)

lemma chunk_increment_equivalent:
  \<open>chunk_increment = increment_through\<close>
  unfolding chunk_increment_def increment_through_def by (rule refl)

text\<open>
The following accepted forms record current divergences from Rust: assigning to a reference
parameter writes through it, and a mutable local passes as a reference without \<open>&mut\<close>.
\<close>

urust_fn \<open> fn AssignThrough(value: &mut u32, next: u32) { value = next; } \<close>

urust_fn \<open>
  fn BumpWithoutBorrow() -> u32 {
    let mut local = 0_u32;
    IncrementThrough(local);
    *local
  }
\<close>

lemma assign_through_writes_through:
  \<open>assign_through = write_through\<close>
  unfolding assign_through_def write_through_def by (rule refl)

chapter\<open> Datatype composition \<close>

section\<open> Complete const arguments and radix discriminants \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

no_adhoc_overloading store_dereference_const \<rightleftharpoons> reference_test_read
no_adhoc_overloading store_reference_const \<rightleftharpoons> reference_test_allocate
no_adhoc_overloading store_update_const \<rightleftharpoons> reference_test_write

urust_datatype \<open> struct CompositionNumeric<T, P, const N: usize>; \<close>

urust_datatype [word_width = 8] \<open>
  enum CompositionRadix { Binary = 0b_10, Octal = 0o_7, Hexadecimal = 0x_10 }
\<close>

urust_expr composition_numeric_decimal \<open> CompositionNumeric::<u8, u16, 16> \<close>

urust_expr composition_numeric_hex \<open> CompositionNumeric::<u8, u16, 0x10> \<close>

urust_expr composition_numeric_binary \<open> CompositionNumeric::<u8, u16, 0b10000> \<close>

urust_expr composition_numeric_octal \<open> CompositionNumeric::<u8, u16, 0o20> \<close>

urust_expr composition_numeric_underscore \<open> CompositionNumeric::<u8, u16, 1_6> \<close>

urust_expr composition_numeric_prefix_underscore \<open> CompositionNumeric::<u8, u16, 0x_10> \<close>

urust_expr composition_numeric_binary_prefix_underscore \<open> CompositionNumeric::<u8, u16, 0b_10000> \<close>

urust_expr composition_numeric_octal_prefix_underscore \<open> CompositionNumeric::<u8, u16, 0o_20> \<close>

urust_expr composition_numeric_escape \<open> CompositionNumeric::<u8, u16, \<tau>\<open>16\<close>> \<close>

lemma composition_numeric_complete_literals:
  \<open>composition_numeric_decimal = composition_numeric_hex\<close>
  \<open>composition_numeric_decimal = composition_numeric_binary\<close>
  \<open>composition_numeric_decimal = composition_numeric_octal\<close>
  \<open>composition_numeric_decimal = composition_numeric_underscore\<close>
  \<open>composition_numeric_decimal = composition_numeric_prefix_underscore\<close>
  \<open>composition_numeric_decimal = composition_numeric_binary_prefix_underscore\<close>
  \<open>composition_numeric_decimal = composition_numeric_octal_prefix_underscore\<close>
  \<open>composition_numeric_decimal = composition_numeric_escape\<close>
  unfolding composition_numeric_decimal_def composition_numeric_hex_def
    composition_numeric_binary_def composition_numeric_octal_def
    composition_numeric_underscore_def composition_numeric_prefix_underscore_def
    composition_numeric_binary_prefix_underscore_def composition_numeric_octal_prefix_underscore_def
    composition_numeric_escape_def
  by (rule refl)+

urust_expr_rejects \<open> CompositionNumeric::<u8, u16, 4+4> \<close> \<open>unexpected input "+"\<close>

urust_expr_rejects \<open> CompositionNumeric::<u8, u16, 0x10+1> \<close> \<open>unexpected input "+"\<close>

urust_expr_rejects \<open> CompositionNumeric::<u8, u16, 4usize> \<close> \<open>unsuffixed integer literals\<close>

urust_expr_rejects \<open>
  match CompositionNumeric::<u8, u16, 4> {
    CompositionNumeric::<u8, u16, 4+4> => 0u8,
  }
\<close> \<open>unexpected input "+"\<close>

section\<open> Generic datatypes, aliases, typed receivers and effect channels \<close>

urust_datatype [hol_names = ["compositionValues" \<rightarrow> \<open>composition_values_model\<close>]] \<open>
  struct CompositionBuffer<T, const N: usize> { compositionValues: [T; N] }
\<close>

urust_type_alias \<open>
  type CompositionAlias<T, const N: usize> = CompositionBuffer<T, N>;
\<close>

urust_datatype [hol_type_parameters = ["P" \<rightarrow> \<open>'tag\<close>]] \<open>
  enum CompositionCustom<T, P, const N: usize> {
    CompositionEmpty,
    CompositionStored(CompositionAlias<T, N>),
  }
\<close>

urust_datatype [backend = hol, hol_names = [
  "NativeMissing" \<rightarrow> \<open>CompositionModelMissing\<close>,
  "NativeStored" \<rightarrow> \<open>CompositionModelStored\<close>
]] \<open>
  enum CompositionNative<T, P, const N: usize> {
    NativeMissing,
    NativeStored { payload: CompositionAlias<T, N> },
  }
\<close>

urust_datatype [word_width = 8, plugins = (plugins only: word_conversion urust_conversion),
  hol_names = ["Ready" \<rightarrow> \<open>CompositionModelReady\<close>]] \<open>
  enum CompositionWord<T, const N: usize> { CompositionOff, Ready = 11 }
\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionRead(self: CompositionAlias<u8, 4>) -> [u8; 4] { self.compositionValues }
\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionReadControl(value: CompositionBuffer<u8, 4>) -> [u8; 4] {
    value.compositionValues
  }
\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionCall(self: CompositionAlias<u8, 4>) -> [u8; 4] { CompositionRead(self) }
\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionMethod(self: CompositionAlias<u8, 4>) -> [u8; 4] { self.CompositionRead() }
\<close>

lemma composition_receiver_alias_equivalent:
  \<open>composition_read = composition_read_control\<close>
  unfolding composition_read_def composition_read_control_def by (rule refl)

lemma composition_default_registration_method:
  \<open>composition_call = composition_method\<close>
  unfolding composition_call_def composition_method_def by (rule refl)

urust_expr_rejects \<open>
  CompositionRead::<u8>(
    CompositionBuffer::<u8, 4> { compositionValues: \<llangle>array_constant (0 :: 8 word)\<rrangle> }
  )
\<close> \<open>generic arguments are not supported on generated Rust function paths\<close>

urust_expr_rejects \<open>
  (CompositionBuffer::<u8, 4> {
    compositionValues: \<llangle>array_constant (0 :: 8 word)\<rrangle>
  }).CompositionRead::<u8>()
\<close> \<open>generic arguments are not supported on generated Rust function paths\<close>

text\<open>
A name whose generated functions are monomorphic takes no generic arguments, even when a
payload would type-check as a leading argument. Generated generic functions instead consume their
source-ordered type/const parameters; explicit-only call notations keep their value payloads.
\<close>

urust_fn \<open> fn TurbofishPair(first: u8, second: u8) -> u8 { second } \<close>

urust_expr_rejects \<open> TurbofishPair::<1>(2u8) \<close> \<open>generic arguments are not supported on generated Rust function paths\<close>

text\<open>
These monomorphic legacy controls retain explicit-backend payload dispatch when an explicit
notation shares the name; an ordinary call still reaches the generated function. A key with an
eligible generated generic scheme and explicit call notations instead rejects turbofish as
ambiguous, as audited in the Generics pair.
\<close>

urust_fn [register_notation = false] \<open> fn TurbofishPairWide(first: u64, second: u64) -> u64 { second } \<close>

micro_rust_notation (call) turbofish_pair_wide ("TurbofishPair")
micro_rust_notation (call) turbofish_pair_wide ("TurbofishPairWideOnly")

urust_expr_rejects \<open> TurbofishPair::<1>(2u8) \<close> \<open>no backend matches the use-site type\<close>

urust_expr turbofish_mixed_explicit \<open> TurbofishPair::<1>(2u64) \<close>

urust_expr turbofish_mixed_explicit_control \<open> TurbofishPairWideOnly::<1>(2u64) \<close>

lemma \<open>turbofish_mixed_explicit = turbofish_mixed_explicit_control\<close>
  unfolding turbofish_mixed_explicit_def turbofish_mixed_explicit_control_def by (rule refl)

urust_expr turbofish_mixed_plain \<open> TurbofishPair(1, 2u8) \<close>

micro_rust_notation (call) turbofish_pair ("TurbofishPairGeneratedOnly")

urust_expr turbofish_generated_control \<open> TurbofishPairGeneratedOnly(1, 2u8) \<close>

lemma \<open>turbofish_mixed_plain = turbofish_generated_control\<close>
  unfolding turbofish_mixed_plain_def turbofish_generated_control_def by (rule refl)

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionCustomWrap(self: CompositionAlias<u8, 4>) -> CompositionCustom<u8, u16, 4> {
    CompositionCustom::<u8, u16, 4>::CompositionStored(self)
  }
\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionNativeWrap(self: CompositionAlias<u8, 4>) -> CompositionNative<u8, u16, 4> {
    CompositionNative::<u8, u16, 4>::NativeStored { payload: self }
  }
\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionWordRead(self: CompositionWord<u16, 0>) -> u8 { CompositionWord::to_u8(self) }
\<close>

lemma composition_native_constructor_identity:
  \<open>composition_native_wrap =
    (\<lambda>value. FunctionBody (funcall1 (lift_fun1 CompositionModelStored) (literal value)))\<close>
  unfolding composition_native_wrap_def by (rule refl)

lemma composition_word_plugin_identity:
  \<open>composition_word_read =
    (\<lambda>value. FunctionBody (funcall1 composition_word_to_u8 (literal value)))\<close>
  unfolding composition_word_read_def by (rule refl)

chapter\<open> Declared HOL types \<close>

section\<open> Declared and Rust-resolved types \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

text\<open>
A declared type that equals the resolved Rust signature produces the same definition. A declared
type that differs from the Rust signature, including its HOL escapes, replaces it entirely.
\<close>

urust_fn declared_successor :: \<open>64 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  \<open> fn DeclaredSuccessor(value: u64) -> u64 { value + 1 } \<close>

urust_fn \<open> fn RustSuccessor(value: u64) -> u64 { value + 1 } \<close>

lemma declared_successor_equivalent:
  \<open>declared_successor = rust_successor\<close>
  unfolding declared_successor_def rust_successor_def by (rule refl)

urust_fn :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  \<open> fn DeclaredIgnoredEscapes(value: \<tau>\<open>bool\<close>) -> \<tau>\<open>bool\<close> { value } \<close>

lemma declared_identity_equivalent:
  \<open>declared_identity = semantic_identity\<close>
  unfolding declared_identity_def semantic_identity_def by (rule refl)

lemma declared_unsupported_types_shape:
  \<open>declared_unsupported_types = (\<lambda>value _. FunctionBody (literal value))\<close>
  unfolding declared_unsupported_types_def by (rule refl)

lemma declared_identity_contract:
  fixes \<Gamma> :: \<open>('s::cancellative_sepalg, bool, nat, unit) striple_context\<close>
  shows \<open>\<Gamma>; declared_identity value \<Turnstile>\<^sub>F lift_pure_to_contract value\<close>
  by (crush_boot f: declared_identity_def contract: lift_pure_to_contract_def; crush_base)

section\<open> Declared channels, defaults and locale fixes \<close>

text\<open>
Rust source types may be retained literally even when they have no HOL interpretation.
These declarations exercise function pointers, iterator lifetime arguments, associated types,
const expressions, and types from an unexpanded Rust macro. Their complete HOL types alone
determine the resulting functions.
\<close>

urust_fn declared_native_function_pointer
  :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  \<open> fn DeclaredNativeFunctionPointer(value: fn(&Element) -> bool) -> bool { value } \<close>

urust_fn declared_native_iterator
  :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  \<open>
    fn DeclaredNativeIterator<'a>(value: slice::IterMut<'a, Element>)
      -> impl Iterator<Item = (&'a Element, u64)> {
      value
    }
  \<close>

urust_fn declared_native_const_expression
  :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  \<open>
    fn DeclaredNativeConstExpression(value: Buffer<{ Flavor::Small as usize }>)
      -> Buffer<{ Flavor::Large as usize }> {
      value
    }
  \<close>

urust_fn declared_native_macro_type
  :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  \<open> fn DeclaredNativeMacroType(value: $Scalar) -> FieldValue<$Scalar, Register> { value } \<close>

lemma declared_native_function_pointer_shape:
  \<open>declared_native_function_pointer = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding declared_native_function_pointer_def by (rule refl)

lemma declared_native_iterator_shape:
  \<open>declared_native_iterator = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding declared_native_iterator_def by (rule refl)

lemma declared_native_const_expression_shape:
  \<open>declared_native_const_expression = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding declared_native_const_expression_def by (rule refl)

lemma declared_native_macro_type_shape:
  \<open>declared_native_macro_type = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding declared_native_macro_type_def by (rule refl)

text\<open>
The declared type supplies every channel, so scoped channel defaults do not apply to it. Locale
type variables in a declared type remain fixed.
\<close>

context
  notes [[urust_state = \<open>unit\<close>, urust_abort = \<open>bool\<close>]]
begin

urust_fn :: \<open>nat \<Rightarrow> ('s, nat, unit, 'i, 'o) function_body\<close>
  \<open> fn DeclaredIgnoresDefaults(value: u64) -> u64 { value } \<close>

end

context semantic_type_locale
begin

urust_fn [register_notation = false]
  :: \<open>'s \<Rightarrow> ('s, 's, bool, 'i, 'o) function_body\<close>
  \<open> fn DeclaredLocaleIdentity(value: LocaleState) -> LocaleState { value } \<close>

end

lemma declared_interpreted_identity:
  \<open>function_body (semantic_unit.declared_locale_identity ()) =
    (literal () :: (unit, unit, unit, bool, nat prompt, unit prompt_output) expression)\<close>
  unfolding semantic_unit.declared_locale_identity_def by simp

section\<open> Native signatures with implicit manual backends \<close>

datatype 'a function_address_model = FunctionAddressModel
datatype 'g function_global_model = FunctionGlobalModel
datatype ('a, 'g) function_pair_model = FunctionPairModel

urust_type [implicit = \<open> address = 'addr \<close>]
  "FunctionAddress" = \<open> 'addr function_address_model \<close>
urust_type [implicit = \<open> global = 'store \<close>]
  "FunctionGlobal" = \<open> 'store function_global_model \<close>
urust_type [implicit = \<open> address = 'addr, global = 'store \<close>]
  "FunctionPair" = \<open> ('addr, 'store) function_pair_model \<close>

urust_fn [register_notation = false] function_address_native \<open>
  fn FunctionAddressNative(value: FunctionAddress) -> FunctionAddress { value }
\<close>
urust_fn [register_notation = false] function_address_escape \<open>
  fn FunctionAddressEscape(value: \<tau>\<open> 'a function_address_model \<close>)
      -> \<tau>\<open> 'a function_address_model \<close> { value }
\<close>

urust_fn [register_notation = false] function_global_native \<open>
  fn FunctionGlobalNative(value: FunctionGlobal) -> FunctionGlobal { value }
\<close>
urust_fn [register_notation = false] function_global_escape \<open>
  fn FunctionGlobalEscape(value: \<tau>\<open> 'g function_global_model \<close>)
      -> \<tau>\<open> 'g function_global_model \<close> { value }
\<close>

urust_fn [register_notation = false] function_pair_native \<open>
  fn FunctionPairNative(value: FunctionPair) -> FunctionPair { value }
\<close>
urust_fn [register_notation = false] function_pair_escape \<open>
  fn FunctionPairEscape(value: \<tau>\<open> ('a, 'g) function_pair_model \<close>)
      -> \<tau>\<open> ('a, 'g) function_pair_model \<close> { value }
\<close>

lemma backend_signature_twins:
  shows \<open>function_address_native = function_address_escape\<close>
    and \<open>function_global_native = function_global_escape\<close>
    and \<open>function_pair_native = function_pair_escape\<close>
  unfolding function_address_native_def function_address_escape_def
    function_global_native_def function_global_escape_def
    function_pair_native_def function_pair_escape_def
  by (rule refl)+

section\<open> Implicit mapping schemes through locale interpretations \<close>

locale function_backend_transport =
  fixes marker :: nat
begin

urust_type [implicit = \<open> address = 'addr \<close>]
  "FunctionTransportAddress" = \<open> 'addr function_address_model \<close>
urust_type [implicit = \<open> global = 'store \<close>]
  "FunctionTransportGlobal" = \<open> 'store function_global_model \<close>
urust_type [implicit = \<open> global = 'store, address = 'addr \<close>]
  "FunctionTransportPair" = \<open> ('addr, 'store) function_pair_model \<close>
urust_type [implicit = \<open> global = 'store, address = 'addr \<close>]
  "FunctionTransportWrapped<'value>" =
    \<open> ('addr, 'store) function_pair_model \<times> 'value \<close>

urust_type_alias \<open> type FunctionTransportAlias = FunctionTransportGlobal; \<close>
urust_type_alias \<open> type FunctionTransportPairAlias = FunctionTransportPair; \<close>
urust_type_alias \<open>
  type FunctionTransportWrappedAlias<Value> = FunctionTransportWrapped<Value>;
\<close>

urust_datatype [verbosity = 0, pretty = false] \<open>
  struct FunctionRolePacket {
    left: FunctionTransportAddress,
    right: FunctionTransportAlias,
    pair: FunctionTransportPairAlias,
  }
\<close>

urust_fn [register_notation = false, verbosity = 0, pretty = false]
  function_transport_identity \<open>
    fn FunctionTransportIdentity(value: FunctionTransportAlias) -> FunctionTransportGlobal { value }
  \<close>
urust_fn [register_notation = false, verbosity = 0, pretty = false]
  function_transport_pair_identity \<open>
    fn FunctionTransportPairIdentity<Value>(value: FunctionTransportWrappedAlias<Value>)
        -> FunctionTransportWrapped<Value> { value }
  \<close>

lemma function_transport_shapes:
  shows \<open>function_transport_identity = (\<lambda>value. FunctionBody (literal value))\<close>
    and \<open>function_transport_pair_identity = (\<lambda>value. FunctionBody (literal value))\<close>
  unfolding function_transport_identity_def function_transport_pair_identity_def
  by (rule refl)+

end

interpretation function_backend_zero: function_backend_transport 0 .
interpretation function_backend_one: function_backend_transport 1 .

section\<open> Implicit mappings in erased signature arguments \<close>

urust_type [erase = \<open> 'tag \<close>] "FunctionErased<'tag>" = \<open> nat \<close>
urust_type [implicit = \<open> address = 'a \<close>]
  "FunctionErasedInside" = \<open> 'a option \<close>
urust_fn [verbosity = 0, pretty = false] \<open>
fn FunctionErasedBackend(value: FunctionErased<FunctionErasedInside>)
  -> FunctionErased<FunctionErasedInside> { value }
\<close>
urust_fn [verbosity = 0, pretty = false] \<open>
fn FunctionErasedBackendTwin(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }
\<close>
lemma function_erased_backend_twin:
  \<open> function_erased_backend = function_erased_backend_twin \<close>
  unfolding function_erased_backend_def function_erased_backend_twin_def by (rule refl)

section\<open> Combined mappings in complete signatures \<close>

urust_type [implicit = \<open> address = 'addr, global = 'store \<close>,
  erase = \<open> 'tag, 'capacity \<close>]
  "FunctionCombined<'payload, 'tag, const 'capacity>" =
    \<open> ('addr, 'store, 'payload) Global_Store.ref \<close>
urust_type_alias \<open>
  type FunctionCombinedAlias<P, Tag, const N: usize> = FunctionCombined<P, Tag, N>;
\<close>

urust_fn [register_notation = false] function_combined_native \<open>
  fn FunctionCombinedNative(value: Option<FunctionCombinedAlias<u8, foreign::Policy<0>, 0>>,
      pointer: *const u8) -> Option<FunctionCombined<u8, foreign::Policy<0>, 0>> { value }
\<close>
urust_fn [register_notation = false] function_combined_escape \<open>
  fn FunctionCombinedEscape(value: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref option \<close>,
      pointer: \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref \<close>)
      -> \<tau>\<open> ('a, 'g, 8 word) Global_Store.ref option \<close> { value }
\<close>

lemma function_combined_twin:
  \<open> function_combined_native = function_combined_escape \<close>
  unfolding function_combined_native_def function_combined_escape_def by (rule refl)


section\<open> Lifetime relations preserve reference channels \<close>

urust_fn [register_notation = false] function_outlives_carry \<open>
  fn FunctionOutlivesCarry<'a: 'b, 'b: 'a>(value: &'a mut u8) -> &'a mut u8
  where 'a: 'a + 'b + 'static, 'b: 'a { value }
\<close>
urust_fn [register_notation = false] function_outlives_carry_plain \<open>
  fn FunctionOutlivesCarryPlain<'a>(value: &'a mut u8) -> &'a mut u8 { value }
\<close>
lemma function_outlives_carry_erased:
  \<open> function_outlives_carry = function_outlives_carry_plain \<close>
  unfolding function_outlives_carry_def function_outlives_carry_plain_def by (rule refl)

end
