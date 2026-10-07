(* Positive function tests for the supported urust_fn declaration surface. *)

theory Parser_Function_Tests
  imports
    Parser_Test_Utils
    Parser_Iterator_Fixtures
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open>Iterator semantics and call syntax\<close>

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

text\<open>
The direct, method, and chained forms all use the normal call pipeline. The method form contributes
exactly one receiver and one explicit argument.
\<close>

urust_fn [register_notation = false] iterator_zip_direct
  \<open> fn iterator_zip_direct(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> { zip(left, right) } \<close>

urust_fn [register_notation = false] iterator_zip_method
  \<open> fn iterator_zip_method(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> { left.zip(right) } \<close>

urust_fn [register_notation = false] iterator_zip_chained
  \<open> fn iterator_zip_chained(left: \<tau>\<open>zip_left_iterator\<close>, right: \<tau>\<open>zip_right_iterator\<close>) -> \<tau>\<open>zip_pair_iterator\<close> { left.into_iter().zip(right.into_iter()) } \<close>
lemma hol_list_zip_is_unchanged:
  shows \<open>List.zip [1 :: nat, 2] [True] = [(1, True)]\<close>
  by simp

section\<open>FunctionBody definitions\<close>

urust_fn [register_notation = false] answer
  \<open> fn answer() -> u32 { \<llangle>42 :: 32 word\<rrangle> } \<close>
urust_fn [register_notation = false] inc
  \<open> fn inc(x: u32) -> u32 { x + \<llangle>1 :: 32 word\<rrangle> } \<close>

urust_fn [register_notation = false] add3
  \<open> fn add3(a: u32, b: u32, c: u32) -> u32 { a + b + c } \<close>

urust_fn [register_notation = false] is_zero
  \<open> fn is_zero(x: u32) -> bool { x == \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_fn [register_notation = false] safe_div
  \<open> fn safe_div(a: u32, b: u32) -> \<tau>\<open>(32 word, unit) result\<close> { if b == \<llangle>0 :: 32 word\<rrangle> { Err(()) } else { Ok(a / b) } } \<close>

urust_fn [register_notation = false] discard
  \<open> fn discard(x: u32) -> () { () } \<close>

urust_fn [register_notation = false] test
  \<open> fn test() -> () { let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; } \<close>
hide_const test


section\<open>Signature surface\<close>

urust_fn [register_notation = false] fun_heterogeneous
  \<open> fn fun_heterogeneous(number: \<tau>\<open>nat\<close>, flag: bool, word: u32) -> \<tau>\<open>nat * bool * 32 word\<close> { \<llangle>(number, flag, word)\<rrangle> } \<close>

urust_fn [register_notation = false] fun_polymorphic
  \<open> fn fun_polymorphic(item: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { item } \<close>

urust_fn [register_notation = false] fun_sort_constrained
  \<open> fn fun_sort_constrained(item: \<tau>\<open>'a::len word\<close>) -> \<tau>\<open>'a word\<close> { item } \<close>

urust_fn [register_notation = false] fun_type_placeholders
  \<open> fn fun_type_placeholders(item: \<tau>\<open>_\<close>) { item } \<close>

urust_fn [register_notation = false] fun_higher_order
  \<open> fn fun_higher_order(f: \<tau>\<open>(nat \<Rightarrow> nat)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>f item\<rrangle> } \<close>

urust_fn [register_notation = false] fun_nested_result
  \<open> fn fun_nested_result() -> \<tau>\<open>(nat option, (bool, unit) result) result\<close> { Ok(Some(\<llangle>1 :: nat\<rrangle>)) } \<close>

urust_fn [register_notation = false] fun_explicit_prompt_output
  \<open> fn fun_explicit_prompt_output(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>



section\<open>Argument-list boundaries\<close>

urust_fn [register_notation = false] fun_zero_arguments
  \<open> fn fun_zero_arguments() -> () { () } \<close>

urust_fn [register_notation = false] fun_one_argument
  \<open> fn fun_one_argument(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>

urust_fn [register_notation = false] fun_trailing_comma
  \<open> fn fun_trailing_comma(item: \<tau>\<open>nat\<close>, flag: bool) -> \<tau>\<open>nat * bool\<close> { \<llangle>(item, flag)\<rrangle> } \<close>

urust_fn [register_notation = false] fun_multiline_arguments
  \<open> fn fun_multiline_arguments(number: \<tau>\<open>nat\<close>, flag: bool, word: u32) -> u32 { if flag { word } else { \<llangle>of_nat number\<rrangle> } } \<close>

urust_fn [register_notation = false] fun_sixteen_arguments
  \<open>
  fn fun_sixteen_arguments(p01: \<tau>\<open>nat\<close>, p02: \<tau>\<open>nat\<close>, p03: \<tau>\<open>nat\<close>, p04: \<tau>\<open>nat\<close>, p05: \<tau>\<open>nat\<close>, p06: \<tau>\<open>nat\<close>, p07: \<tau>\<open>nat\<close>, p08: \<tau>\<open>nat\<close>, p09: \<tau>\<open>nat\<close>, p10: \<tau>\<open>nat\<close>, p11: \<tau>\<open>nat\<close>, p12: \<tau>\<open>nat\<close>, p13: \<tau>\<open>nat\<close>, p14: \<tau>\<open>nat\<close>, p15: \<tau>\<open>nat\<close>, p16: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    \<llangle>
      p01 + p02 + p03 + p04 + p05 + p06 + p07 + p08 +
      p09 + p10 + p11 + p12 + p13 + p14 + p15 + p16
    \<rrangle>
  }
  \<close>


section\<open>Ambient binding and scope\<close>

urust_fn [register_notation = false] fun_plain_parameter
  \<open> fn fun_plain_parameter(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>

urust_fn [register_notation = false] fun_prime_parameter
  \<open> fn fun_prime_parameter(item': \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item' } \<close>

urust_fn [register_notation = false] fun_value_antiquotation
  \<open> fn fun_value_antiquotation(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>item + 1\<rrangle> } \<close>

urust_fn [register_notation = false] fun_expression_antiquotation
  \<open> fn fun_expression_antiquotation(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<epsilon>\<open>literal (item + 1)\<close> } \<close>

urust_fn [register_notation = false] fun_parameter_call
  \<open> fn fun_parameter_call(callee: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { callee(item) } \<close>

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
  \<open> fn fun_parameter_in_closure(outer: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> { |inner| \<llangle>outer + inner\<rrangle> } \<close>

datatype fun_struct_fixture = FunStructFixture nat bool

definition fun_struct_fixture_lift ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, fun_struct_fixture, unit, unit, unit) function_body\<close>
  where \<open>fun_struct_fixture_lift \<equiv> lift_fun2 FunStructFixture\<close>

micro_rust_notation (call) fun_struct_fixture_lift ("FunStructFixture")

urust_fn [register_notation = false] fun_parameter_in_struct
  \<open> fn fun_parameter_in_struct(item: \<tau>\<open>nat\<close>, flag: bool) -> \<tau>\<open>fun_struct_fixture\<close> { FunStructFixture { item: item, flag: flag } } \<close>

urust_fn [register_notation = false] fun_nested_let_shadow
  \<open> fn fun_nested_let_shadow(item: \<tau>\<open>nat\<close>) -> bool { let item = true; item } \<close>

urust_fn [register_notation = false] fun_nested_pattern_shadow
  \<open>
  fn fun_nested_pattern_shadow(item: \<tau>\<open>nat\<close>) -> bool {
    let (item, retained) = (true, \<llangle>item\<rrangle>);
    item
  }
  \<close>

urust_fn [register_notation = false] fun_closure_shadow
  \<open> fn fun_closure_shadow(item: bool) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> { |item| \<llangle>item :: nat\<rrangle> } \<close>

context
  fixes item :: bool
begin

urust_fn [register_notation = false] fun_parameter_shadows_context
  \<open> fn fun_parameter_shadows_context(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>item :: nat\<rrangle> } \<close>

end

urust_fn [register_notation = false] fun_distinct_heterogeneous
  \<open> fn fun_distinct_heterogeneous(number: \<tau>\<open>nat\<close>, flag: bool, message: \<tau>\<open>String.literal\<close>) -> \<tau>\<open>nat * bool * String.literal\<close> { \<llangle>(number, flag, message)\<rrangle> } \<close>


section\<open>Role-specific notation precedence\<close>

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

urust_fn [register_notation = false]  fun_parameter_call_wins
  \<open> fn fun_parameter_call_wins(funCollision: \<tau>\<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body)\<close>, item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { funCollision(item) } \<close>

urust_fn [register_notation = false] fun_registered_field_wins
  \<open> fn fun_registered_field_wins(item: \<tau>\<open>fun_field_record\<close>, funFieldCollision: \<tau>\<open>(fun_field_record, nat) lens\<close>) -> \<tau>\<open>nat\<close> { item.funFieldCollision } \<close>

section\<open>Isabelle declaration integration\<close>

context
begin

qualified urust_fn [register_notation = false] qualified_identity
  \<open> fn qualified_identity(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { item } \<close>

end

locale fun_command_locale =
  fixes offset :: nat
begin

urust_fn [register_notation = false] local_add
  \<open> fn local_add(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>item + offset\<rrangle> } \<close>

end

end
