(* Positive function conformance against the seven corpus FunctionBody definitions
   and the supported urust_fn declaration surface. *)

theory Parser_Tests_Fun
  imports Parser_Test_Utils Conformance_Corpus
begin

declare [[urust_conformance_check = true]]

section\<open>Corpus FunctionBody definitions\<close>

urust_fn answer ::
  \<open>('s, 32 word, 'abort, 'i, 'o) function_body\<close>
  ()
  \<open> \<llangle>42 :: 32 word\<rrangle> \<close>

thm answer_conformance

urust_fn inc ::
  \<open>32 word \<Rightarrow> ('s, 32 word, 'abort, 'i, 'o) function_body\<close>
  (x)
  \<open> x + \<llangle>1 :: 32 word\<rrangle> \<close>

urust_fn add3 ::
  \<open>32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word, 'abort, 'i, 'o) function_body\<close>
  (a, b, c)
  \<open> a + b + c \<close>

urust_fn is_zero ::
  \<open>32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close>
  (x)
  \<open> x == \<llangle>0 :: 32 word\<rrangle> \<close>

urust_fn safe_div ::
  \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, (32 word, unit) result, 'abort, 'i, 'o) function_body\<close>
  (a, b)
  \<open> if b == \<llangle>0 :: 32 word\<rrangle> { Err(()) } else { Ok(a / b) } \<close>

urust_fn discard ::
  \<open>32 word \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
  (x)
  \<open> () \<close>

urust_fn test ::
  \<open>(nat, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> let x = \<llangle>Some (0 :: nat)\<rrangle>; let Some(foo) = x else { return; }; return; \<close>
hide_const test


section\<open>Signature surface\<close>

urust_fn fun_heterogeneous ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow>
    ('s, nat * bool * 32 word, 'abort, 'i, 'o) function_body\<close>
  (number, flag, word)
  \<open> \<llangle>(number, flag, word)\<rrangle> \<close>

urust_fn fun_polymorphic ::
  \<open>'a \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn fun_sort_constrained ::
  \<open>'a::len word \<Rightarrow>
    ('s, 'a word, 'abort, 'i, 'o) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn fun_type_placeholders ::
  \<open>_ \<Rightarrow> (_, _, _, _, _) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn fun_higher_order ::
  \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>
    ('s, nat, 'abort, 'i, 'o) function_body\<close>
  (f, item)
  \<open> \<llangle>f item\<rrangle> \<close>

urust_fn fun_nested_result ::
  \<open>('s, (nat option, (bool, unit) result) result,
    'abort, 'i, 'o) function_body\<close>
  ()
  \<open> Ok(Some(\<llangle>1 :: nat\<rrangle>)) \<close>

urust_fn fun_explicit_prompt_output ::
  \<open>nat \<Rightarrow>
    (unit, nat, unit, unit prompt, unit prompt_output) function_body\<close>
  (item)
  \<open> item \<close>



section\<open>Argument-list boundaries\<close>

urust_fn fun_zero_arguments ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> () \<close>

urust_fn fun_one_argument ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn fun_trailing_comma ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, nat * bool, unit, unit, unit) function_body\<close>
  (item, flag,)
  \<open> \<llangle>(item, flag)\<rrangle> \<close>

urust_fn fun_multiline_arguments ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit) function_body\<close>
  (
    number,
    flag,
    word,
  )
  \<open> if flag { word } else { \<llangle>of_nat number\<rrangle> } \<close>

urust_fn fun_sixteen_arguments ::
  \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body
  \<close>
  (
    p01, p02, p03, p04, p05, p06, p07, p08,
    p09, p10, p11, p12, p13, p14, p15, p16
  )
  \<open>
    \<llangle>
      p01 + p02 + p03 + p04 + p05 + p06 + p07 + p08 +
      p09 + p10 + p11 + p12 + p13 + p14 + p15 + p16
    \<rrangle>
  \<close>


section\<open>Ambient binding and scope\<close>

urust_fn fun_plain_parameter ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_fn fun_value_antiquotation ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<llangle>item + 1\<rrangle> \<close>

urust_fn fun_expression_antiquotation ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<epsilon>\<open>literal (item + 1)\<close> \<close>

urust_fn fun_parameter_call ::
  \<open>
    (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
    nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body
  \<close>
  (callee, item)
  \<open> callee(item) \<close>

urust_fn fun_parameter_in_match_guard ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    match Some(item) {
      Some(inner) if inner == item \<Rightarrow> inner,
      _ \<Rightarrow> item
    }
  \<close>

urust_fn fun_parameter_in_loop ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) {
      let observed = item;
      ()
    }
    item
  \<close>

urust_fn fun_parameter_in_closure ::
  \<open>nat \<Rightarrow>
    (unit, nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body,
      unit, unit, unit) function_body\<close>
  (outer)
  \<open> |inner| \<llangle>outer + inner\<rrangle> \<close>

datatype fun_struct_fixture = FunStructFixture nat bool

definition fun_struct_fixture_lift ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, fun_struct_fixture, unit, unit, unit) function_body\<close>
  where \<open>fun_struct_fixture_lift \<equiv> lift_fun2 FunStructFixture\<close>

micro_rust_notation (call) fun_struct_fixture_lift ("FunStructFixture")

urust_fn fun_parameter_in_struct ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, fun_struct_fixture, unit, unit, unit) function_body\<close>
  (item, flag)
  \<open> FunStructFixture { item: item, flag: flag } \<close>

urust_fn fun_nested_let_shadow ::
  \<open>nat \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  (item)
  \<open> let item = true; item \<close>

urust_fn fun_nested_pattern_shadow ::
  \<open>nat \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  (item)
  \<open>
    let (item, retained) = (true, \<llangle>item\<rrangle>);
    item
  \<close>

urust_fn fun_closure_shadow ::
  \<open>bool \<Rightarrow>
    (unit, nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body,
      unit, unit, unit) function_body\<close>
  (item)
  \<open> |item| \<llangle>item :: nat\<rrangle> \<close>

context
  fixes item :: bool
begin

urust_fn fun_parameter_shadows_context ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<llangle>item :: nat\<rrangle> \<close>

end

urust_fn fun_distinct_heterogeneous ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> String.literal \<Rightarrow>
    (unit, nat * bool * String.literal, unit, unit, unit) function_body\<close>
  (number, flag, message)
  \<open> \<llangle>(number, flag, message)\<rrangle> \<close>


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

urust_fn fun_registered_call_wins ::
  \<open>
    (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
    nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body
  \<close>
  (funCollision, item)
  \<open> funCollision(item) \<close>

urust_fn fun_registered_field_wins ::
  \<open>fun_field_record \<Rightarrow> (fun_field_record, nat) lens \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body\<close>
  (item, funFieldCollision)
  \<open> item.funFieldCollision \<close>

section\<open>Isabelle declaration integration\<close>

context
begin

qualified urust_fn qualified_identity ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

end

locale fun_command_locale =
  fixes offset :: nat
begin

urust_fn local_add ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> \<llangle>item + offset\<rrangle> \<close>

end

end
