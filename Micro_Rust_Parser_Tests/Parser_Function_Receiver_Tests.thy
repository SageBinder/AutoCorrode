theory Parser_Function_Receiver_Tests
  imports Parser_Function_Semantic_Type_Tests
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open> Explicit receiver types and ordinary parameter bindings \<close>

urust_fn [register_notation = false] typed_self_primitive
  \<open> fn TypedSelfPrimitive(self: u64) -> u64 { self } \<close>

urust_fn [register_notation = false] typed_self_value_primitive
  \<open> fn TypedSelfValuePrimitive(self_value: u64) -> u64 { self_value } \<close>

urust_fn [register_notation = false] typed_mut_self
  \<open> fn TypedMutSelf(mut self: u64) -> u64 { self } \<close>

lemma typed_self_primitive_equivalent:
  \<open>typed_self_primitive = typed_self_value_primitive\<close>
  unfolding typed_self_primitive_def typed_self_value_primitive_def by (rule refl)

lemma typed_mut_self_equivalent:
  \<open>typed_mut_self = typed_self_value_primitive\<close>
  unfolding typed_mut_self_def typed_self_value_primitive_def by (rule refl)

type_synonym widget_ref = \<open>(nat, unit, 8 word) Global_Store.ref\<close>

urust_fn [register_notation = false] typed_self_hol_ref
  \<open> fn TypedSelfHOLRef(self: \<tau>\<open>widget_ref\<close>) -> \<tau>\<open>widget_ref\<close> { self } \<close>

urust_fn [register_notation = false] typed_self_value_hol_ref
  \<open> fn TypedSelfValueHOLRef(self_value: \<tau>\<open>widget_ref\<close>) -> \<tau>\<open>widget_ref\<close> { self_value } \<close>

lemma typed_self_hol_ref_equivalent:
  \<open>typed_self_hol_ref = typed_self_value_hol_ref\<close>
  unfolding typed_self_hol_ref_def typed_self_value_hol_ref_def by (rule refl)

urust_type "ReceiverWidget" = \<open> fun_field_record \<close>

urust_fn [register_notation = false] typed_self_field
  \<open> fn TypedSelfField(self: ReceiverWidget) -> \<tau>\<open>nat\<close> { self.funFieldCollision } \<close>

urust_fn [register_notation = false] typed_self_value_field
  \<open> fn TypedSelfValueField(self_value: ReceiverWidget) -> \<tau>\<open>nat\<close> { self_value.funFieldCollision } \<close>

lemma typed_self_field_equivalent:
  \<open>typed_self_field = typed_self_value_field\<close>
  unfolding typed_self_field_def typed_self_value_field_def by (rule refl)

section\<open> HOL value and expression escapes \<close>

urust_fn [register_notation = false] typed_self_hol_value
  \<open> fn TypedSelfHOLValue(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self + 1\<rrangle> } \<close>

urust_fn [register_notation = false] typed_self_value_hol_value
  \<open> fn TypedSelfValueHOLValue(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self_value + 1\<rrangle> } \<close>

urust_fn [register_notation = false] typed_self_hol_expression
  \<open> fn TypedSelfHOLExpression(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<epsilon>\<open>literal (self + 1)\<close> } \<close>

urust_fn [register_notation = false] typed_self_value_hol_expression
  \<open> fn TypedSelfValueHOLExpression(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<epsilon>\<open>literal (self_value + 1)\<close> } \<close>

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

urust_fn
  [state = \<open>unit\<close>, abort = \<open>unit\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>,
   register_notation = false]
  typed_self_value_add
  \<open>
    fn ReceiverAddValue(self_value: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      \<llangle>self_value + delta\<rrangle>
    }
  \<close>

urust_notation (call) typed_self_add ("receiver_add")

urust_fn [register_notation = false] typed_self_method
  \<open>
    fn TypedSelfMethod(self: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      self.receiver_add(delta)
    }
  \<close>

urust_fn [register_notation = false] typed_self_value_method
  \<open>
    fn TypedSelfValueMethod(self_value: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      self_value.receiver_add(delta)
    }
  \<close>

urust_fn [register_notation = false] typed_self_direct
  \<open>
    fn TypedSelfDirect(self: \<tau>\<open>nat\<close>, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      ReceiverAdd(self, delta)
    }
  \<close>

urust_fn [register_notation = false] typed_self_field_method
  \<open>
    fn TypedSelfFieldMethod(self: ReceiverWidget, delta: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      self.funFieldCollision.receiver_add(delta)
    }
  \<close>

urust_fn [register_notation = false] typed_self_value_field_method
  \<open>
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

section\<open> Name collisions and nested lexical scope \<close>

micro_rust_notation (literal) \<open>True\<close> ("self")

urust_fn [register_notation = false] typed_self_literal_shadow
  \<open> fn TypedSelfLiteralShadow(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { self } \<close>

urust_fn [register_notation = false] typed_self_value_literal_shadow
  \<open> fn TypedSelfValueLiteralShadow(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { self_value } \<close>

urust_fn [register_notation = false] typed_self_name_collision
  \<open>
    fn TypedSelfNameCollision(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      let self_value = true;
      self
    }
  \<close>

urust_fn [register_notation = false] typed_self_value_name_collision
  \<open>
    fn TypedSelfValueNameCollision(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      let other_value = true;
      self_value
    }
  \<close>

urust_fn [register_notation = false] typed_self_closure
  \<open>
    fn TypedSelfClosure(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> {
      |self_value| \<llangle>self + self_value\<rrangle>
    }
  \<close>

urust_fn [register_notation = false] typed_self_value_closure
  \<open>
    fn TypedSelfValueClosure(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> {
      |other_value| \<llangle>self_value + other_value\<rrangle>
    }
  \<close>

context
  fixes self :: bool
begin

urust_fn [register_notation = false] typed_self_context_shadow
  \<open> fn TypedSelfContextShadow(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self + 1\<rrangle> } \<close>

urust_fn [register_notation = false] typed_self_value_context_shadow
  \<open> fn TypedSelfValueContextShadow(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self_value + 1\<rrangle> } \<close>

end

lemma typed_self_literal_shadow_equivalent:
  \<open>typed_self_literal_shadow = typed_self_value_literal_shadow\<close>
  unfolding typed_self_literal_shadow_def typed_self_value_literal_shadow_def by (rule refl)

lemma typed_self_name_collision_equivalent:
  \<open>typed_self_name_collision = typed_self_value_name_collision\<close>
  unfolding typed_self_name_collision_def typed_self_value_name_collision_def by (rule refl)

lemma typed_self_closure_equivalent:
  \<open>typed_self_closure = typed_self_value_closure\<close>
  unfolding typed_self_closure_def typed_self_value_closure_def by (rule refl)

lemma typed_self_context_shadow_equivalent:
  \<open>typed_self_context_shadow = typed_self_value_context_shadow\<close>
  unfolding typed_self_context_shadow_def typed_self_value_context_shadow_def by (rule refl)

section\<open> Complete declared schemes and receiver boundaries \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun check expected names =
      List.app (fn name =>
        require (name ^ ": receiver declaration scheme changed")
          (Sign.typ_equiv (Proof_Context.theory_of ctxt)
            (declared_type ctxt name, Logic.varifyT_global expected))) names
    val _ = check
      \<^typ>\<open>64 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close>
      ["typed_self_primitive", "typed_self_value_primitive", "typed_mut_self"]
    val _ = check
      \<^typ>\<open>widget_ref \<Rightarrow> ('s, widget_ref, 'abort, 'i, 'o) function_body\<close>
      ["typed_self_hol_ref", "typed_self_value_hol_ref"]
    val _ = check
      \<^typ>\<open>fun_field_record \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
      ["typed_self_field", "typed_self_value_field"]
    val _ = check
      \<^typ>\<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
      ["typed_self_hol_value", "typed_self_value_hol_value",
       "typed_self_hol_expression", "typed_self_value_hol_expression",
       "typed_self_literal_shadow", "typed_self_value_literal_shadow",
       "typed_self_name_collision", "typed_self_value_name_collision",
       "typed_self_context_shadow", "typed_self_value_context_shadow"]
    val _ = check
      \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
      ["typed_self_add", "typed_self_value_add", "typed_self_method",
       "typed_self_value_method", "typed_self_direct"]
    val _ = check
      \<^typ>\<open>fun_field_record \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
      ["typed_self_field_method", "typed_self_value_field_method"]
    val _ = check
      \<^typ>\<open>nat \<Rightarrow>
        ('s, nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body, 'abort, 'i, 'o) function_body\<close>
      ["typed_self_closure", "typed_self_value_closure"]
    val _ = require "method dispatch lost the registered typed receiver declaration"
      (Term.exists_subterm
        (fn Const (name, _) => name = \<^const_name>\<open>typed_self_add\<close> | _ => false)
        (rhs ctxt "typed_self_method"))

    val base = initial \<^theory>
    val recovered_item = "fn ReceiverRecovery(self: u8) -> u8 { self }"
    fun reject (label, expected, item) =
      let
        val (result, reports) = Parser_Test_Reports.markup (fn () =>
          Exn.capture (run_from base label) (command "" "receiver_failure" item))
        val diagnostic = message result
        val _ = require (label ^ ": wrong diagnostic") (String.isSubstring expected diagnostic)
        val _ = require (label ^ ": no source position")
          (String.isSubstring label diagnostic andalso not (null (diagnostic_ranges diagnostic)))
        val _ = require (label ^ ": installed declaration markup")
          (null (declaration_definitions reports))
        val _ = require (label ^ ": mutated constant table")
          (constant_snapshot ctxt = constant_snapshot (Toplevel.context_of base))
        val _ = registry_unchanged label ctxt (Toplevel.context_of base)
        val recovered =
          run_from base (label ^ "-recovery") (command "" "receiver_failure" recovered_item)
          |> Toplevel.context_of
        val _ = require (label ^ ": failed to recover the typed receiver")
          (binder_types (declared_type recovered "receiver_failure") = [\<^typ>\<open>8 word\<close>])
      in () end
    val _ = List.app reject
      [("receiver-untyped-self", "syntax error", "fn BadReceiver(self) -> u8 { self }"),
       ("receiver-borrowed-shorthand", "syntax error", "fn BadReceiver(&self) -> u8 { self }"),
       ("receiver-mut-borrowed-shorthand", "syntax error", "fn BadReceiver(&mut self) -> u8 { self }"),
       ("receiver-borrowed-pattern", "unsupported function parameter pattern",
        "fn BadReceiver(&self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { self }"),
       ("receiver-implicit-Self", "unknown Rust type", "fn BadReceiver(self: Self) -> Self { self }"),
       ("receiver-rust-reference", "Rust reference types", "fn BadReceiver(self: &u8) -> u8 { 0 }"),
       ("receiver-duplicate", "duplicate parameter \"self\"",
        "fn BadReceiver(self: u8, self: bool) -> u8 { self }"),
       ("receiver-body-type", "Type unification failed", "fn BadReceiver(self: bool) -> u8 { self }")]
  in val _ = () end
\<close>

end
