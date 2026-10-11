theory Parser_Datatype_Composition_Tests
  imports Parser_Function_Receiver_Tests
begin

declare [[urust_pp_test = true, urust_pretty = false, urust_verbosity = 0]]

section\<open> Complete const arguments and radix discriminants \<close>

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

ML_val \<open>
  val ctxt = \<^context>
  val value_type = fastype_of (Syntax.read_term ctxt "composition_numeric_hex")
    |> dest_Type |> snd |> (fn parameters => nth parameters 1)
  val _ = if value_type = \<^typ>\<open>(8 word, 16 word, 16) composition_numeric\<close>
    then () else error "constructor length literal lost its complete radix value"
  val _ = List.app (fn text =>
    if is_none (Parser_Utils.read_unsigned_integer text) then ()
    else error ("partial or malformed numeric spelling accepted: " ^ text))
    ["4+4", "0x10+1", "0x0x10", "0b102", "0o8", "4usize", "-4", "", "_4", "0x_"]
  val _ = List.app (fn (text, expected) =>
    if Parser_Utils.read_unsigned_integer text = SOME expected then ()
    else error ("complete numeric spelling changed: " ^ text))
    [("4", 4), ("1_6", 16), ("0x10", 16), ("0b10000", 16), ("0o20", 16),
     ("0x_10", 16), ("0b_10000", 16), ("0o_20", 16)]
  val malformed = URust_AST.Integer_Literal
    ("4+4", URust_AST.make_source_layout Position.none [], NONE)
  val argument = URust_AST.Rust_Numeric_Argument malformed
  val _ =
    (case Exn.capture (fn () =>
      URust_Type_Mappings.instantiate_constructor ctxt "CompositionNumeric"
        [URust_AST.Rust_Type_Argument
           (URust_AST.Primitive_Type (URust_AST.DPT_U8, Position.none)),
         URust_AST.Rust_Type_Argument
           (URust_AST.Primitive_Type (URust_AST.DPT_U16, Position.none)),
         argument]
        (URust_Item_Scope.constructor_scheme
          (the (URust_Item_Scope.lookup_constructor ctxt "CompositionNumeric")))) () of
       Exn.Exn (ERROR message) =>
         if String.isSubstring "invalid complete unsuffixed length literal" message then ()
         else error ("wrong malformed numeric AST diagnostic: " ^ message)
     | Exn.Exn exn => Exn.reraise exn
     | Exn.Res _ => error "malformed programmatic numeric AST consumed a prefix")
\<close>

section\<open> Generic datatypes, aliases, typed receivers and effect channels \<close>

urust_datatype [renames = ["compositionValues" \<rightarrow> "composition_values_model"]] \<open>
  struct CompositionBuffer<T, const N: usize> { compositionValues: [T; N] }
\<close>
urust_type_alias \<open>
  type CompositionAlias<T, const N: usize> = CompositionBuffer<T, N>;
\<close>
urust_datatype [parameters = ["P" \<rightarrow> "'tag"]] \<open>
  enum CompositionCustom<T, P, const N: usize> {
    CompositionEmpty,
    CompositionStored(CompositionAlias<T, N>),
  }
\<close>
urust_datatype [backend = hol, renames = [
  "NativeMissing" \<rightarrow> "CompositionModelMissing",
  "NativeStored" \<rightarrow> "CompositionModelStored"
]] \<open>
  enum CompositionNative<T, P, const N: usize> {
    NativeMissing,
    NativeStored { payload: CompositionAlias<T, N> },
  }
\<close>
urust_datatype [word_width = 8, plugins = (plugins only: word_conversion urust_conversion),
  renames = ["Ready" \<rightarrow> "CompositionModelReady"]] \<open>
  enum CompositionWord<T, const N: usize> { CompositionOff, Ready = 11 }
\<close>

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  composition_read \<open>
  fn CompositionRead(self: CompositionAlias<u8, 4>) -> [u8; 4] { self.compositionValues }
\<close>
urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  composition_read_control \<open>
  fn CompositionReadControl(value: CompositionBuffer<u8, 4>) -> [u8; 4] {
    value.compositionValues
  }
\<close>
urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  composition_call \<open>
  fn CompositionCall(self: CompositionAlias<u8, 4>) -> [u8; 4] { CompositionRead(self) }
\<close>
urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  composition_method \<open>
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

urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  composition_custom_wrap \<open>
  fn CompositionCustomWrap(self: CompositionAlias<u8, 4>) -> CompositionCustom<u8, u16, 4> {
    CompositionCustom::<u8, u16, 4>::CompositionStored(self)
  }
\<close>
urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  composition_native_wrap \<open>
  fn CompositionNativeWrap(self: CompositionAlias<u8, 4>) -> CompositionNative<u8, u16, 4> {
    CompositionNative::<u8, u16, 4>::NativeStored { payload: self }
  }
\<close>
urust_fn [state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>]
  composition_word_read \<open>
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

ML_val \<open>
local
  open Parser_Function_Regression_Test
  val ctxt = \<^context>
  fun scheme name expected =
    require (name ^ ": composed declaration scheme changed")
      (Sign.typ_equiv (Proof_Context.theory_of ctxt)
        (declared_type ctxt name, Logic.varifyT_global expected))
  val _ = List.app (fn name => scheme name
    \<^typ>\<open>(8 word, 4) composition_buffer \<Rightarrow>
      (unit, (8 word, 4) array, bool, nat prompt, unit prompt_output) function_body\<close>)
    ["composition_read", "composition_read_control", "composition_call", "composition_method"]
  val _ = scheme "composition_custom_wrap"
    \<^typ>\<open>(8 word, 4) composition_buffer \<Rightarrow>
      (unit, (8 word, 16 word, 4) composition_custom, bool, nat prompt, unit prompt_output) function_body\<close>
  val _ = scheme "composition_native_wrap"
    \<^typ>\<open>(8 word, 4) composition_buffer \<Rightarrow>
      (unit, (8 word, 16 word, 4) composition_native, bool, nat prompt, unit prompt_output) function_body\<close>
  val _ = scheme "composition_word_read"
    \<^typ>\<open>(16 word, 0) composition_word \<Rightarrow>
      (unit, 8 word, bool, nat prompt, unit prompt_output) function_body\<close>
  val _ = require "custom enum unexpectedly acquired native BNF metadata"
    (is_none (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>composition_custom\<close>))
  val _ = require "explicit HOL backend lost native BNF metadata"
    (is_some (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>composition_native\<close>))
  val _ = require "word backend lost its native typedef"
    (not (null (Typedef.get_info ctxt \<^type_name>\<open>composition_word\<close>)))
  val mapping = the (URust_Type_Mappings.lookup ctxt "CompositionCustom")
  val _ = require "payload alias failed to propagate the const sort"
    (URust_Type_Mappings.entry_parameter_sorts mapping =
      [\<^sort>\<open>type\<close>, \<^sort>\<open>type\<close>, \<^sort>\<open>len\<close>])
  val word_mapping = the (URust_Type_Mappings.lookup ctxt "CompositionWord")
  val _ = require "word plugin discarded an unused parameter or strengthened const sort"
    (URust_Type_Mappings.entry_parameter_sorts word_mapping =
      [\<^sort>\<open>type\<close>, \<^sort>\<open>len0\<close>])
  val buffer = the (URust_Item_Scope.lookup_constructor ctxt "CompositionBuffer")
  val _ = require "selector rename changed the original Rust field identity"
    (map (apsnd dest_Const_name) (URust_Item_Scope.constructor_fields buffer) =
      [("compositionValues", \<^const_name>\<open>composition_values_model\<close>)])
  val native = the (URust_Item_Scope.lookup_constructor ctxt "CompositionNative::NativeStored")
  val _ = require "constructor rename changed the original Rust path identity"
    (dest_Const_name (URust_Item_Scope.constructor_term native) =
      \<^const_name>\<open>CompositionModelStored\<close>)
  val function = the (URust_Item_Scope.lookup_function ctxt "CompositionRead")
  val _ = require "typed receiver function lost default callable registration"
    (dest_Const_name (URust_Item_Scope.function_term function) =
      \<^const_name>\<open>composition_read\<close>)
in val _ = () end
\<close>

section\<open> Scoped registration with complete generic type mappings \<close>

locale composition_declaration_scope
begin

declare [[urust_register_notation = false]]
urust_datatype \<open> struct CompositionLocal<T, P, const N: usize>(T); \<close>
urust_type_alias \<open> type CompositionLocalAlias<T, P, const N: usize> = CompositionLocal<T, P, N>; \<close>
urust_fn \<open>
  fn CompositionScopedOff(self: CompositionLocalAlias<u8, u16, 0>) -> CompositionLocal<u8, u16, 0> { self }
\<close>
urust_fn [register_notation, state = \<open>unit\<close>, abort = \<open>bool\<close>,
  input = \<open>nat prompt\<close>, output = \<open>unit prompt_output\<close>] \<open>
  fn CompositionScopedOn(self: CompositionLocalAlias<u8, u16, 0>) -> CompositionLocal<u8, u16, 0> { self }
\<close>
urust_fn [register_notation] \<open>
  fn CompositionScopedClient(self: CompositionLocalAlias<u8, u16, 0>) -> CompositionLocal<u8, u16, 0> {
    CompositionScopedOn(self)
  }
\<close>

ML_val \<open>
  val ctxt = \<^context>
  val _ = if is_none (URust_Item_Scope.lookup_function ctxt "CompositionScopedOff") andalso
    is_some (URust_Item_Scope.lookup_function ctxt "CompositionScopedOn") andalso
    is_some (URust_Item_Scope.lookup_type ctxt "CompositionLocal") andalso
    is_some (URust_Type_Mappings.lookup ctxt "CompositionLocalAlias")
    then () else error "scoped registration suppressed complete mappings or ignored inline precedence"
\<close>

end

ML_val \<open>
  val ctxt = \<^context>
  val _ = if is_none (URust_Item_Scope.lookup_type ctxt "CompositionLocal") andalso
    is_none (URust_Item_Scope.lookup_constructor ctxt "CompositionLocal") andalso
    is_none (URust_Type_Mappings.lookup ctxt "CompositionLocalAlias") andalso
    forall (is_none o URust_Item_Scope.lookup_function ctxt)
      ["CompositionScopedOff", "CompositionScopedOn", "CompositionScopedClient"]
    then () else error "generic declaration or typed receiver registration escaped its locale"
\<close>

section\<open> Read-only replay of composed declarations \<close>

ML_val \<open>
local
  open Parser_Function_Regression_Test
  val thy = \<^theory>
  val base = initial thy
  fun commands rendering =
    "urust_datatype [" ^ rendering ^
      ", backend = hol, renames = [\"Stored\" \<rightarrow> \"CompositionReplayStored\"]] " ^
      cartouche "enum CompositionReplay<T, P, const N: usize> { Stored(T), Absent }" ^ "\n" ^
    "urust_type_alias " ^
      cartouche "type CompositionReplayAlias<T, P, const N: usize> = CompositionReplay<T, P, N>;" ^ "\n" ^
    "urust_fn [" ^ rendering ^ ", state = " ^ cartouche "unit" ^
      ", abort = " ^ cartouche "bool" ^ ", input = " ^ cartouche "nat prompt" ^
      ", output = " ^ cartouche "unit prompt_output" ^ "] composition_replay_identity " ^
      cartouche "fn CompositionReplayIdentity(self: CompositionReplayAlias<u8, u16, 0>) -> CompositionReplay<u8, u16, 0> { self }" ^ "\n" ^
    "urust_fn [" ^ rendering ^ "] composition_replay_client " ^
      cartouche "fn CompositionReplayClient(self: CompositionReplay<u8, u16, 0>) -> CompositionReplayAlias<u8, u16, 0> { CompositionReplayIdentity(self) }"
  fun run rendering =
    Parser_Test_Report_Lock.run (fn () =>
      run_from base "composition-replay" (commands rendering)) |> Toplevel.context_of
  val plain = run "pretty = false, pp_test = false, verbosity = 0"
  val replayed = run "pretty, pp_test, verbosity = 2"
  fun mappings ctxt = URust_Type_Mappings.dump ctxt
    |> map (fn (name, entry) =>
      (name, URust_Type_Mappings.entry_template entry, URust_Type_Mappings.entry_arities entry,
       URust_Type_Mappings.entry_parameter_sorts entry,
       URust_Type_Mappings.entry_backend_parameter_sorts entry))
  val _ = require "composed pretty replay changed generated type schemes" (mappings plain = mappings replayed)
  val _ = require "composed pretty replay changed the registered type count"
    (length (URust_Item_Scope.dump_types plain) = length (URust_Item_Scope.dump_types replayed))
  val _ = require "composed pretty replay changed the constructor count"
    (length (URust_Item_Scope.dump_constructors plain) = length (URust_Item_Scope.dump_constructors replayed))
  val _ = require "composed pretty replay changed the function count"
    (length (URust_Item_Scope.dump_functions plain) = length (URust_Item_Scope.dump_functions replayed))
  val _ = List.app (fn name =>
    require (name ^ ": composed replay changed the complete HOL type or body")
      (Sign.typ_equiv thy (declared_type plain name, declared_type replayed name) andalso
       Term.aconv (rhs plain name, rhs replayed name)))
    ["composition_replay_identity", "composition_replay_client"]
in val _ = () end
\<close>

end
