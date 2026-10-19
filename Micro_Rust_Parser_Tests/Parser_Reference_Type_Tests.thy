theory Parser_Reference_Type_Tests
  imports
    Parser_Function_Receiver_Tests
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

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

locale reference_signature_context =
  fixes fixed_reference :: "('address, 'global, 8 word) Global_Store.ref"
begin

urust_fn \<open>
  fn LocaleReferenceChoice(value: &mut u8) -> &mut u8 {
    if true { value } else { fixed_reference }
  }
\<close>

ML_val\<open>
  val _ =
    if member (op =)
        (binder_types (fastype_of (Syntax.read_term \<^context> "locale_reference_choice")))
        (fastype_of (Syntax.read_term \<^context> "fixed_reference"))
    then ()
    else error "locale reference signature lost its rigid backend"
\<close>

end

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun check expected names =
      List.app (fn name =>
        require (name ^ ": reference declaration scheme changed")
          (Sign.typ_equiv (Proof_Context.theory_of ctxt)
            (declared_type ctxt name, Logic.varifyT_global expected))) names
    val _ = check
      \<^typ>\<open>('a, 'b, 8 word) Global_Store.ref \<Rightarrow>
        ('s, ('a, 'b, 8 word) Global_Store.ref, 'abort, 'i, 'o) function_body\<close>
      ["mut_ref_identity", "mut_ref_escape_control", "lifetime_ref_identity",
       "reserved_lifetime_identity", "typed_self_mut_ref", "typed_mut_self_mut_ref"]
    val _ = check
      \<^typ>\<open>('a, 'g, 8 word) Global_Store.ref option \<Rightarrow>
        ('a, 'g, ('a, 'g, 16 word) Global_Store.ref) Global_Store.ref \<Rightarrow>
        ('a, 'g, 8 word \<times> bool \<times> tnil) Global_Store.ref \<Rightarrow>
        ('a, 'g, 32 word) Global_Store.ref \<Rightarrow>
        ('a, 'g, 'x list) Global_Store.ref \<Rightarrow> 'x \<Rightarrow>
        ('s, ('a, 'g, 8 word) Global_Store.ref, 'abort, 'i, 'o) function_body\<close>
      ["mixed_reference_shapes"]
    val _ = check
      \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref \<Rightarrow>
        ('s, (nat, bool, 8 word) Global_Store.ref, 'abort, 'i, 'o) function_body\<close>
      ["reference_body_constraint"]
  in val _ = () end
\<close>

section\<open> Lifetime syntax, positions, markup and printing \<close>

ML\<open>
structure Parser_Reference_Type_Test =
struct
  open Parser_Function_Regression_Test

  fun nth_position text label needle occurrence =
    let
      fun skip 0 offset = token_position text (start label) needle offset
        | skip n offset = skip (n - 1) (find_from text needle offset + 1)
    in skip occurrence 0 end

  fun lifetime_name (URust_AST.Rust_Lifetime (name, _)) = name
  fun lifetime_position (URust_AST.Rust_Lifetime (_, pos)) = pos

  fun reference_lifetimes (URust_AST.Reference_Type (_, lifetime, typ, _)) =
        the_list lifetime @ reference_lifetimes typ
    | reference_lifetimes (URust_AST.Path_Type (segments, _)) =
        let
          fun argument (URust_AST.Rust_Type_Argument typ) = reference_lifetimes typ
            | argument _ = []
          fun segment (URust_AST.Rust_Type_Path_Segment (_, _, arguments, _)) =
            maps argument (the_default [] arguments)
        in maps segment segments end
    | reference_lifetimes _ = []

  val no_channels: URust_Type_Mappings.function_channels =
    {state = NONE, abort = NONE, input = NONE, output = NONE}

  fun resolve_function ctxt function =
    URust_Type_Mappings.resolve_function_signature ctxt no_channels
      (URust_AST.function_lifetime_parameters function)
      (map parameter_type (URust_AST.function_parameters function))
      (the_default
        (URust_AST.Primitive_Type (URust_AST.DPT_Unit, Position.none))
        (URust_AST.function_return_type function))
end
\<close>

ML_val\<open>
  local
    open Parser_Reference_Type_Test
    val ctxt = Context_Position.set_visible true \<^context>
    val label = "reference-lifetime-positions"
    (* An Isabelle symbol before the lifetimes makes byte-counted ranges fail. *)
    val text =
      "fn LifetimePositions<'a, 'b,>(/* \<alpha> */ left: &'a mut u8, \
      \right: &'b mut &'static mut u16, anonymous: &'_ mut u8) -> &'a mut u8 { left }"
    val (function, markup) = Parser_Test_Reports.markup (fn () => parse ctxt label text)
    val declared = URust_AST.function_lifetime_parameters function
    val used = maps reference_lifetimes (signature_types function)
    val _ = require "declared lifetime names changed"
      (map lifetime_name declared = ["'a", "'b"])
    val _ = require "reference lifetime names changed"
      (map lifetime_name used = ["'a", "'b", "'static", "'_", "'a"])
    val expected =
      [nth_position text label "'a" 0, nth_position text label "'b" 0,
       nth_position text label "'a" 1, nth_position text label "'b" 1,
       nth_position text label "'static" 0, nth_position text label "'_" 0,
       nth_position text label "'a" 2]
    val actual = map lifetime_position (declared @ used)
    val _ = require "lifetime positions are not exact symbol-counted token ranges"
      (map range_of actual = map range_of expected)
    val _ =
      List.app (fn position =>
        (require "lifetime lost its type-variable markup"
           (has_markup Markup.tfreeN position markup);
         require "lifetime lost its typing tooltip"
           (has_markup Markup.typingN position markup))) expected

    val printed = URust_Printer.string_of_function URust_Printer.serialized_options function
    (* The printer may break long signatures; compare with layout collapsed to single spaces. *)
    val compact = space_implode " " (String.tokens Char.isSpace printed)
    val _ = require ("printer dropped the lifetime parameter list: " ^ quote compact)
      (String.isSubstring "LifetimePositions<'a, 'b>(" compact)
    val _ = require ("printer dropped reference lifetimes: " ^ quote compact)
      (String.isSubstring "&'a mut u8" compact andalso
       String.isSubstring "&'b mut &'static mut u16" compact andalso
       String.isSubstring "&'_ mut u8" compact)
    val reparsed = parse ctxt (label ^ "-reparsed") printed
    val _ = require "lifetime parse-print-parse tokens changed"
      (URust_Printer.tokens_of_function URust_Printer.serialized_options function =
        URust_Printer.tokens_of_function URust_Printer.serialized_options reparsed)
    val _ = require "lifetimes changed the resolved signature"
      (Sign.typ_equiv (Proof_Context.theory_of ctxt)
        (resolve_function ctxt function,
         resolve_function ctxt
          (parse ctxt (label ^ "-erased")
            "fn LifetimePositions(left: &mut u8, right: &mut &mut u16, anonymous: &mut u8) \
            \-> &mut u8 { left }")))

    val shared = parse ctxt "reference-shared-parse" "fn Shared<'a>(value: &'a u8) -> u8 { 0 }"
    val _ = require "shared lifetime reference parsed with the wrong shape"
      (case signature_types shared of
         [URust_AST.Reference_Type (URust_AST.BM_Imm, SOME lifetime, _, _), _] =>
           lifetime_name lifetime = "'a"
       | _ => false)

    fun positioned_failure (label, text, needle, occurrence, expected) =
      let
        val result =
          Exn.result (fn () =>
            Navigation.capture (fn () => resolve_function ctxt (parse ctxt label text))) ()
        val diagnostic = message result
      in
        require (label ^ ": reason changed") (String.isSubstring expected diagnostic);
        require (label ^ ": diagnostic lost the exact lifetime range")
          (member (op =) (diagnostic_ranges diagnostic)
            (range_of (nth_position text label needle occurrence)))
      end
    val _ =
      List.app positioned_failure
        [("lifetime-position-undeclared",
          "fn Undeclared<'a>(/* \<alpha> */ value: &'b mut u8) { () }", "'b", 0,
          "undeclared lifetime \"'b\""),
         ("lifetime-position-duplicate-first",
          "fn Duplicate<'a, /* \<alpha> */ 'a>(value: &'a mut u8) { () }", "'a", 0,
          "duplicate lifetime parameter \"'a\""),
         ("lifetime-position-duplicate-second",
          "fn Duplicate<'a, /* \<alpha> */ 'a>(value: &'a mut u8) { () }", "'a", 1,
          "duplicate lifetime parameter \"'a\""),
         ("lifetime-position-static",
          "fn Reserved</* \<alpha> */ 'static>(value: u8) { () }", "'static", 0,
          "cannot be declared as a lifetime parameter"),
         ("lifetime-position-anonymous",
          "fn Reserved</* \<alpha> */ '_>(value: u8) { () }", "'_", 0,
          "cannot be declared as a lifetime parameter"),
         ("lifetime-position-shared",
          "fn Shared(/* \<alpha> */ value: &'static u8) { () }", "&'static u8", 0,
          "shared Rust references")]

    fun parser_failure (label, text, needle, expected) =
      let
        val diagnostic = message (Exn.result (fn () => parse ctxt label text) ())
      in
        require (label ^ ": reason changed") (String.isSubstring expected diagnostic);
        require (label ^ ": diagnostic lost the exact token range")
          (member (op =) (diagnostic_ranges diagnostic)
            (range_of (nth_position text label needle 0)))
      end
    val _ =
      List.app parser_failure
        [("lifetime-position-bound",
          "fn Bound<'a, /* \<alpha> */ 'b: 'a>(value: &'b mut u8) { () }", ":",
          "lifetime bounds are not supported"),
         ("lifetime-position-argument",
          "fn Argument(/* \<alpha> */ value: RefOption<'a>) { () }", "'a",
          "lifetime generic arguments are not supported")]
  in val _ = () end
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

adhoc_overloading store_reference_const \<rightleftharpoons> reference_test_allocate
adhoc_overloading store_dereference_const \<rightleftharpoons> reference_test_read
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

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun check expected names =
      List.app (fn name =>
        require (name ^ ": reference body scheme changed")
          (Sign.typ_equiv (Proof_Context.theory_of ctxt)
            (declared_type ctxt name, Logic.varifyT_global expected))) names
    val _ = check
      \<^typ>\<open>(unit, unit, 32 word) Global_Store.ref \<Rightarrow>
        (unit, 32 word, unit, unit, unit) function_body\<close>
      ["read_through", "read_through_control"]
    val _ = check
      \<^typ>\<open>(unit, unit, ref_counter) Global_Store.ref \<Rightarrow>
        (unit, 32 word, unit, unit, unit) function_body\<close>
      ["read_counter", "touch_counter", "touch_via_method"]
    val _ = check
      \<^typ>\<open>(unit, 32 word, unit, unit, unit) function_body\<close>
      ["bump_local", "chunk_caller", "bump_without_borrow"]
    val _ = require "method dispatch lost the typed reference receiver"
      (Term.exists_subterm
        (fn Const (name, _) => name = \<^const_name>\<open>touch_counter\<close> | _ => false)
        (rhs ctxt "touch_via_method"))
    val _ = require "borrowed local call lost its callee"
      (Term.exists_subterm
        (fn Const (name, _) => name = \<^const_name>\<open>increment_through\<close> | _ => false)
        (rhs ctxt "bump_local"))
  in val _ = () end
\<close>

section\<open> Rejections, rollback and recovery \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    val base = initial \<^theory>
    val recovery =
      command "" "reference_failure" "fn ReferenceRecovery(value: &mut u32) -> u32 { *value }"
    fun reject (label, expected, text) =
      let
        val (result, reports) = Parser_Test_Reports.markup (fn () =>
          Exn.capture (run_from base label) text)
        val diagnostic = message result
        val _ = require (label ^ ": wrong diagnostic " ^ quote diagnostic)
          (String.isSubstring expected diagnostic)
        val _ = require (label ^ ": no source position")
          (String.isSubstring label diagnostic andalso not (null (diagnostic_ranges diagnostic)))
        val _ = require (label ^ ": installed declaration markup")
          (null (declaration_definitions reports))
        val _ = require (label ^ ": mutated constant table")
          (constant_snapshot ctxt = constant_snapshot (Toplevel.context_of base))
        val _ = registry_unchanged label ctxt (Toplevel.context_of base)
        val recovered = run_from base (label ^ "-recovery") recovery |> Toplevel.context_of
        val _ = require (label ^ ": failed to recover a reference function")
          (binder_types (declared_type recovered "reference_failure") =
            [\<^typ>\<open>(unit, unit, 32 word) Global_Store.ref\<close>])
      in () end
    fun function label item = (label, command "" "reference_failure" item)
    fun reject_function (label, expected, item) = reject (label, expected, snd (function label item))
    val _ = List.app reject_function
      [("reference-shared-parameter", "shared Rust references",
        "fn BadReference(value: &u8) -> u8 { 0 }"),
       ("reference-shared-lifetime", "shared Rust references",
        "fn BadReference<'a>(value: &'a u8) -> u8 { 0 }"),
       ("reference-shared-result", "shared Rust references",
        "fn BadReference(value: u8) -> &u8 { \<llangle>undefined\<rrangle> }"),
       ("reference-shared-nested", "shared Rust references",
        "fn BadReference(value: &mut &u8) -> u8 { 0 }"),
       ("reference-shared-argument", "shared Rust references",
        "fn BadReference(value: RefOption<&u8>) -> u8 { 0 }"),
       ("reference-undeclared-lifetime", "undeclared lifetime \"'a\"",
        "fn BadReference(value: &'a mut u8) -> u8 { 0 }"),
       ("reference-undeclared-result-lifetime", "undeclared lifetime \"'b\"",
        "fn BadReference<'a>(value: &'a mut u8) -> &'b mut u8 { value }"),
       ("reference-duplicate-lifetime", "duplicate lifetime parameter \"'a\"",
        "fn BadReference<'a, 'a>(value: &'a mut u8) -> u8 { 0 }"),
       ("reference-declared-static", "cannot be declared as a lifetime parameter",
        "fn BadReference<'static>(value: u8) -> u8 { 0 }"),
       ("reference-declared-anonymous", "cannot be declared as a lifetime parameter",
        "fn BadReference<'_>(value: u8) -> u8 { 0 }"),
       ("reference-lifetime-bound", "lifetime bounds are not supported",
        "fn BadReference<'a, 'b: 'a>(value: &'b mut u8) -> u8 { 0 }"),
       ("reference-lifetime-argument", "lifetime generic arguments are not supported",
        "fn BadReference(value: RefOption<'a>) -> u8 { 0 }"),
       ("reference-mixed-generics", "syntax error",
        "fn BadReference<'a, T>(value: &'a mut u8) -> u8 { 0 }"),
       ("reference-empty-generics", "syntax error",
        "fn BadReference<>(value: u8) -> u8 { 0 }"),
       ("reference-lifetime-without-reference", "syntax error",
        "fn BadReference<'a>(value: 'a) -> u8 { 0 }"),
       ("reference-missing-target", "syntax error",
        "fn BadReference(value: &'a mut) -> u8 { 0 }"),
       ("reference-shorthand-receiver", "syntax error",
        "fn BadReference(&'a mut self) -> u8 { 0 }"),
       ("reference-body-apostrophe", "unexpected input",
        "fn BadReference(value: &mut u8) -> u8 { 'a }"),
       ("reference-reborrow", "Unresolved adhoc overloading of constant",
        "fn BadReference(value: &mut u32) { IncrementThrough(&mut *value) }"),
       ("reference-borrowed-literal", "Type unification failed",
        "fn BadReference() { IncrementThrough(&mut 5_u32) }")]
    val _ = List.app reject
      [("reference-datatype-field", "Rust reference types is not supported in datatype fields",
        "urust_datatype " ^ cartouche "struct BadReferenceField { value: &mut u8 }"),
       ("reference-datatype-lifetime-field",
        "Rust reference types is not supported in datatype fields",
        "urust_datatype " ^ cartouche "struct BadReferenceField { value: &'a mut u8 }"),
       ("reference-datatype-lifetime-parameter", "syntax error",
        "urust_datatype " ^ cartouche "struct BadReferenceField<'a> { value: u8 }"),
       ("reference-type-alias", "Rust reference types is not supported in type aliases",
        "urust_type_alias " ^ cartouche "type BadReferenceAlias = &'static mut u8;"),
       ("reference-cast-target", "Rust reference types is not supported in cast targets",
        "urust_expr bad_reference_cast " ^ cartouche "0_u8 as &mut u8"),
       ("reference-cast-lifetime", "unexpected input",
        "urust_expr bad_reference_cast " ^ cartouche "0_u8 as &'a mut u8"),
       ("reference-turbofish-lifetime", "unexpected input",
        "urust_expr bad_reference_turbofish " ^ cartouche "IncrementThrough::<'a>()")]
  in val _ = () end
\<close>

no_adhoc_overloading store_reference_const \<rightleftharpoons> reference_test_allocate
no_adhoc_overloading store_dereference_const \<rightleftharpoons> reference_test_read
no_adhoc_overloading store_update_const \<rightleftharpoons> reference_test_write

end
