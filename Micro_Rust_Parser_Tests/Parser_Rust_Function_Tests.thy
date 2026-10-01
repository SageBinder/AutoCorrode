theory Parser_Rust_Function_Tests
  imports Parser_Test_Utils
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open> Rust-shaped function items \<close>

urust_fn explicit_hol_name ::
  \<open>64 word \<Rightarrow> bool \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn RustAlias(x: u64, _: bool) -> u64 {
      x
    }
  \<close>

urust_fn ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  \<open>
    fn HTTPServer() {
      ()
    }
  \<close>

urust_fn _ ::
  \<open>64 word \<Rightarrow>
    (unit, bool, unit, unit, unit) function_body\<close>
  \<open>
    fn probe(x: u64) -> bool {
      x == 0
    }
  \<close>

ML_val\<open>
  if is_none (URust_Item_Scope.lookup_function \<^context> "probe")
  then ()
  else error "anonymous Rust function item was registered"
\<close>

urust_fn registered_probe ::
  \<open>64 word \<Rightarrow>
    (unit, bool, unit, unit, unit) function_body\<close>
  \<open>
    fn probe(x: u64) -> bool {
      x == 0
    }
  \<close>

urust_fn call_registered_probe ::
  \<open>64 word \<Rightarrow>
    (unit, bool, unit, unit, unit) function_body\<close>
  (x)
  \<open> probe(x) \<close>

urust_fn ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  \<open>
    fn HTTP2XMLParser() {
      ()
    }
  \<close>

urust_fn already_snake ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  \<open>
    fn already_snake() {
      ()
    }
  \<close>

ML_val\<open>
  List.app
    (fn (source, expected) =>
      let val actual = URust_AST.rust_snake_case source in
        if actual = expected then ()
        else
          error
            ("Rust function inferred-name conversion changed for " ^
              quote source ^ ": expected " ^ quote expected ^
              ", found " ^ quote actual)
      end)
    [("HTTPServer", "http_server"),
     ("HTTP2XMLParser", "http2_xml_parser"),
     ("XMLHttpRequest", "xml_http_request"),
     ("Already_snake", "already_snake"),
     ("_LeadingHTTP", "_leading_http"),
     ("parse2DValue", "parse2_d_value")]
\<close>

urust_fn rust_hol_disagreement ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn type_labels_are_documentary(x: bool) -> char {
      x + 1
    }
  \<close>

urust_fn mutable_parameter ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn MutableParameter(mut x: str) -> ! {
      x
    }
  \<close>

urust_fn mixed_parameter_slots ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> unit \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body\<close>
  \<open>
    fn MixedParameterSlots(
      first: u8,
      _: bool,
      mut retained: str,
      _: Outer::Ignored<u64>,
    ) -> u128 {
      retained
    }
  \<close>

urust_fn empty_block ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  \<open>
    fn EmptyBlock() {}
  \<close>

urust_fn commented_signature ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
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

urust_fn [abbrev] abbreviated_hol_name ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn AbbreviatedRustName(x: u128) -> i8 {
      x
    }
  \<close>

urust_fn call_abbreviated_rust_name ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  (x)
  \<open> AbbreviatedRustName(x) \<close>

urust_fn [application_def, attrs = [micro_rust_simps]]
  attributed_application_function ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn AttributedApplication(x: u64) -> u64 {
      x
    }
  \<close>

urust_fn rust_maximum_call_arity ::
  \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body
  \<close>
  \<open>
    fn RustMaximumCallArity(
      p01: u8, p02: u8, p03: u8, p04: u8,
      p05: u8, p06: u8, p07: u8, p08: u8,
      p09: u8, p10: u8, p11: u8, p12: u8,
      p13: u8, p14: u8,
    ) -> u8 {
      p14
    }
  \<close>

urust_fn invoke_rust_maximum_call_arity ::
  \<open>(unit, nat, unit, unit, unit) function_body\<close>
  \<open>
    fn InvokeRustMaximumCallArity() -> u8 {
      RustMaximumCallArity(
        1, 2, 3, 4, 5, 6, 7,
        8, 9, 10, 11, 12, 13, 14,
      )
    }
  \<close>

urust_fn
  [pp_test, pretty, verbosity = 2]
  configured_function ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn ConformanceFunction(x: u64) -> u64 {
      x
    }
  \<close>

urust_fn completed_result_type ::
  \<open>64 word \<Rightarrow> _\<close>
  \<open>
    fn CompletedResultType(x: u64,) -> u8 {
      x
    }
  \<close>

urust_fn omitted_rust_return_type ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn DocumentaryUnit(x: u64) {
      x
    }
  \<close>

urust_fn lexical_function_shadow ::
  \<open>
    (64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body) \<Rightarrow>
    64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body
  \<close>
  \<open>
    fn LexicalFunctionShadow(RustAlias: Handler, x: u64) -> u64 {
      RustAlias(x)
    }
  \<close>

urust_fn call_registered_function ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  (x)
  \<open> RustAlias(x, true) \<close>

urust_fn _ ::
  \<open>64 word \<Rightarrow> bool \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn RustAlias(x: u64, _: bool) -> u64 {
      x
    }
  \<close>

ML_val\<open>
  (case URust_Item_Scope.lookup_function \<^context> "RustAlias" of
     SOME entry =>
       if Term.aconv_untyped
           (URust_Item_Scope.function_term entry,
            Const (\<^const_name>\<open>explicit_hol_name\<close>, dummyT))
       then ()
       else error "anonymous duplicate Rust item replaced the registered function"
   | NONE => error "anonymous duplicate Rust item removed the registered function")
\<close>

urust_fn call_inferred_function ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> HTTPServer() \<close>

locale rust_function_item_locale =
  fixes offset :: nat
begin

urust_fn locale_scoped_function ::
  \<open>nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body\<close>
  \<open>
    fn LocaleScopedFunction(value: u64) -> u64 {
      \<llangle>value + offset\<rrangle>
    }
  \<close>

urust_fn locale_scoped_client ::
  \<open>nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body\<close>
  \<open>
    fn LocaleScopedClient(value: u64) -> u64 {
      LocaleScopedFunction(value)
    }
  \<close>

end

ML_val\<open>
  if is_none
      (URust_Item_Scope.lookup_function
        \<^context> "LocaleScopedFunction")
  then ()
  else error "locale-scoped Rust function registration leaked globally"
\<close>

urust_fn global_after_locale_scope ::
  \<open>nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body\<close>
  \<open>
    fn LocaleScopedFunction(value: u64) -> u64 {
      value
    }
  \<close>

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

ML_val\<open>
  let
    val ctxt = \<^context>
    val proposition =
      Thm.prop_of
        (Proof_Context.get_thm ctxt
          "invoke_rust_maximum_call_arity_def")
  in
    if Term.exists_subterm
        (fn Const (name, _) =>
              name = \<^const_name>\<open>funcall14\<close>
          | _ => false)
        proposition
    then ()
    else error "maximum-arity Rust function call did not lower through funcall14"
  end
\<close>

ML_val\<open>
  let
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val attributes =
      Named_Theorems.get ctxt
        \<^named_theorems>\<open>micro_rust_simps\<close>

    fun assert label condition =
      if condition then ()
      else error ("Rust function artifact audit: " ^ label)

    fun theorem name = Proof_Context.get_thm ctxt name

    fun has_theorem name =
      can (Proof_Context.get_thm ctxt) name

    fun equation name =
      theorem name |> Thm.prop_of |> Logic.dest_equals

    val (default_lhs, default_rhs) =
      equation "explicit_hol_name_def"
    val (application_lhs, _) =
      equation "attributed_application_function_def"

    val default_arguments = #2 (Term.strip_comb default_lhs)
    val application_arguments = #2 (Term.strip_comb application_lhs)

    val _ =
      assert "ordinary item definition no longer has a lambda-shaped rhs"
        (null default_arguments andalso
          length (binder_types (fastype_of default_rhs)) = 2)
    val _ =
      assert "application_def item did not move its argument to the lhs"
        (length application_arguments = 1)
    val _ =
      assert "abbreviation unexpectedly generated a definition theorem"
        (not (has_theorem "abbreviated_hol_name_def"))
    val _ =
      assert "attrs did not reach the Rust-item definition theorem"
        (exists
          (Thm.equiv_thm thy o
            pair (theorem "attributed_application_function_def"))
          attributes)
  in
    ()
  end
\<close>

thm rust_hol_disagreement_def
thm attributed_application_function_def
thm configured_function_def
thm http2_xml_parser_def
thm already_snake_def

urust_datatype shared_item \<open> struct SharedItem; \<close>

definition notation_function_target ::
    \<open>64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where
    \<open>notation_function_target =
      (\<lambda>x. FunctionBody (literal x))\<close>

urust_notation (call)
  notation_function_target ("NotationClash")

ML\<open>
local
  open URust_AST

  fun source label text =
    Parser_Lex_Util.positioned_content_source text
      (Position.line_file 1 label)

  fun parse label text =
    (case URust_Parser.parse_function_source \<^context>
        (source label text) of
       SOME function => function
     | NONE =>
         error
           ("Rust function source parsed as empty" ^
             Position.here (Position.file label)))

  fun assert label condition =
    if condition then ()
    else error ("Rust function AST audit: " ^ label)

  fun parameter_type
      (Function_Parameter (_, _, typ, _)) = typ

  fun serialized function =
    URust_Printer.string_of_function
      URust_Printer.serialized_options function

  fun assert_roundtrip label function =
    let
      val text = serialized function
      val reparsed = parse (label ^ "-reparsed") text
      val original_tokens =
        URust_Printer.tokens_of_function
          URust_Printer.serialized_options function
      val reparsed_tokens =
        URust_Printer.tokens_of_function
          URust_Printer.serialized_options reparsed
    in
      assert (label ^ " parse-print-parse tokens changed")
        (original_tokens = reparsed_tokens);
      text
    end

  val type_forms =
    parse "rust-function-type-forms"
      "fn Types(\
      \a: u8, b: i128, c: bool, d: char, e: &str, \
      \f: &mut [u64], g: *const Foo::Bar<Baz<u8>, 4>, \
      \h: *mut u16, i: [u8; 32], j: (u8, bool), \
      \k: (), l: !, m: u16, n: u32, o: u128, p: usize, \
      \q: i8, r: i16, s: i32, t: i64, u: isize) \
      \-> Outer::Result<Inner<u64>, 8> { a >> 1 }"

  val _ =
    (case map parameter_type (function_parameters type_forms) of
       [Primitive_Type (DPT_U8, _),
        Primitive_Type (DPT_I128, _),
        Primitive_Type (DPT_Bool, _),
        Primitive_Type (DPT_Char, _),
        Reference_Type
          (BM_Imm, Primitive_Type (DPT_Str, _), _),
        Reference_Type
          (BM_Mut,
           Slice_Type (Primitive_Type (DPT_U64, _), _), _),
        Raw_Pointer_Type
          (RPM_Const, Path_Type (_, _), _),
        Raw_Pointer_Type
          (RPM_Mut, Primitive_Type (DPT_U16, _), _),
        Array_Type
          (Primitive_Type (DPT_U8, _), array_length, _),
        Tuple_Type
          ([Primitive_Type (DPT_U8, _),
            Primitive_Type (DPT_Bool, _)], _),
        Primitive_Type (DPT_Unit, _),
        Primitive_Type (DPT_Never, _),
        Primitive_Type (DPT_U16, _),
        Primitive_Type (DPT_U32, _),
        Primitive_Type (DPT_U128, _),
        Primitive_Type (DPT_Usize, _),
        Primitive_Type (DPT_I8, _),
        Primitive_Type (DPT_I16, _),
        Primitive_Type (DPT_I32, _),
        Primitive_Type (DPT_I64, _),
        Primitive_Type (DPT_Isize, _)] =>
          assert "array length token changed"
            (integer_literal_lexeme array_length = "32")
     | _ => error "Rust function primitive/type-form AST changed")

  val type_forms_text =
    assert_roundtrip "rust-function-type-forms" type_forms

  val _ =
    assert "nested Rust generic types were not preserved"
      (String.isSubstring
        "Outer::Result<Inner<u64>, 8>" type_forms_text)
  val _ =
    assert "function-body shift tokenization changed"
      (String.isSubstring "a >> 1" type_forms_text)

  val edge_forms =
    parse "rust-function-edge-type-forms"
      "fn TypeEdges(\
      \group: (u8), singleton: (u8,), tuple: (u32, bool,), \
      \nested: &&mut [*const Foo::Bar<Baz<u8>, 4>], \
      \array: [u16; 0x20usize], \
      \path: Result<Outer<Inner<u64>>, 1_024usize,>,\
      \) -> (Result<u8, Error>,) { group }"

  val _ =
    (case map parameter_type (function_parameters edge_forms) of
       [Group_Type (Primitive_Type (DPT_U8, _), _),
        Tuple_Type ([Primitive_Type (DPT_U8, _)], _),
        Tuple_Type
          ([Primitive_Type (DPT_U32, _),
            Primitive_Type (DPT_Bool, _)], _),
        Reference_Type
          (BM_Imm,
           Reference_Type
             (BM_Mut,
              Slice_Type
                (Raw_Pointer_Type
                  (RPM_Const, Path_Type (_, _), _), _), _), _),
        Array_Type
          (Primitive_Type (DPT_U16, _), array_length, _),
        Path_Type (_, _)] =>
          assert "suffixed hexadecimal array length changed"
            (integer_literal_lexeme array_length = "0x20usize")
     | _ => error "Rust function edge type-form AST changed")

  val _ =
    (case function_return_type edge_forms of
       SOME (Tuple_Type ([Path_Type (_, _)], _)) => ()
     | _ => error "Rust function singleton-tuple return type changed")

  val edge_forms_text =
    assert_roundtrip "rust-function-edge-type-forms" edge_forms

  val _ =
    List.app
      (fn expected =>
        assert ("serialized edge type lost " ^ quote expected)
          (String.isSubstring expected edge_forms_text))
      ["(u8)", "(u8,)", "(u32, bool)",
       "Foo::Bar<Baz<u8>, 4>",
       "[u16; 0x20usize]",
       "Result<Outer<Inner<u64>>, 1_024usize>",
       "-> (Result<u8, Error>,)"]

  val layout_wrapped =
    parse "rust-function-leading-trailing-layout"
      ("/* leading /* nested */ layout */\n" ^
       "fn LayoutWrapped() {} // trailing layout\n")

  val _ =
    assert "leading/trailing layout changed the function name"
      (#1 (function_name layout_wrapped) = "LayoutWrapped")

  val layout_tokens =
    source_tokens (function_source_layout layout_wrapped)

  val _ =
    assert "function source layout lost structural delimiters"
      (length
        (filter
          (fn (Delimiter_Token _, _) => true
            | _ => false)
          layout_tokens) = 4)
in
end
\<close>

ML_val\<open>
local
  val ctxt = \<^context>
  val serial = Unsynchronized.ref 0

  fun source label text =
    Parser_Lex_Util.positioned_content_source text
      (Position.line_file 1 label)

  fun parse label text =
    URust_Parser.parse_function_source ctxt (source label text)

  fun recover () =
    let
      val index = !serial
      val _ = serial := index + 1
      val label =
        "rust-function-parser-recovery-" ^ string_of_int index
      val text =
        "fn ParserRecovery" ^ string_of_int index ^
          "(value: u64) -> u64 { value >> 1 }"
    in
      (case parse label text of
         SOME _ => ()
       | NONE =>
           error
             ("Rust function parser did not recover" ^
               Position.here (Position.file label)))
    end

  fun reject label expected text =
    (case Exn.result (parse label) text of
       Exn.Res _ =>
         error
           ("invalid Rust function item was accepted" ^
             Position.here (Position.file label))
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn in
             if String.isSubstring expected message andalso
                String.isSubstring label message
             then recover ()
             else
               error
                 ("unexpected Rust function parser diagnostic:\n" ^
                   message ^ "\nexpected: " ^ quote expected)
           end)

  val syntax_cases =
    [("rust-function-parser-empty", "syntax error", ""),
     ("rust-function-parser-expression", "syntax error", "value + 1"),
     ("rust-function-parser-missing-name", "syntax error",
       "fn (value: u64) -> u64 { value }"),
     ("rust-function-parser-qualified-name", "syntax error",
       "fn Module::qualified(value: u64) -> u64 { value }"),
     ("rust-function-parser-missing-left-paren", "syntax error",
       "fn MissingLeft value: u64) -> u64 { value }"),
     ("rust-function-parser-missing-right-paren", "syntax error",
       "fn MissingRight(value: u64 -> u64 { value }"),
     ("rust-function-parser-leading-comma", "syntax error",
       "fn LeadingComma(, value: u64) -> u64 { value }"),
     ("rust-function-parser-double-comma", "syntax error",
       "fn DoubleComma(value: u64,, other: u64) -> u64 { value }"),
     ("rust-function-parser-missing-colon", "syntax error",
       "fn MissingColon(value u64) -> u64 { value }"),
     ("rust-function-parser-missing-parameter-type", "syntax error",
       "fn MissingParameterType(value:) -> u64 { value }"),
     ("rust-function-parser-missing-return-type", "syntax error",
       "fn MissingReturnType(value: u64) -> { value }"),
     ("rust-function-parser-missing-body", "syntax error",
       "fn MissingBody(value: u64) -> u64"),
     ("rust-function-parser-bodyless", "syntax error",
       "fn Bodyless(value: u64) -> u64;"),
     ("rust-function-parser-unclosed-body", "syntax error",
       "fn UnclosedBody(value: u64) -> u64 { value"),
     ("rust-function-parser-extra-close", "syntax error",
       "fn ExtraClose(value: u64) -> u64 { value }}"),
     ("rust-function-parser-trailing-semicolon", "syntax error",
       "fn TrailingSemicolon(value: u64) -> u64 { value };"),
     ("rust-function-parser-two-items", "syntax error",
       "fn First() {} fn Second() {}"),
     ("rust-function-parser-visibility", "syntax error",
       "pub fn Visible(value: u64) -> u64 { value }"),
     ("rust-function-parser-scoped-visibility", "syntax error",
       "pub(crate) fn Scoped(value: u64) -> u64 { value }"),
     ("rust-function-parser-async", "syntax error",
       "async fn Async(value: u64) -> u64 { value }"),
     ("rust-function-parser-const", "syntax error",
       "const fn Constant(value: u64) -> u64 { value }"),
     ("rust-function-parser-unsafe", "syntax error",
       "unsafe fn Unsafe(value: u64) -> u64 { value }"),
     ("rust-function-parser-extern", "syntax error",
       "extern \"C\" fn External(value: u64) -> u64 { value }"),
     ("rust-function-parser-generics", "syntax error",
       "fn Generic<T>(value: T) -> T { value }"),
     ("rust-function-parser-where", "syntax error",
       "fn Where(value: u64) -> u64 where u64: Copy { value }"),
     ("rust-function-parser-variadic", "unexpected input",
       "fn Variadic(value: u64, ...) -> u64 { value }"),
     ("rust-function-parser-empty-generic", "syntax error",
       "fn EmptyGeneric(value: Vec<>) -> u64 { value }"),
     ("rust-function-parser-leading-generic-comma", "syntax error",
       "fn LeadingGenericComma(value: Vec<, u8>) -> u64 { value }"),
     ("rust-function-parser-double-generic-comma", "syntax error",
       "fn DoubleGenericComma(value: Vec<u8,, u16>) -> u64 { value }"),
     ("rust-function-parser-generic-expression", "unexpected input",
       "fn GenericExpression(value: Array<1 + 2>) -> u64 { value }"),
     ("rust-function-parser-excess-generic-close", "syntax error",
       "fn ExcessClose(value: Outer<Inner<u8>>>) -> u64 { value }"),
     ("rust-function-parser-leading-type-path", "syntax error",
       "fn LeadingTypePath(value: ::Module::Type) -> u64 { value }"),
     ("rust-function-parser-empty-slice", "syntax error",
       "fn EmptySlice(value: []) -> u64 { value }"),
     ("rust-function-parser-symbolic-array-length", "syntax error",
       "fn SymbolicArray(value: [u8; LENGTH]) -> u64 { value }"),
     ("rust-function-parser-array-length-expression", "unexpected input",
       "fn ArrayExpression(value: [u8; 1 + 2]) -> u64 { value }"),
     ("rust-function-parser-missing-array-length", "syntax error",
       "fn MissingArrayLength(value: [u8;]) -> u64 { value }"),
     ("rust-function-parser-negative-array-length", "unexpected input",
       "fn NegativeArrayLength(value: [u8; -1]) -> u64 { value }"),
     ("rust-function-parser-unqualified-raw-pointer", "syntax error",
       "fn RawPointer(value: *u8) -> u64 { value }"),
     ("rust-function-parser-bare-reference", "syntax error",
       "fn BareReference(value: &) -> u64 { value }"),
     ("rust-function-parser-reference-const", "syntax error",
       "fn ReferenceConst(value: &const u8) -> u64 { value }"),
     ("rust-function-parser-leading-tuple-comma", "syntax error",
       "fn LeadingTupleComma(value: (, u8)) -> u64 { value }"),
     ("rust-function-parser-missing-tuple-comma", "syntax error",
       "fn MissingTupleComma(value: (u8 bool)) -> u64 { value }")]

  val _ =
    List.app
      (fn (label, expected, text) =>
        reject label expected text)
      syntax_cases

  val _ =
    reject "rust-function-parser-datatype"
      "expected a complete function item"
      "struct NotAFunction;"
  val _ =
    reject "rust-function-parser-lifetime"
      "unexpected input"
      "fn Lifetime(value: &'a u64) -> u64 { value }"
  val _ =
    reject "rust-function-parser-unterminated-string"
      "malformed or unterminated string literal"
      "fn UnterminatedString(value: \"missing) -> u64 { value }"
  val _ =
    reject "rust-function-parser-unterminated-comment"
      "unterminated block comment"
      "fn UnterminatedComment(/* outer /* inner */ value: u64"
  val _ =
    reject "rust-function-parser-malformed-formal-comment"
      "opening cartouche expected after formal comment"
      "fn FormalComment(\<comment> value: u64) -> u64 { value }"
in
end
\<close>

ML_val\<open>
local
  val nullary_type =
    Symbol.open_ ^
      "(unit, unit, unit, unit, unit) function_body" ^
    Symbol.close
  val unary_type =
    Symbol.open_ ^
      "64 word \<Rightarrow> " ^
      "(unit, 64 word, unit, unit, unit) function_body" ^
    Symbol.close
  val binary_type =
    Symbol.open_ ^
      "64 word \<Rightarrow> 64 word \<Rightarrow> " ^
      "(unit, 64 word, unit, unit, unit) function_body" ^
    Symbol.close
  val ternary_type =
    Symbol.open_ ^
      "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> " ^
      "(unit, 64 word, unit, unit, unit) function_body" ^
    Symbol.close
  val pure_unary_type =
    Symbol.open_ ^ "64 word \<Rightarrow> 64 word" ^ Symbol.close
  val source_open = Symbol.open_
  val source_close = Symbol.close
  val serial = Unsynchronized.ref 0

  fun cartouche text = source_open ^ text ^ source_close

  fun command name typ item =
    "urust_fn " ^ name ^ " :: " ^ typ ^ " " ^
      cartouche item

  fun run source_name text () =
    let
      val thy = \<^theory>
      val transitions =
        Outer_Syntax.parse_text thy (K thy)
          (Position.line_file 1 source_name) text
    in
      fold (Toplevel.command_exception true) transitions
        (Toplevel.make_state (SOME thy))
    end

  fun recover () =
    let
      val index = !serial
      val _ = serial := index + 1
    in
      ignore
        (run ("rust-function-recovery-" ^ string_of_int index)
          (command
            ("rust_function_recovery_" ^ string_of_int index)
            unary_type
            ("fn Recovery" ^ string_of_int index ^
              "(x: u64) -> u64 { x }")) ())
    end

  fun reject label expected text =
    (case Exn.result (run label text) () of
       Exn.Res _ =>
         error ("invalid Rust function command was accepted" ^
           Position.here (Position.file label))
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn in
             if String.isSubstring expected message andalso
                String.isSubstring label message
             then recover ()
             else
               error
                 ("unexpected Rust function diagnostic:\n" ^ message ^
                   "\nexpected: " ^ quote expected)
           end)

  val _ =
    List.app
      (fn (label, pattern, body) =>
        reject label "unsupported function parameter pattern"
          (command "unsupported_parameter_pattern" unary_type
            ("fn UnsupportedParameterPattern(" ^ pattern ^
              ": PatternType) -> u64 { " ^ body ^ " }")))
      [("rust-function-group-pattern", "(x)", "x"),
       ("rust-function-tuple-pattern", "(x, y)", "x"),
       ("rust-function-constructor-pattern", "Some(x)", "x"),
       ("rust-function-borrow-pattern", "&x", "x"),
       ("rust-function-alias-pattern", "x @ _", "x"),
       ("rust-function-literal-pattern", "0", "0"),
       ("rust-function-range-pattern", "0..=1", "0"),
       ("rust-function-slice-pattern", "[x]", "x"),
       ("rust-function-struct-pattern", "Pair { left: x }", "x"),
       ("rust-function-or-pattern", "x | y", "x"),
       ("rust-function-qualified-pattern", "Module::VALUE", "0")]
  val _ =
    reject "rust-function-mut-wildcard"
      "unsupported function parameter pattern"
      (command "mut_wildcard" unary_type
        "fn MutWildcard(mut _: u64) -> u64 { 0 }")
  val _ =
    reject "rust-function-mut-destructuring"
      "unsupported function parameter pattern"
      (command "mut_destructuring" unary_type
        "fn MutDestructuring(mut (x, y): Pair) -> u64 { x }")
  val _ =
    reject "rust-function-duplicate-parameter"
      "duplicate parameter \"x\""
      (command "duplicate_parameter" binary_type
        "fn DuplicateParameter(x: u64, x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-duplicate-parameter-around-wildcard"
      "duplicate parameter \"x\""
      (command "duplicate_parameter_around_wildcard" ternary_type
        "fn DuplicateAroundWildcard(x: u64, _: u64, x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-too-many-parameters"
      "declared type expects 1 parameter"
      (command "too_many_parameters" unary_type
        "fn ParameterCount(x: u64, y: u64) -> u64 { x }")
  val _ =
    reject "rust-function-too-few-parameters"
      "declared type expects 2 parameters"
      (command "too_few_parameters" binary_type
        "fn TooFewParameters(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-parameter-for-nullary-type"
      "declared type expects 0 parameters"
      (command "parameter_for_nullary_type" nullary_type
        "fn ParameterForNullaryType(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-receiver"
      "receiver parameters are not supported"
      (command "receiver_parameter" unary_type
        "fn Receiver(self: u64) -> u64 { self }")
  val _ =
    reject "rust-function-mutable-receiver"
      "receiver parameters are not supported"
      (command "mutable_receiver_parameter" unary_type
        "fn MutableReceiver(mut self: u64) -> u64 { self }")
  val _ =
    reject "rust-function-borrowed-receiver"
      "unsupported function parameter pattern"
      (command "borrowed_receiver_parameter" unary_type
        "fn BorrowedReceiver(&self: &u64) -> u64 { self }")
  val _ =
    reject "rust-function-missing-hol-type"
      "function elaboration requires a declared type"
      ("urust_fn missing_hol_type " ^
        cartouche "fn MissingHOLType() {}")
  val _ =
    reject "rust-function-wrong-hol-terminal"
      "declared result type must be function_body"
      (command "wrong_hol_terminal" pure_unary_type
        "fn WrongHOLTerminal(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-inferred-legacy-target"
      "legacy body syntax requires an explicit HOL declaration target"
      ("urust_fn :: " ^ nullary_type ^ " () " ^ cartouche "()")
  val _ =
    reject "rust-function-explicit-empty-clause-selects-legacy"
      "function declarations are not expressions"
      ("urust_fn legacy_mode_item :: " ^ nullary_type ^ " () " ^
        cartouche "fn LegacyModeItem() {}")
  val _ =
    reject "rust-function-item-mode-requires-item"
      "syntax error"
      (command "item_mode_expression" unary_type "x")
  val _ =
    reject "rust-function-anonymous-attributes"
      "attrs is not supported for anonymous declarations"
      ("urust_fn [attrs = []] _ :: " ^ unary_type ^ " " ^
        cartouche "fn AnonymousAttributes(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-abbreviation-attributes"
      "attrs is not supported in abbreviation mode"
      ("urust_fn [abbrev, attrs = []] abbreviation_attributes :: " ^
        unary_type ^ " " ^
        cartouche "fn AbbreviationAttributes(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-abbreviation-application"
      "abbreviation mode cannot be combined with `application_def`"
      ("urust_fn [abbrev, application_def] abbreviation_application :: " ^
        unary_type ^ " " ^
        cartouche "fn AbbreviationApplication(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-unknown-option"
      "unknown uRust command option"
      ("urust_fn [future_option] unknown_option :: " ^ unary_type ^ " " ^
        cartouche "fn UnknownOption(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-duplicate-option"
      "duplicate uRust command option"
      ("urust_fn [pp_test, pp_test = false] duplicate_option :: " ^
        unary_type ^ " " ^
        cartouche "fn DuplicateOption(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-invalid-boolean-option"
      "expects true or false"
      ("urust_fn [abbrev = 1] invalid_boolean_option :: " ^
        unary_type ^ " " ^
        cartouche "fn InvalidBooleanOption(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-invalid-verbosity"
      "must be 0, 1, or 2"
      ("urust_fn [verbosity = 3] invalid_verbosity :: " ^
        unary_type ^ " " ^
        cartouche "fn InvalidVerbosity(x: u64) -> u64 { x }")
  val _ =
    List.app
      (fn (label, expected, item) =>
        reject label expected
          (command "invalid_function_item" unary_type item))
      [("rust-function-visibility", "syntax error",
         "pub fn Visible(x: u64) -> u64 { x }"),
       ("rust-function-qualifier", "syntax error",
         "unsafe fn Qualified(x: u64) -> u64 { x }"),
       ("rust-function-generics", "syntax error",
         "fn Generic<T>(x: T) -> T { x }"),
       ("rust-function-where", "syntax error",
         "fn WhereClause(x: u64) -> u64 where X: Y { x }"),
       ("rust-function-bodyless", "syntax error",
         "fn Bodyless(x: u64) -> u64;"),
       ("rust-function-malformed-type", "syntax error",
         "fn Malformed(x: &mut) -> u64 { x }"),
       ("rust-function-lifetime", "unexpected input",
         "fn Lifetime(x: &'a u64) -> u64 { x }"),
       ("rust-function-function-pointer", "syntax error",
         "fn Pointer(x: fn(u64) -> u64) -> u64 { x }"),
       ("rust-function-associated-binding", "unexpected input",
         "fn Associated(x: Iterator<Item = u8>) -> u64 { 0 }"),
       ("rust-function-impl-type", "syntax error",
         "fn ImplType(x: impl Iterator) -> u64 { 0 }"),
       ("rust-function-dyn-type", "syntax error",
         "fn DynType(x: dyn Iterator) -> u64 { 0 }")]
  val _ =
    reject "rust-function-trailing-input"
      "syntax error"
      (command "trailing_input" unary_type
        "fn TrailingInput(x: u64) -> u64 { x } ignored")
  val _ =
    reject "rust-function-call-over-maximum-arity"
      "unsupported call arity 15 (max 14"
      (command "call_over_maximum_arity" nullary_type
        ("fn CallOverMaximumArity() -> u8 { " ^
          "RustMaximumCallArity(" ^
          "1, 2, 3, 4, 5, 6, 7, 8, " ^
          "9, 10, 11, 12, 13, 14, 15) }"))
  val _ =
    reject "rust-function-forward-reference"
      "unresolved body name \"LaterFunction\""
      (command "forward_reference" unary_type
        "fn ForwardReference(x: u64) -> u64 { LaterFunction(x) }")
  val _ =
    reject "rust-function-item-as-value"
      "unresolved body name \"RustMaximumCallArity\""
      (command "function_item_as_value" nullary_type
        "fn FunctionItemAsValue() -> u8 { RustMaximumCallArity }")
  val _ =
    reject "rust-function-existing-function"
      "already owned by a Rust function item"
      (command "duplicate_rust_function" unary_type
        "fn RustAlias(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-existing-constructor"
      "already owned by a Rust constructor item"
      (command "constructor_conflict" unary_type
        "fn SharedItem(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-existing-notation"
      "conflicts with an existing micro_rust_notation"
      (command "notation_conflict" unary_type
        "fn NotationClash(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-recursive-definition"
      "RecursiveFunction"
      (command "recursive_function" unary_type
        "fn RecursiveFunction(x: u64) -> u64 { RecursiveFunction(x) }")
  val _ =
    reject "rust-function-inferred-hol-name-collision"
      "Duplicate constant"
      ("urust_fn :: " ^ nullary_type ^ " " ^
        cartouche "fn Http2XMLParser() {}")
  val _ =
    reject "rust-function-explicit-hol-name-collision"
      "Duplicate constant"
      (command "empty_block" nullary_type
        "fn DistinctRustName() {}")
in
end
\<close>

ML_val\<open>
local
  structure I = URust_Item_Scope
  val ctxt = Context_Position.set_visible true \<^context>

  fun capture label action =
    let
      val reports =
        Synchronized.var
          ("rust_function_reports_" ^ label) ([]: string list)
      val result =
        Parser_Test_Report_Lock.run (fn () =>
          Unsynchronized.setmp Private_Output.report_fn
            (fn chunks =>
              Synchronized.change reports (append chunks))
            (fn () =>
              Print_Mode.with_modes [Print_Mode.PIDE]
                (fn () => Exn.result action ()) ())
            ())
    in (result, Synchronized.value reports) end

  fun collect (XML.Text _) result = result
    | collect (XML.Elem (markup, body)) result =
        fold collect body (markup :: result)

  fun markups chunks =
    fold collect (maps YXML.parse_body chunks) []

  fun find_from text needle offset =
    if offset + size needle > size text then
      error ("function markup audit: missing " ^ quote needle)
    else if String.substring (text, offset, size needle) = needle then
      offset
    else find_from text needle (offset + 1)

  fun position_at source_start text needle offset =
    let
      val raw = find_from text needle offset
      val start =
        Position.symbol_explode
          (String.substring (text, 0, raw)) source_start
    in
      (raw,
       Position.range_position
         (Position.range
           (start, Position.symbol_explode needle start)))
    end

  fun has_position properties position =
    Properties.get properties Markup.offsetN =
      Option.map Value.print_int (Position.offset_of position) andalso
    Properties.get properties Markup.end_offsetN =
      Option.map Value.print_int (Position.end_offset_of position) andalso
    Properties.get properties Markup.idN =
      Position.id_of position

  fun has_markup markup_name position markup =
    exists
      (fn (name, properties) =>
        name = markup_name andalso
          has_position properties position)
      markup

  fun has_function_entity property position markup =
    exists
      (fn (name, properties) =>
        name = Markup.entityN andalso
          Properties.get properties Markup.kindN =
            SOME "urust_function" andalso
          is_some (Properties.get properties property) andalso
          has_position properties position)
      markup

  val SOME entry = I.lookup_function ctxt "RustAlias"
  val (definition_result, definition_chunks) =
    capture "definition"
      (fn () => I.report_function_definition entry)
  val _ =
    (case definition_result of
       Exn.Res _ => ()
     | Exn.Exn exn => Exn.reraise exn)
  val _ =
    if has_function_entity Markup.defN
         (I.function_position entry) (markups definition_chunks)
    then ()
    else error "function item definition navigation changed"

  val success_start =
    Position.make0 1 1 0 "" "" "rust-function-navigation"
  val success_text = "RustAlias(1u64, true)"
  val success_source =
    Parser_Lex_Util.positioned_content_source
      success_text success_start
  val (_, success_reference_pos) =
    position_at success_start success_text "RustAlias" 0
  val (successful, success_chunks) =
    capture "reference"
      (fn () =>
        URust_Command.elaborate ctxt
          {kind = URust_Command.Function,
           source = success_source,
           arguments = [],
           arguments_pos = success_start,
           declared_type =
             SOME
               ("(unit, 64 word, unit, unit, unit) function_body",
                Position.none)})
  val _ =
    (case successful of
       Exn.Res _ => ()
     | Exn.Exn exn => Exn.reraise exn)
  val _ =
    if has_function_entity Markup.refN
         success_reference_pos (markups success_chunks)
    then ()
    else error "function item reference navigation changed"

  val signature_start =
    Position.make0 1 1 0 "" ""
      "rust-function-signature-markup"
  val signature_text =
    "fn SignatureMarkup(mut x: &mut [Outer::Inner<u8, 4>], \
    \_: *const str,) -> (bool,) { x }"
  val signature_source =
    Parser_Lex_Util.positioned_content_source
      signature_text signature_start
  val (fn_offset, fn_pos) =
    position_at signature_start signature_text "fn" 0
  val (first_mut_offset, first_mut_pos) =
    position_at signature_start signature_text "mut"
      (fn_offset + size "fn")
  val (first_colon_offset, first_colon_pos) =
    position_at signature_start signature_text ":"
      (first_mut_offset + size "mut")
  val (amp_offset, amp_pos) =
    position_at signature_start signature_text "&"
      (first_colon_offset + 1)
  val (second_mut_offset, second_mut_pos) =
    position_at signature_start signature_text "mut"
      (amp_offset + 1)
  val (left_bracket_offset, left_bracket_pos) =
    position_at signature_start signature_text "["
      (second_mut_offset + size "mut")
  val (path_separator_offset, path_separator_pos) =
    position_at signature_start signature_text "::"
      (left_bracket_offset + 1)
  val (generic_open_offset, generic_open_pos) =
    position_at signature_start signature_text "<"
      (path_separator_offset + size "::")
  val (u8_offset, u8_pos) =
    position_at signature_start signature_text "u8"
      (generic_open_offset + 1)
  val (numeric_offset, numeric_pos) =
    position_at signature_start signature_text "4"
      (u8_offset + size "u8")
  val (generic_close_offset, generic_close_pos) =
    position_at signature_start signature_text ">"
      (numeric_offset + 1)
  val (right_bracket_offset, right_bracket_pos) =
    position_at signature_start signature_text "]"
      (generic_close_offset + 1)
  val (star_offset, star_pos) =
    position_at signature_start signature_text "*"
      (right_bracket_offset + 1)
  val (const_offset, const_pos) =
    position_at signature_start signature_text "const"
      (star_offset + 1)
  val (str_offset, str_pos) =
    position_at signature_start signature_text "str"
      (const_offset + size "const")
  val (arrow_offset, arrow_pos) =
    position_at signature_start signature_text "->"
      (str_offset + size "str")
  val (bool_offset, bool_pos) =
    position_at signature_start signature_text "bool"
      (arrow_offset + size "->")
  val (_, body_open_pos) =
    position_at signature_start signature_text "{"
      (bool_offset + size "bool")
  val (signature_result, signature_chunks) =
    capture "signature"
      (fn () =>
        ignore
          (URust_Parser.parse_function_source
            ctxt signature_source))
  val _ =
    (case signature_result of
       Exn.Res _ => ()
     | Exn.Exn exn => Exn.reraise exn)
  val signature_markup = markups signature_chunks
  val _ =
    if List.all
         (fn pos => has_markup Markup.keyword1N pos signature_markup)
         [fn_pos, first_mut_pos, second_mut_pos,
          u8_pos, const_pos, str_pos, bool_pos] andalso
       List.all
         (fn pos => has_markup Markup.operatorN pos signature_markup)
         [amp_pos, star_pos] andalso
       List.all
         (fn pos => has_markup Markup.delimiterN pos signature_markup)
         [first_colon_pos, left_bracket_pos, path_separator_pos,
          generic_open_pos, generic_close_pos, right_bracket_pos,
          arrow_pos, body_open_pos] andalso
       has_markup Markup.numeralN numeric_pos signature_markup
    then ()
    else error "function signature lexical markup changed"

  val failed_start =
    Position.make0 1 1 0 "" ""
      "rust-function-failed-navigation"
  val failed_text = "RustAlias(true, true)"
  val failed_source =
    Parser_Lex_Util.positioned_content_source
      failed_text failed_start
  val (_, failed_reference_pos) =
    position_at failed_start failed_text "RustAlias" 0
  val (failed, failed_chunks) =
    capture "failed-reference"
      (fn () =>
        URust_Command.elaborate ctxt
          {kind = URust_Command.Function,
           source = failed_source,
           arguments = [],
           arguments_pos = failed_start,
           declared_type =
             SOME
               ("(unit, 64 word, unit, unit, unit) function_body",
                Position.none)})
  val _ =
    (case failed of
       Exn.Res _ =>
         error "ill-typed function-item call unexpectedly succeeded"
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn else ())
  val _ =
    if has_function_entity Markup.refN failed_reference_pos
         (markups failed_chunks)
    then
      error "failed function declaration leaked an item reference"
    else ()
in
end
\<close>

end
