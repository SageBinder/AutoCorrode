(* ML audits for urust_fn declarations; the readable examples are in Parser_Function_Examples. *)

theory Parser_Function_ML_Tests
  imports
    Parser_Function_Examples
    Parser_Test_Fixtures_Left
    Parser_Test_Fixtures_Right
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
begin

declare [[urust_pp_test = true, urust_pretty = false, urust_verbosity = 0, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

text\<open>
This theory checks the declarations in Parser_Function_Examples and runs isolated negative commands.
Its ML fixtures are test infrastructure; the imported function theory presents the public syntax
through ordinary declarations.
\<close>

chapter\<open> Function items, artifacts and parser recovery \<close>

section\<open> Name conversion and registration scope \<close>

ML_val\<open>
  let
    val ctxt = \<^context>
    fun require label condition =
      if condition then ()
      else error ("function registration example: " ^ label)

    fun registered (rust_name, hol_name) =
      (case Parser_Test_Calls.lookup ctxt rust_name of
         SOME entry =>
           require (rust_name ^ " selected the wrong HOL artifact")
             (Term.aconv_untyped
               ((fn (entry: Micro_Rust_Names.entry) => #hol_term entry) entry, Const (hol_name, dummyT)))
       | NONE => error ("function example did not register " ^ quote rust_name))

    val _ =
      List.app registered
        [("BareRegistered", \<^const_name>\<open>bare_registered\<close>),
         ("ExplicitlyRegistered", \<^const_name>\<open>explicitly_registered\<close>),
         ("ScopedRegisteredOverride", \<^const_name>\<open>scoped_registered_override\<close>),
         ("SignaturePrimitive", \<^const_name>\<open>signature_primitive\<close>)]
    val _ =
      List.app
        (fn name => require (name ^ " unexpectedly registered")
          (is_none (Parser_Test_Calls.lookup ctxt name)))
        ["UnregisteredHelper", "ScopedUnregisteredHelper"]
  in
    ()
  end
\<close>

ML_val\<open>
  if is_none (Parser_Test_Calls.lookup \<^context> "AnonymousProbe")
  then ()
  else error "anonymous Rust function item was registered"
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

ML_val\<open>
  (case Parser_Test_Calls.lookup \<^context> "RustAlias" of
     SOME entry =>
       if Term.aconv_untyped
           ((fn (entry: Micro_Rust_Names.entry) => #hol_term entry) entry,
            Const (\<^const_name>\<open>explicit_hol_name\<close>, dummyT))
       then ()
       else error "anonymous duplicate Rust item replaced the registered function"
   | NONE => error "anonymous duplicate Rust item removed the registered function")
\<close>

ML_val\<open>
  (case Parser_Test_Calls.lookup \<^context> "LocaleScopedFunction" of
     SOME entry =>
       if Term.aconv_untyped
           ((fn (entry: Micro_Rust_Names.entry) => #hol_term entry) entry,
            Const (\<^const_name>\<open>global_after_locale_scope\<close>, dummyT))
       then ()
       else error "locale-scoped Rust function registration leaked globally"
   | NONE => error "global declaration after locale scope was not registered");
  if is_none (Parser_Test_Calls.lookup \<^context> "LocaleScopedClient")
  then ()
  else error "locale-scoped Rust client registration leaked globally"
\<close>

section\<open> Generated equations and declaration artifacts \<close>

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

section\<open> AST structure and signature printer roundtrips \<close>

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
          (BM_Imm, NONE, Primitive_Type (DPT_Str, _), _),
        Reference_Type
          (BM_Mut, NONE,
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
          (BM_Imm, NONE,
           Reference_Type
             (BM_Mut, NONE,
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

  val symbolic_array =
    parse "rust-function-parser-symbolic-array-length"
      "fn SymbolicArray(value: [u8; LENGTH]) -> u64 { value }"
  val _ =
    (case map parameter_type (function_parameters symbolic_array) of
       [Const_Array_Type (Primitive_Type (DPT_U8, _),
          Path_Type ([Rust_Type_Path_Segment ("LENGTH", _, NONE, _)], _), _)] => ()
     | _ => error "symbolic array type AST changed")
  val _ = ignore (assert_roundtrip "rust-function-symbolic-array" symbolic_array)
in
end
\<close>

section\<open> Invalid item grammar and parser recovery \<close>

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
  val _ = ignore (parse "rust-function-parser-where-retained"
    "fn Where(value: u64) -> u64 where u64: Copy { value }")

  val _ =
    reject "rust-function-parser-datatype"
      "expected a complete function item"
      "struct NotAFunction;"
  val _ =
    reject "rust-function-parser-body-apostrophe"
      "unexpected input"
      "fn BodyApostrophe(value: u64) -> u64 { 'a }"
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

section\<open> Invalid declarations, callable conflicts and recovery \<close>

ML_val\<open>
local
  val source_open = Symbol.open_
  val source_close = Symbol.close
  val serial = Unsynchronized.ref 0

  fun cartouche text = source_open ^ text ^ source_close

  fun command name item =
    "urust_fn " ^ name ^ " " ^ cartouche item

  (* Imported constants may be shadowed by a new theory. Create the occupied
     binding in this probe's namespace before testing same-owner rejection. *)
  fun occupied_hol_name name =
    "definition " ^ name ^ " where " ^
      cartouche (name ^ " = ()") ^ "\n"

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
          (command "unsupported_parameter_pattern"
            ("fn UnsupportedParameterPattern(" ^ pattern ^
              ": u64) -> u64 { " ^ body ^ " }")))
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
      (command "mut_wildcard"
        "fn MutWildcard(mut _: u64) -> u64 { 0 }")
  val _ =
    reject "rust-function-mut-destructuring"
      "unsupported function parameter pattern"
      (command "mut_destructuring"
        "fn MutDestructuring(mut (x, y): u64) -> u64 { x }")
  val _ =
    reject "rust-function-duplicate-parameter"
      "duplicate parameter \"x\""
      (command "duplicate_parameter"
        "fn DuplicateParameter(x: u64, x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-duplicate-parameter-around-wildcard"
      "duplicate parameter \"x\""
      (command "duplicate_parameter_around_wildcard"
        "fn DuplicateAroundWildcard(x: u64, _: u64, x: u64) -> u64 { x }")
  val _ =
    ignore
      (run "rust-function-signature-controls-two-parameters"
        (command "signature_two_parameters"
          "fn ParameterCount(x: u64, y: u64) -> u64 { x }") ())
  val _ =
    ignore
      (run "rust-function-signature-controls-one-parameter"
        (command "signature_one_parameter"
          "fn OneParameter(x: u64) -> u64 { x }") ())
  val _ =
    ignore
      (run "rust-function-signature-controls-zero-parameters"
        (command "signature_zero_parameters"
          "fn ZeroParameters() -> u64 { 0 }") ())
  val _ =
    ignore
      (run "rust-function-typed-receiver"
        (command "receiver_parameter"
          "fn Receiver(self: u64) -> u64 { self }") ())
  val _ =
    ignore
      (run "rust-function-mutable-typed-receiver"
        (command "mutable_receiver_parameter"
          "fn MutableReceiver(mut self: u64) -> u64 { self }") ())
  val _ =
    reject "rust-function-borrowed-receiver"
      "unsupported function parameter pattern"
      (command "borrowed_receiver_parameter"
        "fn BorrowedReceiver(&self: &u64) -> u64 { self }")
  val _ =
    ignore
      (run "rust-function-no-outer-hol-type"
        ("urust_fn inferred_hol_type " ^
          cartouche "fn InferredHOLType() {}") ())
  val _ =
    ignore
      (run "rust-function-signature-supplies-result-type"
        (command "signature_result_type"
          "fn SignatureResultType(x: u64) -> u64 { x }") ())
  val _ =
    reject "rust-function-forbidden-outer-hol-type"
      "Outer syntax error"
      ("urust_fn :: " ^ cartouche "unit" ^ " () " ^ cartouche "()")
  val _ =
    reject "rust-function-forbidden-outer-parameter-clause"
      "Outer syntax error"
      ("urust_fn legacy_mode_item () " ^
        cartouche "fn LegacyModeItem() {}")
  val _ =
    reject "rust-function-item-mode-requires-item"
      "syntax error"
      (command "item_mode_expression" "x")
  val _ =
    reject "rust-function-anonymous-attributes"
      "attrs is not supported for anonymous declarations"
      ("urust_fn [attrs = []] _ " ^
        cartouche "fn AnonymousAttributes(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-abbreviation-attributes"
      "attrs is not supported in abbreviation mode"
      ("urust_fn [abbrev, attrs = []] abbreviation_attributes " ^
        cartouche "fn AbbreviationAttributes(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-abbreviation-application"
      "abbreviation mode cannot be combined with `application_def`"
      ("urust_fn [abbrev, application_def] abbreviation_application " ^
        cartouche "fn AbbreviationApplication(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-unknown-option"
      "unknown uRust command option"
      ("urust_fn [future_option] unknown_option " ^
        cartouche "fn UnknownOption(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-duplicate-option"
      "duplicate uRust command option"
      ("urust_fn [pp_test, pp_test = false] duplicate_option " ^
        cartouche "fn DuplicateOption(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-invalid-boolean-option"
      "expects true or false"
      ("urust_fn [abbrev = 1] invalid_boolean_option " ^
        cartouche "fn InvalidBooleanOption(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-invalid-verbosity"
      "must be 0, 1, or 2"
      ("urust_fn [verbosity = 3] invalid_verbosity " ^
        cartouche "fn InvalidVerbosity(x: u64) -> u64 { x }")
  val _ =
    List.app
      (fn (label, expected, item) =>
        reject label expected
          (command "invalid_function_item" item))
      [("rust-function-visibility", "syntax error",
         "pub fn Visible(x: u64) -> u64 { x }"),
       ("rust-function-qualifier", "syntax error",
         "unsafe fn Qualified(x: u64) -> u64 { x }"),
       ("rust-function-where", "where clauses may only bound this function's type parameters",
         "fn WhereClause(x: u64) -> u64 where X: Y { x }"),
       ("rust-function-bodyless", "syntax error",
         "fn Bodyless(x: u64) -> u64;"),
       ("rust-function-malformed-type", "syntax error",
         "fn Malformed(x: &mut) -> u64 { x }"),
       ("rust-function-lifetime", "undeclared lifetime \"'a\"",
         "fn Lifetime(x: &'a mut u64) -> u64 { 0 }"),
       ("rust-function-function-pointer", "Rust function pointer types",
         "fn Pointer(x: fn(u64) -> u64) -> u64 { x }"),
       ("rust-function-associated-binding", "associated type bindings",
         "fn Associated(x: Iterator<Item = u8>) -> u64 { 0 }"),
       ("rust-function-impl-type", "Rust impl Trait types",
         "fn ImplType(x: impl Iterator) -> u64 { 0 }"),
       ("rust-function-dyn-type", "syntax error",
         "fn DynType(x: dyn Iterator) -> u64 { 0 }")]
  val _ =
    reject "rust-function-trailing-input"
      "syntax error"
      (command "trailing_input"
        "fn TrailingInput(x: u64) -> u64 { x } ignored")
  val _ =
    reject "rust-function-call-over-maximum-arity"
      "unsupported call arity 15 (max 14"
      (command "call_over_maximum_arity"
        ("fn CallOverMaximumArity() -> u8 { " ^
          "RustMaximumCallArity(" ^
          "1, 2, 3, 4, 5, 6, 7, 8, " ^
          "9, 10, 11, 12, 13, 14, 15) }"))
  val _ =
    reject "rust-function-forward-reference"
      "unresolved body name \"LaterFunction\""
      (command "forward_reference"
        "fn RejectedForwardReference(x: u64) -> u64 { LaterFunction(x) }")
  val _ =
    reject "rust-function-item-as-value"
      "unresolved body name \"RustMaximumCallArity\""
      (command "function_item_as_value"
        "fn FunctionItemAsValue() -> u8 { RustMaximumCallArity }")
  val _ =
    reject "rust-function-existing-constructor"
      "already owned by a Rust constructor item"
      (command "constructor_conflict"
        "fn SharedItem(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-recursive-definition"
      "RecursiveFunction"
      (command "recursive_function"
        "fn RecursiveFunction(x: u64) -> u64 { RecursiveFunction(x) }")
  val _ =
    reject "rust-function-inferred-hol-name-collision"
      "Duplicate constant"
      (occupied_hol_name "http2_xml_parser" ^
        "urust_fn " ^ cartouche "fn Http2XMLParser() {}")
  val _ =
    reject "rust-function-explicit-hol-name-collision"
      "Duplicate constant"
      (occupied_hol_name "empty_block" ^ command "empty_block"
        "fn DistinctRustName() {}")
in
end
\<close>

section\<open> Function declaration and reference navigation \<close>

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
            SOME "micro_rust_notation" andalso
          is_some (Properties.get properties property) andalso
          has_position properties position)
      markup

  val SOME entry = Parser_Test_Calls.lookup ctxt "RustAlias"
  val (definition_result, definition_chunks) =
    capture "definition"
      (fn () => Position.report (#reg_pos entry)
        (Position.make_entity_markup {def = true} (#serial entry)
          Micro_Rust_Names.notationN ("RustAlias", #reg_pos entry)))
  val _ =
    (case definition_result of
       Exn.Res _ => ()
     | Exn.Exn exn => Exn.reraise exn)
  val _ =
    if has_function_entity Markup.defN
         ((fn (entry: Micro_Rust_Names.entry) => #reg_pos entry) entry) (markups definition_chunks)
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

chapter\<open> Signature inference and registration regressions \<close>

section\<open> Audit helpers \<close>

ML \<open>
structure Parser_Function_Regression_Test =
struct
  structure Navigation = Micro_Rust_Semantic_Navigation

  fun require label condition =
    if condition then ()
    else error ("function type mapping regression: " ^ label)

  fun cartouche body = Symbol.open_ ^ body ^ Symbol.close

  fun start label =
    Position.make0 7 101 0 "" label ""
    |> Position.copy_id (Position.thread_data ())

  fun source label body =
    Parser_Lex_Util.positioned_content_source body (start label)

  fun parse ctxt label body =
    (case URust_Parser.parse_function_source ctxt (source label body) of
       SOME function => function
     | NONE => error ("empty function fixture " ^ quote label))

  fun parameter_type
      (URust_AST.Function_Parameter (_, _, typ, _)) = typ

  fun signature_types function =
    map parameter_type (URust_AST.function_parameters function) @
      the_list (URust_AST.function_return_type function)

  fun resolve ctxt function =
    Navigation.capture
      (fn () =>
        URust_Type_Mappings.resolve_signature ctxt
          (signature_types function))
    |> fst

  fun run_from state label text =
    let
      val thy = Toplevel.theory_of state
      val transitions =
        Outer_Syntax.parse_text thy (K thy) (start label) text
    in
      fold (Toplevel.command_exception true) transitions state
    end

  fun initial thy = Toplevel.make_state (SOME thy)

  fun command options target body =
    "urust_fn " ^ options ^ " " ^ target ^ " " ^ cartouche body

  fun theorem ctxt name = Proof_Context.get_thm ctxt (name ^ "_def")

  fun rhs ctxt name =
    theorem ctxt name |> Thm.prop_of |> Logic.dest_equals |> snd

  fun declared_type ctxt name =
    Proof_Context.read_const {proper = true, strict = false} ctxt name
    |> dest_Const_name
    |> Consts.the_constraint (Proof_Context.consts_of ctxt)

  fun channels typ =
    (case Term.body_type typ of
       Type (name, [state, result, abort, input, output]) =>
         (require "result is not function_body"
            (name = \<^type_name>\<open>function_body\<close>);
          (state, result, abort, input, output))
     | _ => error "expected a five-channel function_body")

  fun generic (TFree _) = true
    | generic (TVar _) = true
    | generic _ = false

  fun sort_of (TFree (_, sort)) = sort
    | sort_of (TVar (_, sort)) = sort
    | sort_of _ = error "expected a type variable"

  fun independent label types =
    require label
      (forall generic types andalso
        length (distinct (op =) types) = length types)

  fun function_snapshot ctxt =
    Parser_Test_Calls.dump ctxt
    |> map (fn (name, entry) =>
        (name, #hol_term entry, Position.properties_of (#reg_pos entry)))

  fun type_snapshot ctxt =
    URust_Item_Scope.dump_types ctxt
    |> map (fn entry =>
        (URust_Item_Scope.type_rust_name entry,
         URust_Item_Scope.type_hol_name entry,
         Position.properties_of (URust_Item_Scope.type_position entry)))

  fun constructor_snapshot ctxt =
    URust_Item_Scope.dump_constructors ctxt
    |> map (fn entry =>
        (URust_Item_Scope.constructor_rust_path entry,
         URust_Item_Scope.constructor_term entry,
         URust_Item_Scope.constructor_fields entry,
         Position.properties_of (URust_Item_Scope.constructor_position entry)))

  fun notation_snapshot ctxt =
    Micro_Rust_Names.dump ctxt
    |> map (fn (kind, name, entry) =>
        (kind, name, #hol_term entry, #source_const entry, #serial entry,
         Position.properties_of (#reg_pos entry)))

  fun mapping_snapshot ctxt =
    URust_Type_Mappings.dump ctxt
    |> map (fn (name, entry) =>
        (name, URust_Type_Mappings.entry_template entry,
         URust_Type_Mappings.entry_arities entry,
         URust_Type_Mappings.entry_parameter_sorts entry,
         URust_Type_Mappings.entry_identity entry))

  fun constant_snapshot ctxt =
    #constants (Consts.dest (Proof_Context.consts_of ctxt))

  fun ownership_snapshot ctxt =
    Micro_Rust_Names.Declaration_Owners.get (Context.Proof ctxt)
    |> Symtab.dest
    |> map (fn (name, owners) => (name,
        map (fn ({kind, pos}: Micro_Rust_Names.declaration_owner) =>
          (kind, Position.properties_of pos)) owners))

  fun registry_unchanged label earlier later =
    (require (label ^ ": function registry changed")
       (function_snapshot earlier = function_snapshot later);
     require (label ^ ": generated type registry changed")
       (type_snapshot earlier = type_snapshot later);
     require (label ^ ": constructor registry changed")
       (constructor_snapshot earlier = constructor_snapshot later);
     require (label ^ ": declaration ownership changed")
       (ownership_snapshot earlier = ownership_snapshot later);
     require (label ^ ": notation registry changed")
       (notation_snapshot earlier = notation_snapshot later);
     require (label ^ ": type registry changed")
       (mapping_snapshot earlier = mapping_snapshot later))

  fun message result =
    (case result of
       Exn.Res _ => error "expected rejection, but command succeeded"
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else Runtime.exn_message exn)

  fun has_position properties position =
    Properties.get properties Markup.offsetN =
      Option.map Value.print_int (Position.offset_of position) andalso
    Properties.get properties Markup.end_offsetN =
      Option.map Value.print_int (Position.end_offset_of position) andalso
    Properties.get properties Markup.idN = Position.id_of position

  fun has_markup name position markup =
    exists
      (fn (actual, properties) =>
        actual = name andalso has_position properties position)
      markup

  fun entities kind markup =
    filter
      (fn (name, properties) =>
        name = Markup.entityN andalso
        Properties.get properties Markup.kindN = SOME kind)
      markup

  fun declaration_definitions markup =
    filter
      (fn (name, properties) =>
        name = Markup.entityN andalso
        is_some (Properties.get properties Markup.defN) andalso
        member (op =)
          ["urust_item", "urust_constructor", "urust_field", "micro_rust_notation",
           "micro_rust_type_mapping"]
          (the_default "" (Properties.get properties Markup.kindN)))
      markup

  fun entity_ids kind property rust_name position markup =
    entities kind markup
    |> map_filter
        (fn (_, properties) =>
          if Properties.get properties Markup.nameN = SOME rust_name andalso
              has_position properties position
          then Properties.get properties property
          else NONE)
    |> distinct (op =)

  fun find_from text needle offset =
    if offset + size needle > size text then
      error ("missing source token " ^ quote needle)
    else if String.substring (text, offset, size needle) = needle then
      offset
    else find_from text needle (offset + 1)

  fun token_position text source_start needle offset =
    let
      val raw = find_from text needle offset
      val token_start =
        Position.symbol_explode
          (String.substring (text, 0, raw)) source_start
    in
      Position.range_position
        (token_start, Position.symbol_explode needle token_start)
    end

  fun diagnostic_ranges message =
    let
      fun collect (XML.Text _) ranges = ranges
        | collect (XML.Elem ((_, properties), children)) ranges =
            let
              val ranges' =
                (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                   (SOME offset, SOME end_offset) =>
                     (offset, end_offset) :: ranges
                 | _ => ranges)
            in fold collect children ranges' end
    in
      distinct (op =) (fold collect (YXML.parse_body message) [])
    end

  fun range_of position =
    (Value.print_int (the (Position.offset_of position)),
     Value.print_int (the (Position.end_offset_of position)))
end
\<close>

section\<open> Types, effect channels and wrapper shape \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>

    fun identity (name, expected) =
      let
        val typ = declared_type ctxt name
        val (state, result, abort, input, output) = channels typ
        val effects = [state, abort, input, output]
      in
        require (name ^ ": parameter mapping changed")
          (binder_types typ = [expected]);
        require (name ^ ": result mapping changed") (result = expected);
        independent (name ^ ": unused effects were specialized or shared") effects;
        require (name ^ ": value leaked into unused effects")
          (not (member (op =) effects result))
      end

    val _ =
      List.app identity
        [("signature_primitive", \<^typ>\<open>8 word\<close>),
         ("signature_custom", \<^typ>\<open>nat\<close>),
         ("signature_qualified", \<^typ>\<open>bool\<close>),
         ("signature_generic", \<^typ>\<open>(8 word option, bool) result\<close>),
         ("signature_segmented", \<^typ>\<open>(16 word, bool option) result\<close>),
         ("signature_generated_struct", \<^typ>\<open>signature_packet\<close>),
         ("signature_generated_enum", \<^typ>\<open>signature_choice_hol\<close>),
         ("signature_grouped", \<^typ>\<open>8 word\<close>),
         ("signature_tuple",
          \<^typ>\<open>8 word \<times> (bool \<times> nat \<times> tnil) \<times>
            16 word option \<times> tnil\<close>),
         ("signature_hol_escape", \<^typ>\<open>nat option\<close>),
         ("signature_function_result", \<^typ>\<open>nat \<Rightarrow> nat\<close>),
         ("signature_nested_hole", \<^typ>\<open>16 word option\<close>),
         ("signature_result_hole", \<^typ>\<open>32 word\<close>),
         ("signature_inferred_result", \<^typ>\<open>64 word\<close>)]

    val holes = declared_type ctxt "signature_holes"
    val (_, holes_result, _, _, _) = channels holes
    val _ =
      require "distinct HOL holes were conflated"
        (binder_types holes = [\<^typ>\<open>8 word\<close>, \<^typ>\<open>bool\<close>] andalso
          holes_result = \<^typ>\<open>8 word \<times> bool \<times> tnil\<close>)

    val mixed_identity = declared_type ctxt "signature_identity_two_instantiations"
    val (_, mixed_identity_result, _, _, _) = channels mixed_identity
    val _ =
      require "one function could not instantiate a registered identity at u8 and bool"
        (binder_types mixed_identity = [\<^typ>\<open>8 word\<close>, \<^typ>\<open>bool\<close>] andalso
          mixed_identity_result = \<^typ>\<open>8 word \<times> bool \<times> tnil\<close>)
    val identity_occurrences =
      Term.fold_aterms
        (fn Const (name, typ) =>
              if name = \<^const_name>\<open>signature_plain_identity\<close>
              then cons typ else I
          | _ => I)
        (rhs ctxt "signature_identity_two_instantiations") []
    val _ =
      require "registry calls reused one type-variable instantiation"
        (length identity_occurrences = 2 andalso
          exists (fn typ => binder_types typ = [\<^typ>\<open>8 word\<close>]) identity_occurrences andalso
          exists (fn typ => binder_types typ = [\<^typ>\<open>bool\<close>]) identity_occurrences)

    val shared = declared_type ctxt "signature_shared_variables"
    val [left, right] = binder_types shared
    val (state, result, abort, input, output) = channels shared
    val _ =
      require "signature type variables are not shared across escapes"
        (generic left andalso left = right andalso right = result)
    val _ =
      independent "signature variable captured an unused effect"
        [left, state, abort, input, output]

    val inferred = declared_type ctxt "signature_inferred_polymorphic_result"
    val [inferred_parameter] = binder_types inferred
    val (inferred_state, inferred_result, inferred_abort, inferred_input, inferred_output) =
      channels inferred
    val _ =
      require "explicit polymorphic return lost its signature type variable"
        (inferred_result = inferred_parameter)
    val _ =
      independent "explicit polymorphic return specialized an unused type variable"
        [inferred_parameter, inferred_state, inferred_abort, inferred_input, inferred_output]

    val sorted = declared_type ctxt "signature_shared_sorts"
    val [values, value] = binder_types sorted
    val (_, sorted_result, _, _, _) = channels sorted
    val _ =
      require "shared signature sorts were not refined"
        (generic value andalso values = HOLogic.listT value andalso
          sorted_result = values andalso
          Sign.subsort (Proof_Context.theory_of ctxt)
            (sort_of value, \<^sort>\<open>linorder\<close>))

    val higher = declared_type ctxt "signature_higher_order"
    val [operation, argument] = binder_types higher
    val (_, higher_result, _, _, _) = channels higher
    val _ =
      require "higher-order signature arrows consumed parameter slots"
        (operation = (argument --> higher_result) andalso
          generic argument andalso generic higher_result andalso
          argument <> higher_result)

    val _ =
      List.app
        (fn name =>
          let val (_, result, _, _, _) = channels (declared_type ctxt name) in
            require (name ^ ": unit result changed") (result = \<^typ>\<open>unit\<close>)
          end)
        ["signature_omitted_return", "signature_explicit_unit",
         "signature_inferred_write"]

    val (read_state, read_result, read_abort, read_input, read_output) =
      channels (declared_type ctxt "signature_inferred_state")
    val _ =
      require "get did not constrain the state and result"
        (read_state = \<^typ>\<open>nat\<close> andalso read_result = \<^typ>\<open>nat\<close>)
    val _ =
      independent "get constrained an unused effect"
        [read_abort, read_input, read_output]

    val (write_state, _, write_abort, write_input, write_output) =
      channels (declared_type ctxt "signature_inferred_write")
    val _ = require "put did not constrain the state" (write_state = \<^typ>\<open>nat\<close>)
    val _ =
      independent "put constrained an unused effect"
        [write_abort, write_input, write_output]

    val (abort_state, abort_result, abort_payload, abort_input, abort_output) =
      channels (declared_type ctxt "signature_inferred_abort")
    val _ =
      require "CustomAbort did not constrain the abort payload"
        (abort_payload = \<^typ>\<open>nat\<close> andalso abort_result = \<^typ>\<open>bool\<close>)
    val _ =
      independent "CustomAbort constrained an unused effect"
        [abort_state, abort_input, abort_output]

    val (prompt_state, prompt_result, prompt_abort, prompt_input, prompt_output) =
      channels (declared_type ctxt "signature_inferred_prompt")
    val (input_parameter, output_parameter) =
      (case (prompt_input, prompt_output) of
         (Type (input_name, [i]), Type (output_name, [o])) =>
           (require "yield prompt constructors changed"
              (input_name = \<^type_name>\<open>prompt\<close> andalso
                output_name = \<^type_name>\<open>prompt_output\<close>);
            (i, o))
       | _ => error "yield did not constrain the prompt channels")
    val _ = require "yield changed the Rust result" (prompt_result = \<^typ>\<open>8 word\<close>)
    val _ =
      independent "yield specialized its otherwise unused type variables"
        [prompt_state, prompt_abort, input_parameter, output_parameter]

    fun count_wrapper term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = \<^const_name>\<open>FunctionBody\<close> then Integer.add 1 else I
          | _ => I)
        term 0
    val _ =
      List.app
        (fn name =>
          require (name ^ ": FunctionBody wrapper count changed")
            (count_wrapper (rhs ctxt name) = 1))
        ["signature_primitive", "signature_higher_order", "signature_function_result",
         "signature_omitted_return", "signature_inferred_state", "signature_inferred_prompt"]
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val _ =
      List.app
        (fn (rust, hol) =>
          let
            val state =
              run_from base ("signature-primitive-command-" ^ rust)
                (command "" "signature_primitive_command"
                  ("fn SignaturePrimitiveCommand(value: " ^ rust ^ ") -> " ^
                    rust ^ " { value }"))
            val typ =
              declared_type (Toplevel.context_of state) "signature_primitive_command"
            val (state_type, result, abort, input, output) = channels typ
          in
            require ("primitive command parameter/result " ^ rust)
              (binder_types typ = [hol] andalso result = hol);
            independent ("primitive command unused effects " ^ rust)
              [state_type, abort, input, output]
          end)
        [("u8", \<^typ>\<open>8 word\<close>),
         ("u16", \<^typ>\<open>16 word\<close>),
         ("u32", \<^typ>\<open>32 word\<close>),
         ("u64", \<^typ>\<open>64 word\<close>),
         ("usize", \<^typ>\<open>64 word\<close>),
         ("i32", \<^typ>\<open>32 word\<close>),
         ("i64", \<^typ>\<open>64 word\<close>),
         ("bool", \<^typ>\<open>bool\<close>),
         ("()", \<^typ>\<open>unit\<close>)]
  in
    val _ = ()
  end
\<close>

section\<open> Exported resolver and elaborator interfaces \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = Context_Position.set_visible true \<^context>
    val original_functions = function_snapshot ctxt
    val original_mappings = mapping_snapshot ctxt

    val _ =
      List.app
        (fn (rust, hol) =>
          let
            val function =
              parse ctxt ("signature-api-" ^ rust)
                ("fn APIPrimitive(value: " ^ rust ^ ") -> " ^ rust ^ " { value }")
            val actual = resolve ctxt function
          in
            require ("primitive signature API mapping " ^ rust) (actual = [hol, hol])
          end)
        [("u8", \<^typ>\<open>8 word\<close>),
         ("u16", \<^typ>\<open>16 word\<close>),
         ("u32", \<^typ>\<open>32 word\<close>),
         ("u64", \<^typ>\<open>64 word\<close>),
         ("usize", \<^typ>\<open>64 word\<close>),
         ("i32", \<^typ>\<open>32 word\<close>),
         ("i64", \<^typ>\<open>64 word\<close>),
         ("bool", \<^typ>\<open>bool\<close>),
         ("()", \<^typ>\<open>unit\<close>)]

    val generic_item =
      parse ctxt "signature-api-sharing"
        ("fn APISharing(left: " ^ "\<tau>" ^ cartouche "'shared" ^
          ", right: SignatureOption<" ^ "\<tau>" ^ cartouche "'shared" ^
          ">) -> " ^ "\<tau>" ^ cartouche "'shared" ^ " { left }")
    val [left, right, result] = resolve ctxt generic_item
    val _ =
      require "resolve_signature allocated separate variables for one HOL name"
        (generic left andalso right = Type (\<^type_name>\<open>option\<close>, [left]) andalso
          result = left)

    val sorted_item =
      parse ctxt "signature-api-sort-sharing"
        ("fn APISorts(value: " ^ "\<tau>" ^ cartouche "'ordered" ^
          ") -> SignatureOrdered<" ^ "\<tau>" ^ cartouche "'ordered" ^ "> { () }")
    val [ordered, ordered_list] = resolve ctxt sorted_item
    val _ =
      require "resolve_signature lost a sort imposed by another signature slot"
        (generic ordered andalso ordered_list = HOLogic.listT ordered andalso
          Sign.subsort (Proof_Context.theory_of ctxt)
            (sort_of ordered, \<^sort>\<open>linorder\<close>))

    val empty = resolve ctxt (parse ctxt "signature-api-empty" "fn APIEmpty() {}")
    val _ = require "empty signature API result changed" (null empty)

    (* The datatype resolver must keep its monomorphic contract. *)
    val [polymorphic_field] = signature_types
      (parse ctxt "signature-api-datatype-control"
        ("fn APIControl(value: " ^ "\<tau>" ^ cartouche "'field" ^ ") {}"))
    val datatype_failure =
      Exn.result
        (fn () => Navigation.capture (fn () =>
          URust_Type_Mappings.resolve ctxt polymorphic_field)) ()
      |> message
    val _ =
      require "datatype resolver accepted a signature-only type variable"
        (String.isSubstring "type variables are not supported" datatype_failure)

    (* The public record shape remains the explicit typed-body API. *)
    val body_type =
      "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
    val api_term =
      Parser_Test_Elaboration.function ctxt
        {raw_type = (body_type, start "signature-stable-api-type"),
         parameters = [("value", start "signature-stable-api-parameter")],
         parameters_pos = start "signature-stable-api-parameter",
         body = source "signature-stable-api-body" "value"}
    val _ =
      require "URust_Command.elaborate changed its typed-body contract"
        (fastype_of api_term = Syntax.read_typ ctxt body_type)
    val _ =
      require "pure resolver or elaborator installed function entries"
        (function_snapshot ctxt = original_functions)
    val _ =
      require "pure resolver or elaborator installed type mappings"
        (mapping_snapshot ctxt = original_mappings)
    val _ =
      registry_unchanged "pure exported interfaces" \<^context> ctxt
  in
    val _ = ()
  end
\<close>

section\<open> Shared signature sorts and independent holes \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open URust_AST
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    val layout = make_source_layout Position.none []

    fun hol text = HOL_Type_Source (Input.string text)
    fun nominal name arguments =
      Path_Type
        ([Rust_Type_Path_Segment
            (name, Position.none,
             SOME (map Rust_Type_Argument arguments), layout)],
         layout)
    fun resolve_batch context types =
      Navigation.capture
        (fn () => URust_Type_Mappings.resolve_signature context types)
      |> fst
    fun rejected_sort label context types =
      let
        val diagnostic =
          Exn.result (fn () => resolve_batch context types) () |> message
      in
        require (label ^ ": unexpected sort rejection: " ^ diagnostic)
          (String.isSubstring "urust_fn: generic argument type" diagnostic)
      end

    val shared =
      resolve_batch ctxt [hol "'value", hol "'value::linorder"]
    val ordered_value = TFree ("'value", \<^sort>\<open>linorder\<close>)
    val _ =
      require "explicit sort was not shared by the complete signature batch"
        (shared = replicate 2 ordered_value)
    val strengthened =
      resolve_batch ctxt
        [hol "'value", nominal "SignatureOrdered" [hol "'value"],
         hol "'value option"]
    val _ =
      require "mapping sort did not strengthen every occurrence of a named variable"
        (strengthened =
          [ordered_value, HOLogic.listT ordered_value,
           Type (\<^type_name>\<open>option\<close>, [ordered_value])])

    val fixed = TFree ("'fixed", \<^sort>\<open>type\<close>)
    val fixed_ctxt = Variable.declare_typ fixed ctxt
    val _ =
      rejected_sort "insufficient rigid ambient sort" fixed_ctxt
        [nominal "SignatureOrdered" [hol "'fixed"]]
    val _ =
      require "rejected mapping strengthened the ambient type variable"
        (resolve_batch fixed_ctxt [hol "'fixed"] = [fixed])
    val fixed_ordered = TFree ("'fixed", \<^sort>\<open>linorder\<close>)
    val fixed_ordered_ctxt = Variable.declare_typ fixed_ordered ctxt
    val _ =
      require "sufficient rigid ambient sort changed"
        (resolve_batch fixed_ordered_ctxt
          [hol "'fixed", nominal "SignatureOrdered" [hol "'fixed"]] =
            [fixed_ordered, HOLogic.listT fixed_ordered])

    val nested =
      resolve_batch ctxt
        [hol "'nested", nominal "SignatureFinite" [hol "'nested option"]]
    val finite_value = TFree ("'nested", \<^sort>\<open>finite\<close>)
    val _ =
      require "option finiteness did not propagate to its element type"
        (nested =
          [finite_value,
           HOLogic.listT (Type (\<^type_name>\<open>option\<close>, [finite_value]))])
    val _ =
      rejected_sort "list does not acquire linorder from its element" ctxt
        [hol "'nested", nominal "SignatureOrdered" [hol "'nested list"]]

    val holes = resolve_batch ctxt [hol "_", hol "_", hol "_ \<times> _"]
    val hole_variables = fold Term.add_tvarsT holes []
    val _ =
      require "anonymous holes were coupled within or between HOL escapes"
        (length hole_variables = 4 andalso
          forall (Type_Infer.is_param o fst) hole_variables)

    val reused_source = hol "_"
    val reused = resolve_batch ctxt [reused_source, reused_source]
    val reused_variables = fold Term.add_tvarsT reused []
    val _ =
      require "reusing one HOL_Type_Source coupled its independent occurrences"
        (length reused_variables = 2 andalso
          forall (Type_Infer.is_param o fst) reused_variables)

    val [ordered_hole, explicitly_ordered_hole, finite_hole] =
      resolve_batch ctxt
        [nominal "SignatureOrdered" [hol "_"],
         nominal "SignatureOrdered" [hol "_::linorder"],
         nominal "SignatureFinite" [hol "_::finite"]]
    val sorted_variables =
      fold Term.add_tvarsT [ordered_hole, explicitly_ordered_hole, finite_hole] []
    val _ =
      require "independently sorted holes shared an inference variable"
        (length sorted_variables = 3 andalso
          forall (Type_Infer.is_param o fst) sorted_variables)
    fun has_hole_sort expected typ =
      (case Term.add_tvarsT typ [] of
         [(variable, sort)] =>
           Type_Infer.is_param variable andalso Sign.subsort thy (sort, expected)
       | _ => false)
    val _ =
      require "independent hole sorts were lost"
        (has_hole_sort \<^sort>\<open>linorder\<close> ordered_hole andalso
          has_hole_sort \<^sort>\<open>linorder\<close> explicitly_ordered_hole andalso
          has_hole_sort \<^sort>\<open>finite\<close> finite_hole)

    val combined =
      resolve_batch ctxt
        [hol "'combined",
         nominal "SignatureOrdered" [hol "'combined"],
         nominal "SignatureFinite" [hol "'combined"], hol "'combined"]
    val _ =
      require "multiple mappings did not share their sort intersection"
        (case fold Term.add_tfreesT combined [] of
           [("'combined", sort)] =>
             Sign.subsort thy (sort, \<^sort>\<open>linorder\<close>) andalso
             Sign.subsort thy (sort, \<^sort>\<open>finite\<close>)
         | _ => false)
  in
    val _ = ()
  end
\<close>

section\<open> Function registration options and artifacts \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val base_ctxt = Toplevel.context_of base

    fun audit_case (label, prefix, options, target, registered, abbreviated) =
      let
        val rust = "SignatureOptionMatrix"
        val hol = if target = "" then "signature_option_matrix" else target
        val scoped_state = run_from base (label ^ "-scope") prefix
        val state =
          run_from scoped_state label
            (command options target
              ("fn " ^ rust ^ "(value: u16) -> u16 { value }"))
        val ctxt = Toplevel.context_of state
        val entry = Parser_Test_Calls.lookup ctxt rust
        val _ = require (label ^ ": registration option ignored") (is_some entry = registered)
        val _ =
          if target = "_" then
            (registry_unchanged label (Toplevel.context_of scoped_state) ctxt;
             require (label ^ ": anonymous item installed a HOL artifact")
               (constant_snapshot (Toplevel.context_of scoped_state) =
                 constant_snapshot ctxt))
          else
            let
              val expanded = Syntax.read_term ctxt hol
              val (_, result, _, _, _) = channels (fastype_of expanded)
              val _ = require (label ^ ": inferred type changed") (result = \<^typ>\<open>16 word\<close>)
              val has_def = can (Proof_Context.get_thm ctxt) (hol ^ "_def")
              val _ =
                require (label ^ ": abbreviation/definition artifacts changed")
                  (has_def = not abbreviated)
              val _ =
                if abbreviated then ()
                else
                  let
                    val (lhs, body) =
                      theorem ctxt hol |> Thm.prop_of |> Logic.dest_equals
                  in
                    require (label ^ ": ordinary definition lost its lambda rhs")
                      (null (#2 (Term.strip_comb lhs)) andalso
                        length (binder_types (fastype_of body)) = 1)
                  end
              val _ =
                (case entry of
                   NONE => ()
                 | SOME registered_entry =>
                     require (label ^ ": registered target differs from installed artifact")
                       (Term.aconv_untyped
                         (Proof_Context.expand_abbrevs ctxt
                            ((fn (entry: Micro_Rust_Names.entry) => #hol_term entry) registered_entry),
                          expanded)))
            in () end
        val _ =
          require (label ^ ": registration changed unrelated type mappings")
            (mapping_snapshot ctxt = mapping_snapshot base_ctxt)
      in () end

    val _ =
      List.app audit_case
        [("default-inferred", "", "", "", true, false),
         ("default-named", "", "", "signature_matrix_named", true, false),
         ("bare-inferred", "", "[register_notation]", "", true, false),
         ("bare-named", "", "[register_notation]", "signature_matrix_named", true, false),
         ("true-inferred", "", "[register_notation = true]", "", true, false),
         ("true-named", "", "[register_notation = true]", "signature_matrix_named", true, false),
         ("false-inferred", "", "[register_notation = false]", "", false, false),
         ("false-named", "", "[register_notation = false]", "signature_matrix_named", false, false),
         ("scoped-off", "declare [[urust_register_notation = false]]",
          "", "", false, false),
         ("bare-overrides-scoped-off", "declare [[urust_register_notation = false]]",
          "[register_notation]", "", true, false),
         ("true-overrides-scoped-off", "declare [[urust_register_notation = false]]",
          "[register_notation = true]", "signature_matrix_named", true, false),
         ("false-overrides-scoped-on", "declare [[urust_register_notation = true]]",
          "[register_notation = false]", "", false, false),
         ("abbrev-inferred", "", "[abbrev]", "", true, true),
         ("abbrev-named", "", "[abbrev]", "signature_matrix_named", true, true),
         ("abbrev-off", "", "[abbrev, register_notation = false]",
          "signature_matrix_named", false, true),
         ("scoped-abbrev", "declare [[urust_abbrev = true]]",
          "[register_notation = false]", "", false, true),
         ("anonymous-default", "", "", "_", false, false),
         ("anonymous-enabled", "", "[register_notation]", "_", false, false),
         ("anonymous-abbrev", "", "[abbrev, register_notation]", "_", false, true),
         ("mixed-options-first", "", "[register_notation = false, pp_test, verbosity = 0]",
          "signature_matrix_named", false, false),
         ("mixed-options-last", "", "[verbosity = 0, pp_test, register_notation]",
          "signature_matrix_named", true, false)]

    val scoped =
      run_from base "signature-registration-nested-scope"
        ("context notes [[urust_register_notation = false]]\nbegin\n" ^
          command "" "signature_scoped_off"
            "fn SignatureScopedOff(value: u8) -> u8 { value }" ^ "\n" ^
          "context notes [[urust_register_notation = true]]\nbegin\n" ^
          command "[register_notation = false]" "signature_nested_off"
            "fn SignatureNestedOff(value: u8) -> u8 { value }" ^ "\n" ^
          "end\nend\n" ^
          command "" "signature_restored_on"
            "fn SignatureRestoredOn(value: u8) -> u8 { value }")
    val scoped_ctxt = Toplevel.context_of scoped
    val _ =
      require "scoped registration configuration leaked"
        (is_none (Parser_Test_Calls.lookup scoped_ctxt "SignatureScopedOff") andalso
          is_none (Parser_Test_Calls.lookup scoped_ctxt "SignatureNestedOff") andalso
          is_some (Parser_Test_Calls.lookup scoped_ctxt "SignatureRestoredOn"))

    val application =
      run_from base "signature-application-artifacts"
        (command "[application_def, attrs = [micro_rust_simps], register_notation = false]"
          "signature_application_artifact"
          "fn SignatureApplicationArtifact(value: u8) -> u8 { value }")
    val application_ctxt = Toplevel.context_of application
    val application_thm = theorem application_ctxt "signature_application_artifact"
    val (application_lhs, _) = application_thm |> Thm.prop_of |> Logic.dest_equals
    val _ =
      require "application_def lost source parameter application"
        (length (#2 (Term.strip_comb application_lhs)) = 1)
    val _ =
      require "attrs were lost with registration disabled"
        (exists
          (Thm.equiv_thm (Proof_Context.theory_of application_ctxt) o pair application_thm)
          (Named_Theorems.get application_ctxt \<^named_theorems>\<open>micro_rust_simps\<close>))
  in
    val _ = ()
  end
\<close>

section\<open> Occupied paths, atomic rejection, and recovery \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val earlier_ctxt = Toplevel.context_of base

    val _ =
      List.app
        (fn (label, options, target, rust, typ) =>
          let
            val state =
              run_from base label
                (command options target
                  ("fn " ^ rust ^ "(value: " ^ typ ^ ") -> " ^ typ ^ " { value }"))
            val later_ctxt = Toplevel.context_of state
          in
            registry_unchanged label earlier_ctxt later_ctxt;
            if target = "_" then
              require (label ^ ": anonymous occupied path installed a HOL artifact")
                (constant_snapshot earlier_ctxt = constant_snapshot later_ctxt)
            else ignore (theorem later_ctxt target)
          end)
        [("occupied-function-optout", "[register_notation = false]",
          "signature_occupied_optout", "SignaturePrimitive", "u8"),
         ("occupied-constructor-optout", "[register_notation = false]",
          "signature_occupied_optout", "SignaturePacket", "SignaturePacket"),
         ("occupied-notation-optout", "[register_notation = false]",
          "signature_occupied_optout", "SignatureExistingCall", "u8"),
         ("occupied-function-anonymous", "[register_notation]", "_",
          "SignaturePrimitive", "u8"),
         ("occupied-constructor-anonymous", "[register_notation]", "_",
          "SignaturePacket", "SignaturePacket"),
         ("occupied-notation-anonymous", "[register_notation]", "_",
          "SignatureExistingCall", "u8")]

    fun reject label expected text =
      let
        val (result, markup) =
          Parser_Test_Reports.markup
            (fn () => Exn.result (fn () => run_from base label text) ())
        val diagnostic =
          (case result of
             Exn.Res _ => error (label ^ ": expected command rejection")
           | _ => message result)
        val _ =
          require (label ^ ": unexpected diagnostic: " ^ diagnostic)
            (String.isSubstring expected diagnostic)
        val _ =
          require (label ^ ": source position missing")
            (String.isSubstring label diagnostic)
        val _ =
          if expected = "Type" then
            require (label ^ ": type mismatch lost its source range")
              (not (null (diagnostic_ranges diagnostic)))
          else ()
        val _ =
          require (label ^ ": failed command emitted successful mapping navigation")
            (null (entities "micro_rust_type_mapping" markup))
        val _ =
          require (label ^ ": failed command emitted successful function navigation")
            (null (entities "micro_rust_notation" markup))
        val unchanged = Toplevel.context_of base
        val _ = registry_unchanged (label ^ " rollback") earlier_ctxt unchanged
        val _ =
          require (label ^ ": failed command left HOL artifacts")
            (constant_snapshot earlier_ctxt = constant_snapshot unchanged)
        val _ =
          require (label ^ ": failed command installed a HOL constant")
            (not (can (declared_type unchanged) "signature_failure"))
        val recovered =
          run_from base (label ^ "-recovery")
            (command "" "signature_failure"
              "fn SignatureFailure(value: u8) -> u8 { value }")
        val recovered_ctxt = Toplevel.context_of recovered
      in
        require (label ^ ": parser/registry did not recover")
          (is_some (Parser_Test_Calls.lookup recovered_ctxt "SignatureFailure"));
        ignore (theorem recovered_ctxt "signature_failure")
      end

    fun item options body = command options "signature_failure" body

    val _ =
      List.app
        (fn (label, expected, body) => reject label expected (item "" body))
        [("signature-parameter-body-mismatch", "Type",
          "fn SignatureFailure(value: bool) -> u8 { value }"),
         ("signature-result-body-mismatch", "Type",
          "fn SignatureFailure(value: u8) -> bool { value }"),
         ("signature-shared-variable-mismatch", "Type",
          "fn SignatureFailure(left: \<tau>\<open>'a\<close>, right: \<tau>\<open>'a\<close>) \
          \-> (u8, bool) { (left, right) }"),
         ("signature-unknown-parameter", "unknown Rust type \"MissingSignatureType\"",
          "fn SignatureFailure(value: MissingSignatureType) -> () { () }"),
         ("signature-unknown-result", "unknown Rust type \"missing::SignatureType\"",
          "fn SignatureFailure(value: u8) -> missing::SignatureType { value }"),
         ("signature-no-implicit-hol-type", "unknown Rust type \"signature_unregistered_hol\"",
          "fn SignatureFailure(value: signature_unregistered_hol) { () }"),
         ("signature-unregistered-primitive", "unknown Rust type \"u128\"",
          "fn SignatureFailure(value: u128) { () }"),
         ("signature-generic-arity-small", "active urust_type mapping expects [2]",
          "fn SignatureFailure(value: SignatureResult<u8>) { () }"),
         ("signature-generic-arity-large", "active urust_type mapping expects [1]",
          "fn SignatureFailure(value: SignatureOption<u8, bool>) { () }"),
         ("signature-segment-arity", "active urust_type mapping expects [0, 1, 1]",
          "fn SignatureFailure(value: signature::Header::Body<u8, bool>) { () }"),
         ("signature-prelude-option-arity", "active urust_type mapping expects [1]",
          "fn SignatureFailure(value: Option<u8, bool>) { () }"),
         ("signature-prelude-result-arity", "active urust_type mapping expects [2]",
          "fn SignatureFailure(value: Result<u8>) { () }"),
         ("signature-prelude-bare-option", "active urust_type mapping expects [1]",
          "fn SignatureFailure(value: Option) { () }"),
         ("signature-invalid-sort", "does not satisfy sort",
          "fn SignatureFailure(value: SignatureOrdered<SignatureFunction>) { () }"),
         ("signature-unknown-hol-sort", "Undeclared class",
          "fn SignatureFailure(value: \<tau>\<open>'a::missing_signature_sort\<close>) { () }"),
         ("signature-reference", "shared Rust references",
          "fn SignatureFailure(value: &u8) { () }"),
         ("signature-raw-const-pointer-unknown-pointee", "unknown Rust type \"MissingPointee\"",
          "fn SignatureFailure(value: *const MissingPointee) { () }"),
         ("signature-raw-mut-pointer-unknown-pointee", "unknown Rust type \"MissingPointee\"",
          "fn SignatureFailure(value: *mut MissingPointee) { () }"),
         ("signature-slice", "Rust slice types",
          "fn SignatureFailure(value: [u8]) { () }"),
         ("signature-zero-array", "does not satisfy sort",
          "fn SignatureFailure(value: [u8; 0]) { () }"),
         ("signature-undeclared-array-length", "unknown Rust type \"LENGTH\"",
          "fn SignatureFailure(value: [u8; LENGTH]) { () }"),
         ("signature-singleton-tuple", "singleton tuple types",
          "fn SignatureFailure(value: (u8,)) { () }"),
         ("signature-numeric-generic", "numeric generic arguments",
          "fn SignatureFailure(value: SignatureOption<4>) { () }"),
         ("signature-result-reference", "shared Rust references",
          "fn SignatureFailure(value: u8) -> &u8 { value }"),
         ("signature-destructuring", "unsupported function parameter pattern",
          "fn SignatureFailure((left, right): (u8, bool)) -> u8 { left }"),
         ("signature-duplicate-parameter", "duplicate parameter",
          "fn SignatureFailure(value: u8, value: bool) -> u8 { value }"),
         ("signature-untyped-receiver", "receiver shorthand is only allowed in impl members",
          "fn SignatureFailure(self) -> u8 { self }"),
         ("signature-body-unresolved", "unresolved body name",
          "fn SignatureFailure(value: u8) -> u8 { MissingSignatureBody(value) }"),
         ("signature-trailing-input", "syntax error",
          "fn SignatureFailure(value: u8) -> u8 { value } trailing")]

    val _ =
      List.app
        (fn (label, expected, options) =>
          reject label expected
            (item options "fn SignatureFailure(value: u8) -> u8 { value }"))
        [("registration-duplicate-option", "duplicate uRust command option",
          "[register_notation, register_notation = false]"),
         ("registration-nonboolean-option", "expects true or false", "[register_notation = 1]"),
         ("registration-unknown-option", "unknown uRust command option",
          "[urust_register_notation = false]"),
         ("registration-abbrev-attrs", "attrs is not supported in abbreviation mode",
          "[abbrev, register_notation = false, attrs = []]"),
         ("registration-abbrev-application", "abbreviation mode cannot be combined",
          "[abbrev, register_notation = false, application_def]")]

    val _ =
      List.app
        (fn (label, expected, rust, typ) =>
          reject label expected
            (item "[register_notation]"
              ("fn " ^ rust ^ "(value: " ^ typ ^ ") -> " ^ typ ^ " { value }")))
        [("registration-existing-constructor", "already owned by a Rust constructor item",
          "SignaturePacket", "SignaturePacket")]

    val _ =
      reject "registration-disabled-still-checks-signature" "unknown Rust type"
        (item "[register_notation = false]"
          "fn SignaturePrimitive(value: MissingSignatureType) { () }")
    val _ =
      reject "registration-disabled-still-checks-body" "Type"
        (item "[register_notation = false]"
          "fn SignaturePrimitive(value: u8) -> bool { value }")
    val _ =
      reject "signature-outer-type-terminal" "declared result type must be function_body"
        ("urust_fn signature_failure :: " ^ cartouche "nat" ^ " " ^
          cartouche "fn SignatureFailure(value: u8) -> u8 { value }")
    val _ =
      reject "signature-outer-parameters-rejected" "Outer syntax error"
        ("urust_fn signature_failure (value) " ^
          cartouche "fn SignatureFailure(value: u8) -> u8 { value }")
    val _ =
      reject "signature-legacy-body-rejected" "syntax error"
        (item "" "value")
    val _ =
      reject "signature-hol-target-collision" "Duplicate constant"
        ("definition signature_primitive where " ^
          cartouche "signature_primitive = ()" ^ "\n" ^
          command "[register_notation = false]" "signature_primitive"
          "fn SignatureFreshFailedRegistration(value: u8) -> u8 { value }")
  in
    val _ = ()
  end
\<close>

section\<open> Positioned resolver errors and native navigation \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = Context_Position.set_visible true \<^context>
    val mapping_kind = "micro_rust_type_mapping"

    val label = "signature-native-navigation"
    val text =
      "fn Navigation(value: signature::Header<u8>::Body<SignatureOption<bool>>) \
      \-> SignaturePacket { value }"
    val (function, lexical_markup) =
      Parser_Test_Reports.markup (fn () => parse ctxt label text)
    val ((resolved, deferred), eager_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.capture
          (fn () => URust_Type_Mappings.resolve_signature ctxt (signature_types function)))
    val _ =
      require "signature resolver emitted mapping navigation before replay"
        (null (entities mapping_kind eager_markup))
    val _ =
      require "navigation resolver changed signature meaning"
        (resolved =
          [\<^typ>\<open>(8 word, bool option) result\<close>, \<^typ>\<open>signature_packet\<close>])
    val ((), markup) =
      Parser_Test_Reports.markup (fn () => Navigation.replay ctxt deferred)

    fun audit_mapping (name, token, type_name) =
      let
        val SOME entry = URust_Type_Mappings.lookup ctxt name
        val position = token_position text (start label) token 0
        val identity = Value.print_int (URust_Type_Mappings.entry_identity entry)
      in
        require (name ^ ": mapping reference did not link to its declaration")
          (entity_ids mapping_kind Markup.refN name position markup = [identity]);
        require (name ^ ": native HOL type navigation missing")
          (exists
            (fn (markup_name, properties) =>
              markup_name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME Markup.type_nameN andalso
              Properties.get properties Markup.nameN = SOME type_name andalso
              has_position properties position)
            markup);
        require (name ^ ": typing tooltip missing")
          (has_markup Markup.typingN position markup)
      end

    val _ =
      List.app audit_mapping
        [("signature::Header::Body", "Body", \<^type_name>\<open>result\<close>),
         ("SignatureOption", "SignatureOption", \<^type_name>\<open>option\<close>),
         ("SignaturePacket", "SignaturePacket", \<^type_name>\<open>signature_packet\<close>),
         ("u8", "u8", \<^type_name>\<open>word\<close>),
         ("bool", "bool", \<^type_name>\<open>bool\<close>)]
    val u8_position = token_position text (start label) "u8" 0
    val _ =
      require "primitive signature styling lost its lexical role"
        (has_markup Markup.keyword1N u8_position lexical_markup)

    val escape_label = "signature-native-hol-escape"
    val escape_text =
      "fn EscapeNavigation(value: \<tau>\<open>'a::linorder list\<close>) \
      \-> \<tau>\<open>'a list\<close> { value }"
    val escape_function = parse ctxt escape_label escape_text
    val ((_, escape_reports), escape_native_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.capture (fn () =>
          URust_Type_Mappings.resolve_signature ctxt (signature_types escape_function)))
    val ((), escape_deferred_markup) =
      Parser_Test_Reports.markup (fn () => Navigation.replay ctxt escape_reports)
    val escape_markup = escape_native_markup @ escape_deferred_markup
    val _ =
      require "HOL escape lost native type-variable markup"
        (has_markup Markup.tfreeN
          (token_position escape_text (start escape_label) "'a" 0) escape_markup)
    val _ =
      require "HOL escape lost native sort markup"
        (has_markup Markup.tclassN
          (token_position escape_text (start escape_label) "linorder" 0) escape_markup)
    val _ =
      require "HOL escape lost native type-constructor markup"
        (has_markup Markup.tconstN
          (token_position escape_text (start escape_label) "list" 0) escape_markup)

    fun positioned_failure (label, type_text, offending, expected) =
      let
        (* An Isabelle symbol before the type makes byte-counted ranges fail. *)
        val text =
          "fn Positioned(/* \<alpha> */ value: " ^ type_text ^ ") { () }"
        val function = parse ctxt label text
        val expected_position = token_position text (start label) offending 0
        val result =
          Exn.result
            (fn () => Navigation.capture (fn () =>
              URust_Type_Mappings.resolve_signature ctxt (signature_types function))) ()
        val diagnostic = message result
      in
        require (label ^ ": reason changed") (String.isSubstring expected diagnostic);
        require (label ^ ": diagnostic lost exact symbol-counted type range")
          (member (op =) (diagnostic_ranges diagnostic) (range_of expected_position))
      end

    val _ =
      List.app positioned_failure
        [("signature-position-unknown", "missing::PositionedType", "missing::PositionedType",
          "unknown Rust type"),
         ("signature-position-arity", "SignatureResult<u8>", "SignatureResult<u8>",
          "active urust_type mapping expects"),
         ("signature-position-sort", "SignatureOrdered<SignatureFunction>", "SignatureFunction",
          "does not satisfy sort"),
         ("signature-position-reference", "&u8", "&u8", "shared Rust references"),
         ("signature-position-zero-array", "[u8; 0]", "[u8; 0]", "does not satisfy sort"),
         ("signature-position-singleton", "(u8,)", "(u8,)", "singleton tuple types"),
         ("signature-position-numeric", "SignatureOption<4>", "4", "numeric generic arguments")]

    val base = initial \<^theory>
    val success_label = "signature-command-navigation"
    val success_text =
      command "" "signature_navigation_command"
        "fn SignatureNavigationCommand(value: SignatureCount) -> SignatureCount { value }"
    val (success, success_markup) =
      Parser_Test_Reports.markup
        (fn () => run_from base success_label success_text)
    val success_ctxt = Context_Position.set_visible true (Toplevel.context_of success)
    val SOME function_entry =
      Parser_Test_Calls.lookup success_ctxt "SignatureNavigationCommand"
    val declaration_position = (fn (entry: Micro_Rust_Names.entry) => #reg_pos entry) function_entry
    val _ =
      require "successful command lost native function declaration markup"
        (not (null
          (entity_ids "micro_rust_notation" Markup.defN "SignatureNavigationCommand"
            declaration_position success_markup)))
    val success_hol_name =
      Proof_Context.read_const {proper = true, strict = false}
        success_ctxt "signature_navigation_command"
      |> dest_Const_name
    val _ =
      require "registered Rust name lost native HOL declaration navigation"
        (exists
          (fn (name, properties) =>
            name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "constant" andalso
            Properties.get properties Markup.nameN = SOME success_hol_name andalso
            has_position properties declaration_position)
          success_markup)
    val _ =
      require "registered Rust name lost its declaration styling"
        (exists
          (fn (name, properties) =>
            name = Markup.keyword3N andalso has_position properties declaration_position)
          success_markup)
    val _ =
      require "successful command did not replay signature mapping reports"
        (length (entities mapping_kind success_markup) = 2)

    val client_label = "signature-command-call-navigation"
    val client_text =
      command "" "signature_navigation_client"
        "fn SignatureNavigationClient(value: SignatureCount) -> SignatureCount \
        \{ SignatureNavigationCommand(value) }"
    val (_, client_markup) =
      Parser_Test_Reports.markup
        (fn () => run_from success client_label client_text)
    val call_position =
      token_position client_text (start client_label) "SignatureNavigationCommand" 0
    val _ =
      require "registered signature function call lost its native reference"
        (entity_ids "micro_rust_notation" Markup.refN "SignatureNavigationCommand"
          call_position client_markup =
            entity_ids "micro_rust_notation" Markup.defN "SignatureNavigationCommand"
              declaration_position success_markup)

    val disabled_label = "signature-disabled-navigation"
    val disabled_text =
      command "[register_notation = false]" "signature_navigation_disabled"
        "fn SignatureNavigationDisabled(value: SignatureCount) -> SignatureCount { value }"
    val (disabled, disabled_markup) =
      Parser_Test_Reports.markup
        (fn () => run_from base disabled_label disabled_text)
    val _ =
      require "disabled registration emitted a function declaration entity"
        (null (entities "micro_rust_notation" disabled_markup))
    val _ =
      require "disabled registration suppressed signature type navigation"
        (length (entities mapping_kind disabled_markup) = 2)
    val disabled_ctxt = Toplevel.context_of disabled
    val disabled_hol_name =
      Proof_Context.read_const {proper = true, strict = false}
        disabled_ctxt "signature_navigation_disabled"
      |> dest_Const_name
    val disabled_rust_position =
      token_position disabled_text (start disabled_label) "SignatureNavigationDisabled" 0
    val _ =
      require "disabled registration suppressed native HOL declaration navigation"
        (exists
          (fn (name, properties) =>
            name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "constant" andalso
            Properties.get properties Markup.nameN = SOME disabled_hol_name andalso
            has_position properties disabled_rust_position)
          disabled_markup)

    fun optout_alias_navigation (label, options, hol_alias, rust_name, abbreviated) =
      let
        val text =
          command options hol_alias
            ("fn " ^ rust_name ^
              "(value: SignatureCount) -> SignatureCount { value }")
        val (state, reports) =
          Parser_Test_Reports.markup (fn () => run_from base label text)
        val alias_ctxt = Toplevel.context_of state
        val native_name = Proof_Context.intern_const alias_ctxt hol_alias
        val rust_position = token_position text (start label) rust_name 0
        val SOME (_, abbreviation_rhs) =
          AList.lookup (op =) (constant_snapshot alias_ctxt) native_name
        val has_def = can (Proof_Context.get_thm alias_ctxt) (hol_alias ^ "_def")
      in
        require (label ^ ": HOL alias artifact changed")
          (is_some abbreviation_rhs = abbreviated andalso has_def = not abbreviated);
        require (label ^ ": optout registered a Rust callable path")
          (is_none (Parser_Test_Calls.lookup alias_ctxt rust_name));
        require (label ^ ": optout emitted a synthetic function declaration")
          (null (entities "micro_rust_notation" reports));
        require (label ^ ": Rust name does not navigate to the explicit HOL alias")
          (exists
            (fn (name, properties) =>
              name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME "constant" andalso
              Properties.get properties Markup.nameN = SOME native_name andalso
              has_position properties rust_position)
            reports);
        registry_unchanged (label ^ " registries") (Toplevel.context_of base) alias_ctxt
      end

    val _ =
      List.app optout_alias_navigation
        [("signature-optout-definition-alias-navigation", "[register_notation = false]",
          "signature_optout_definition_alias", "SignatureOptoutDefinitionRustName", false),
         ("signature-optout-abbreviation-alias-navigation", "[abbrev, register_notation = false]",
          "signature_optout_abbreviation_alias", "SignatureOptoutAbbreviationRustName", true)]
  in
    val _ = ()
  end
\<close>

section\<open> Signature printer roundtrips \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>

    fun audit (label, text) =
      let
        val original = parse ctxt label text
        val printed =
          URust_Printer.string_of_function URust_Printer.serialized_options original
        val reparsed = parse ctxt (label ^ "-reparsed") printed
        val tokens = URust_Printer.tokens_of_function URust_Printer.serialized_options
        val original_types = resolve ctxt original
        val reparsed_types = resolve ctxt reparsed
        (* Type-variable indices may be fresh; the whole signature is compared together. *)
        fun signature_type types =
          types ---> \<^typ>\<open>unit\<close>
          |> Logic.varifyT_global
      in
        require (label ^ ": serialized signature token stream changed")
          (tokens original = tokens reparsed);
        require (label ^ ": signature slot count changed")
          (length original_types = length reparsed_types);
        require (label ^ ": mapped signature types changed")
          (Sign.typ_equiv (Proof_Context.theory_of ctxt)
            (signature_type original_types, signature_type reparsed_types))
      end

    val _ =
      List.app audit
        [("signature-roundtrip-custom",
          "fn RoundtripCustom(mut count: SignatureCount, _: signature::Flag) \
          \-> SignatureCount { count }"),
         ("signature-roundtrip-generics",
          "fn RoundtripGenerics(value: signature::Header<u8>::Body<\
          \SignatureResult<SignatureOption<u16>, bool>>) \
          \-> signature::Header<u8>::Body<SignatureResult<SignatureOption<u16>, bool>> { value }"),
         ("signature-roundtrip-tuples",
          "fn RoundtripTuples(value: (u8, (bool, SignatureCount), SignaturePacket)) \
          \-> (u8, (bool, SignatureCount), SignaturePacket) { value }"),
         ("signature-roundtrip-escapes",
          "fn RoundtripEscapes(operation: \<tau>\<open>'a \<Rightarrow> 'b\<close>, \
          \value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'b\<close> { \<llangle>operation value\<rrangle> }"),
         ("signature-roundtrip-sorts",
          "fn RoundtripSorts(value: SignatureOrdered<\<tau>\<open>'a::linorder\<close>>) \
          \-> SignatureOrdered<\<tau>\<open>'a\<close>> { value }"),
         ("signature-roundtrip-holes",
          "fn RoundtripHoles(value: SignatureOption<\<tau>\<open>_\<close>>) \
          \-> SignatureOption<u8> { value }"),
         ("signature-roundtrip-omitted", "fn RoundtripOmitted(value: u8) {}"),
         ("signature-roundtrip-inferred-result", "fn RoundtripInferred(value: u64) { value }"),
         ("signature-roundtrip-comments",
          "/* prefix */ fn RoundtripComments(value /* colon */ : \
          \SignatureResult</* first */ u8, // next\n bool,>,) \
          \-> SignatureResult<u8, bool> { value } // suffix")]
  in
    val _ = ()
  end
\<close>

section\<open> Registered call arity boundary \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val parameters = map (fn n => "p" ^ string_of_int n ^ ": u8") (1 upto 14)
    val function_text =
      command "" "signature_arity_fourteen"
        ("fn SignatureArityFourteen(" ^ commas parameters ^ ") -> u8 { p14 }")
    val with_function = run_from base "signature-arity-fourteen" function_text
    val function_ctxt = Toplevel.context_of with_function
    val _ =
      require "maximum callable signature lost ordered parameter slots"
        (binder_types (declared_type function_ctxt "signature_arity_fourteen") =
          replicate 14 \<^typ>\<open>8 word\<close>)
    val client =
      run_from with_function "signature-call-arity-fourteen"
        (command "" "signature_call_arity_fourteen"
          ("fn SignatureCallArityFourteen() -> u8 { SignatureArityFourteen(" ^
            commas (replicate 14 "1u8") ^ ") }"))
    val _ =
      require "maximum signature call did not lower through funcall14"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>funcall14\<close>
            | _ => false)
          (rhs (Toplevel.context_of client) "signature_call_arity_fourteen"))
    val failure =
      Exn.result
        (fn () =>
          run_from with_function "signature-call-arity-fifteen"
            (command "" "signature_call_arity_fifteen"
              ("fn SignatureCallArityFifteen() -> u8 { SignatureArityFourteen(" ^
                commas (replicate 15 "1u8") ^ ") }"))) ()
      |> message
    val _ =
      require "oversized signature call lost its positioned arity diagnostic"
        (String.isSubstring "unsupported call arity 15" failure andalso
          String.isSubstring "signature-call-arity-fifteen" failure)
    val _ =
      registry_unchanged "failed oversized call" function_ctxt
        (Toplevel.context_of with_function)
  in
    val _ = ()
  end
\<close>

section\<open> Overloadable registration and context merges \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val parent = \<^theory>
    val base = run_from (initial parent) "registration-same-name-selector"
      ("datatype_record signature_call_record = SignatureOverloaded :: " ^ cartouche " bool ")
    fun entries state = Parser_Test_Calls.entries (Toplevel.context_of state) "SignatureOverloaded"
    val first = run_from base "registration-first-backend"
      (command "" "signature_overloaded_word" "fn SignatureOverloaded(value: u8) -> u8 { value }")
    val second = run_from first "registration-second-backend"
      (command "" "signature_overloaded_bool" "fn SignatureOverloaded(value: bool) -> bool { value }")
    val _ = require "distinct types did not accumulate" (length (entries second) = 2)
    val clients = run_from second "registration-typed-clients"
      (command "[register_notation = false]" "signature_word_client"
         "fn WordClient(value: u8) -> u8 { SignatureOverloaded(value) }" ^ "\n" ^
       command "[register_notation = false]" "signature_bool_client"
         "fn BoolClient(value: bool) -> bool { value.SignatureOverloaded() }")
    val _ = require "direct call did not select the word backend"
      (Term.exists_subterm (fn Const (name, _) =>
        name = Proof_Context.intern_const (Toplevel.context_of clients) "signature_overloaded_word"
        | _ => false) (rhs (Toplevel.context_of clients) "signature_word_client"))
    val _ = require "method call did not select the bool backend"
      (Term.exists_subterm (fn Const (name, _) =>
        name = Proof_Context.intern_const (Toplevel.context_of clients) "signature_overloaded_bool"
        | _ => false) (rhs (Toplevel.context_of clients) "signature_bool_client"))
    val duplicate = run_from clients "registration-explicit-duplicate"
      "micro_rust_notation (call) signature_overloaded_word (\"SignatureOverloaded\")"
    val _ = require "duplicate explicit registration introduced ambiguity" (length (entries duplicate) = 2)
    val duplicate_wrapper = run_from duplicate "registration-wrapper-duplicate"
      "urust_notation (call) signature_overloaded_word (\"SignatureOverloaded\")"
    val _ = require "parser-aware duplicate introduced ambiguity" (length (entries duplicate_wrapper) = 2)
    val third = run_from duplicate_wrapper "registration-same-type-backend"
      (command "" "signature_overloaded_other_word" "fn SignatureOverloaded(value: u8) -> u8 { value }")
    val failure = Exn.result (fn () => run_from third "registration-ambiguous-client"
      (command "" "signature_ambiguous_client"
        "fn AmbiguousClient(value: u8) -> u8 { SignatureOverloaded(value) }")) () |> message
    val _ = require "indistinguishable backends did not reject at use"
      (String.isSubstring "Ambiguous uRust notation" failure andalso
        String.isSubstring "signature_overloaded_word" failure andalso
        String.isSubstring "signature_overloaded_other_word" failure)

    fun branch name options =
      let
        val thy = Theory.begin_theory (name, start name) [parent]
        val state = run_from (initial thy) name
          (command options "signature_merge_function"
            "fn SignatureMergeFunction(value: u8) -> u8 { value }")
      in Theory.end_theory (Toplevel.theory_of state) end
    fun merge name left right =
      Theory.begin_theory (name, start name) [left, right] |> Proof_Context.init_global
    val left = branch "Signature_Function_Merge_Left" ""
    val right = branch "Signature_Function_Merge_Right" ""
    val disabled = branch "Signature_Function_Merge_Disabled" "[register_notation = false]"
    val constructor = run_from
      (initial (Theory.begin_theory ("Signature_Function_Merge_Constructor", Position.none) [parent]))
      "registration-merge-constructor"
      ("urust_datatype signature_merge_constructor " ^ cartouche " struct SignatureMergeFunction; ")
      |> Toplevel.theory_of |> Theory.end_theory
    val named_constructor = run_from
      (initial (Theory.begin_theory ("Signature_Function_Merge_Named", Position.none) [parent]))
      "registration-merge-named-constructor"
      ("urust_datatype signature_merge_named " ^
        cartouche " struct SignatureMergeFunction { value: u8 } ")
      |> Toplevel.theory_of |> Theory.end_theory
    val _ = List.app (fn (label, a, b) =>
      require (label ^ ": overload union lost a backend")
        (length (Parser_Test_Calls.entries (merge label a b) "SignatureMergeFunction") = 2))
      [("Signature_Merge_Left_Right", left, right), ("Signature_Merge_Right_Left", right, left)]
    val _ = List.app (fn (label, a, b) =>
      let
        val failure = Exn.result (fn () =>
          let val ctxt = merge label a b
              val _ = Micro_Rust_Names.Declaration_Owners.get (Context.Proof ctxt)
          in () end) () |> message
      in require (label ^ ": constructor ownership did not reject")
        (String.isSubstring "already owned by a Rust constructor item" failure) end)
      [("Signature_Merge_Function_Constructor", left, constructor),
       ("Signature_Merge_Constructor_Function", constructor, left),
       ("Signature_Merge_Function_Named", left, named_constructor),
       ("Signature_Merge_Named_Function", named_constructor, left)]
    val _ = require "optout reserved constructor ownership"
      (is_some (URust_Item_Scope.lookup_constructor
        (merge "Signature_Merge_Disabled_Constructor" disabled constructor) "SignatureMergeFunction"))
    val _ = require "merge fixture leaked into parent" (null
      (Parser_Test_Calls.entries \<^context> "SignatureMergeFunction"))
  in val _ = () end
\<close>

section\<open> Shadow warnings at automatic calls \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    fun warnings_of label action =
      let
        val captured = Synchronized.var ("shadow_warnings_" ^ label) ([]: string list)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.warning_fn
              (fn chunks => Synchronized.change captured (append chunks)) action ())
      in (result, map (XML.content_of o YXML.parse_body) (Synchronized.value captured)) end
    (* Warning capture is process-wide, so each probe matches only its own name. *)
    fun ambiguous name =
      exists (String.isSubstring ("Ambiguous uRust notation \<open>" ^ name ^ "\<close>"))
    val base = initial \<^theory>
    (* The same-named HOL constant is the automatically registered backend itself. *)
    val (declared, declaration_warnings) = warnings_of "automatic-backend" (fn () =>
      run_from base "shadow-automatic-backend"
        (command "" "ShadowSameName" "fn ShadowSameName(value: u8) -> u8 { value }"))
    val (_, call_warnings) = warnings_of "automatic-call" (fn () =>
      run_from declared "shadow-automatic-call"
        (command "" "shadow_same_name_client"
          "fn ShadowSameNameClient(value: u8) -> u8 { ShadowSameName(value) }"))
    val _ = require "an automatic call warned about its own backend"
      (not (ambiguous "ShadowSameName" (declaration_warnings @ call_warnings)))
    (* An abbreviated function registers its expansion; the abbreviation itself is no shadow. *)
    val (abbreviated, _) = warnings_of "abbreviated-backend" (fn () =>
      run_from declared "shadow-abbreviated-backend"
        (command "[abbrev]" "ShadowAbbreviated" "fn ShadowAbbreviated(value: u8) -> u8 { value }"))
    val (_, abbreviated_call_warnings) = warnings_of "abbreviated-call" (fn () =>
      run_from abbreviated "shadow-abbreviated-call"
        (command "" "shadow_abbreviated_client"
          "fn ShadowAbbreviatedClient(value: u8) -> u8 { ShadowAbbreviated(value) }"))
    val _ = require "an abbreviated automatic call warned about its own backend"
      (not (ambiguous "ShadowAbbreviated" abbreviated_call_warnings))
    (* An explicit registration of a constant under its own name is no shadow either. *)
    val self_registered = run_from abbreviated "shadow-self-registration"
      (command "[register_notation = false]" "ShadowSelf"
         "fn ShadowSelfHelper(value: u8) -> u8 { value }" ^ "\n" ^
       "micro_rust_notation (call) ShadowSelf (\"ShadowSelf\")")
    val (_, self_warnings) = warnings_of "self-registered-call" (fn () =>
      run_from self_registered "shadow-self-registered-call"
        (command "[register_notation = false]" "shadow_self_client"
          "fn ShadowSelfClient(value: u8) -> u8 { ShadowSelf(value) }"))
    val _ = require "an explicit self-registration warned about its own backend"
      (not (ambiguous "ShadowSelf" self_warnings))
    (* An unregistered same-named HOL constant still shadows an explicit notation. *)
    val shadowed = run_from declared "shadow-unregistered-constant"
      (command "[register_notation = false]" "ShadowedConstant"
         "fn ShadowedConstantHelper(value: u8) -> u8 { value }" ^ "\n" ^
       "micro_rust_notation (call) ShadowSameName (\"ShadowedConstant\")")
    val (_, shadow_warnings) = warnings_of "unregistered-call" (fn () =>
      run_from shadowed "shadow-unregistered-call"
        (command "[register_notation = false]" "shadow_constant_client"
          "fn ShadowConstantClient(value: u8) -> u8 { ShadowedConstant(value) }"))
    val _ = require "an unregistered same-named constant lost its shadow warning"
      (ambiguous "ShadowedConstant" shadow_warnings)
  in val _ = () end
\<close>

section\<open> Repeated locale interpretations \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val first = run_from base "registration-first-locale"
      "interpretation signature_enabled_first: signature_registration_enabled 1\nby unfold_locales"
    val second = run_from first "registration-second-locale"
      "interpretation signature_enabled_second: signature_registration_enabled 2\nby unfold_locales"
    val _ = require "same-typed interpretations did not coexist"
      (length (Parser_Test_Calls.entries (Toplevel.context_of second) "SignatureRepeatedEnabled") = 2)
    val repeated_ambiguity = Exn.result (fn () => run_from second "registration-same-typed-locale-client"
      (command "[register_notation = false]" "signature_same_typed_locale_client"
        "fn SameTypedLocaleClient(value: SignatureCount) -> SignatureCount { SignatureRepeatedEnabled(value) }")) () |> message
    val _ = require "distinct same-typed locale operations were deduplicated"
      (String.isSubstring "Ambiguous uRust notation" repeated_ambiguity)
    val first_typed = run_from base "registration-nat-locale"
      ("interpretation signature_type_only_nat: signature_type_only_registration " ^
        quote "TYPE(nat)" ^ "\nby unfold_locales")
    val duplicate_typed = run_from first_typed "registration-duplicate-nat-locale"
      ("interpretation signature_type_only_nat_again: signature_type_only_registration " ^
        quote "TYPE(nat)" ^ "\nby unfold_locales")
    val _ = require "identical interpretation was not deduplicated"
      (length (Parser_Test_Calls.entries (Toplevel.context_of duplicate_typed)
        "SignatureTypeOnlyFunction") = 1)
    val both_typed = run_from duplicate_typed "registration-bool-locale"
      ("interpretation signature_type_only_bool: signature_type_only_registration " ^
        quote "TYPE(bool)" ^ "\nby unfold_locales")
    val ctxt = Toplevel.context_of both_typed
    val _ = require "typed interpretation was lost by untyped deduplication"
      (length (Parser_Test_Calls.entries ctxt "SignatureTypeOnlyFunction") = 2)
    val clients = run_from both_typed "registration-locale-clients"
      (command "[register_notation = false]" "signature_nat_locale_client"
         "fn NatLocaleClient(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { SignatureTypeOnlyFunction(value) }" ^ "\n" ^
       command "[register_notation = false]" "signature_bool_locale_client"
         "fn BoolLocaleClient(value: bool) -> bool { SignatureTypeOnlyFunction(value) }")
    val _ = List.app (fn name => ignore (theorem (Toplevel.context_of clients) name))
      ["signature_nat_locale_client", "signature_bool_locale_client"]
    val _ = require "disabled locale interpretations registered"
      (null (Parser_Test_Calls.entries \<^context> "SignatureRepeatedLocale"))
  in val _ = () end
\<close>

section\<open> Schematic replay, independent calls and fixed ambient types \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = Named_Target.theory_init \<^theory>
    val identity = Const (\<^const_name>\<open>signature_plain_identity\<close>,
      declared_type base "signature_plain_identity") |> Term_Subst.zero_var_indexes
    val index_ten = Term.map_types (Logic.incr_tvar 10) identity
    val index_hundred = Term.map_types (Logic.incr_tvar 100) identity
    fun register term position ctxt = Parser_Test_Calls.declare
      {rust_name = "SignatureSchematicReplay", rust_pos = start position, function = term} ctxt
    val polymorphic_duplicate = run_from (initial \<^theory>) "registration-polymorphic-explicit-duplicate"
      ("micro_rust_notation (call) " ^ cartouche
        " signature_plain_identity :: 'renamed \<Rightarrow> ('effects, 'renamed, 'abort, 'input, 'output) function_body " ^
        " (\"SignaturePlainIdentity\")")
    val _ = require "alpha-renamed explicit registration duplicates automatic polymorphic backend"
      (length (Parser_Test_Calls.entries (Toplevel.context_of polymorphic_duplicate)
        "SignaturePlainIdentity") = 1)
    val specialized_duplicate = run_from polymorphic_duplicate "registration-specialized-explicit-duplicate"
      ("micro_rust_notation (call) " ^ cartouche
        " signature_plain_identity :: nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body " ^
        " (\"SignaturePlainIdentity\")")
    val _ = require "specialized explicit registration duplicates a covering polymorphic backend"
      (length (Parser_Test_Calls.entries (Toplevel.context_of specialized_duplicate)
        "SignaturePlainIdentity") = 1)
    val specialized = Syntax.read_term base
      "signature_plain_identity :: nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
    fun register_coverage term context =
      Micro_Rust_Names.register Micro_Rust_Names.NFunction "SignatureCoverageReplay"
        term Position.none context
    val generic_then_concrete = Context.Theory \<^theory>
      |> register_coverage identity |> register_coverage specialized
    val concrete_then_generic = Context.Theory \<^theory>
      |> register_coverage specialized |> register_coverage identity
    val _ = List.app (fn context => require "specialization duplicate depends on registration order"
      (length (Parser_Test_Calls.entries (Context.proof_of context) "SignatureCoverageReplay") = 1))
      [generic_then_concrete, concrete_then_generic]
    fun branch name term =
      Theory.begin_theory (name, Position.none) [\<^theory>] |> Context.Theory
      |> register_coverage term |> Context.the_theory |> Theory.end_theory
    val generic_branch = branch "Signature_Coverage_Generic" identity
    val concrete_branch = branch "Signature_Coverage_Concrete" specialized
    fun check_merge (name, left, right) =
      let
        val ctxt = Theory.begin_theory (name, Position.none) [left, right]
          |> Proof_Context.init_global
        val _ = require "merge equality lost distinct typed schemes"
          (length (Micro_Rust_Names.registrations ctxt Micro_Rust_Names.NFunction
            "SignatureCoverageReplay") = 2)
        val _ = require "the merged view does not show the covering scheme alone"
          (map (Micro_Rust_Names.normalized_backend o #hol_term)
             (Parser_Test_Calls.entries ctxt "SignatureCoverageReplay") =
           [Micro_Rust_Names.normalized_backend identity])
        val compatible = Micro_Rust_Dispatch.candidates ctxt Micro_Rust_Names.NFunction
          "SignatureCoverageReplay" (fastype_of specialized)
        val _ = require "generic/specialized theory union creates ambiguity"
          (length compatible = 1)
        val checked_call = Parser_Test_Elaboration.function ctxt
          {raw_type = ("nat \<Rightarrow> (_, nat, _, _, _) function_body", Position.none),
           parameters = [("value", Position.none)], parameters_pos = Position.none,
           body = source (name ^ "-body") "SignatureCoverageReplay(value)"}
        val (_, checked_result, _, _, _) = channels (fastype_of checked_call)
        val _ = require "merged generic/specialized call failed elaboration"
          (checked_result = \<^typ>\<open>nat\<close>)
      in () end
    val _ = List.app check_merge
      [("Signature_Coverage_Generic_Concrete", generic_branch, concrete_branch),
       ("Signature_Coverage_Concrete_Generic", concrete_branch, generic_branch)]
    val first = register index_ten "registration-replay-ten" base
    val repeated_indices = register index_hundred "registration-replay-hundred" first
    val renamed = Term.map_types (Term.map_atyps
      (fn TVar ((name, index), sort) => TVar ((name ^ "_renamed", index), sort) | typ => typ)) identity
    val repeated = register renamed "registration-replay-renamed" repeated_indices
    val _ = registry_unchanged "schematic-index replay" first repeated
    val first_call = Micro_Rust_Dispatch.fresh_backend repeated identity
    val second_call = Micro_Rust_Dispatch.fresh_backend repeated identity
    val _ = require "calls share signature or effect inference variables"
      (not (exists (member (op =) (Term.add_tvars second_call [])) (Term.add_tvars first_call [])))
    val mixed_call = Parser_Test_Elaboration.function repeated
      {raw_type = ("8 word \<Rightarrow> bool \<Rightarrow> (_, 8 word \<times> bool \<times> tnil, _, _, _) function_body",
         start "registration-independent-type"),
       parameters = [("value", Position.none), ("flag", Position.none)],
       parameters_pos = Position.none,
       body = source "registration-independent-body"
         "(SignatureSchematicReplay(value), SignatureSchematicReplay(flag))"}
    val (_, mixed_result, _, _, _) = channels (fastype_of mixed_call)
    val _ = require "one registration did not instantiate independently"
      (mixed_result = \<^typ>\<open>8 word \<times> bool \<times> tnil\<close>)
    fun ambient_call (locale_name, required_sort) =
      let
        val ambient_ctxt = Named_Target.init [] (Locale.intern \<^theory> locale_name) \<^theory>
        val ambient = Syntax.read_typ ambient_ctxt "'a"
        val value_type = hd (binder_types (fastype_of identity))
        val rigid = Term.map_types (Term.typ_subst_atomic [(value_type, ambient)]) identity
        val rigid_ctxt = Parser_Test_Calls.declare
          {rust_name = "SignatureStoredRigid", rust_pos = Position.none, function = rigid} ambient_ctxt
        val successful = Parser_Test_Elaboration.function rigid_ctxt
          {raw_type = ("'a \<Rightarrow> (_, 'a, _, _, _) function_body", Position.none),
           parameters = [("value", Position.none)], parameters_pos = Position.none,
           body = source "registration-rigid-body" "SignatureStoredRigid(value)"}
        val (_, result, _, _, _) = channels (fastype_of successful)
        val _ = require "ambient fixed type lost rigidity or sort"
          (result = ambient andalso Sign.subsort (Proof_Context.theory_of rigid_ctxt)
            (sort_of ambient, required_sort))
        val rejected = Exn.result (fn () => Parser_Test_Elaboration.function rigid_ctxt
          {raw_type = ("(_, bool, _, _, _) function_body", Position.none), parameters = [],
           parameters_pos = Position.none,
           body = source "registration-rigid-reject" "SignatureStoredRigid(true)"}) () |> message
        val _ = require "ambient fixed type was generalized at dispatch"
          (String.isSubstring "no backend matches" rejected orelse String.isSubstring "Type" rejected)
      in () end
    val _ = List.app ambient_call [("signature_type_only_registration", \<^sort>\<open>type\<close>),
      ("signature_ordered_ambient", \<^sort>\<open>linorder\<close>)]
  in val _ = () end
\<close>

section\<open> Method-only marks, backend filters and dispatch payloads \<close>

definition registry_filter_word :: \<open>8 word \<Rightarrow> ('s, 8 word, 'a, 'i, 'o) function_body\<close> where
  \<open>registry_filter_word value = FunctionBody (literal value)\<close>

definition registry_filter_other_word ::
  \<open>8 word \<Rightarrow> ('s, 8 word, 'a, 'i, 'o) function_body\<close> where
  \<open>registry_filter_other_word value = FunctionBody (literal value)\<close>

definition registry_filter_bool :: \<open>bool \<Rightarrow> ('s, bool, 'a, 'i, 'o) function_body\<close> where
  \<open>registry_filter_bool value = FunctionBody (literal value)\<close>

definition registry_filter_nat :: \<open>nat \<Rightarrow> ('s, nat, 'a, 'i, 'o) function_body\<close> where
  \<open>registry_filter_nat value = FunctionBody (literal value)\<close>

ML \<open>
(* Registrations in the shapes of the impl registration path, made directly through the registry. *)
structure Parser_Registry_Test =
struct
  structure Names = Micro_Rust_Names

  fun range label offset =
    Position.make0 1 offset (offset + 4) "" label ""
    |> Position.copy_id (Position.thread_data ())

  fun backend ctxt name =
    Const (Proof_Context.intern_const ctxt name,
      Parser_Function_Regression_Test.declared_type ctxt name)

  fun register name term s =
    Names.register_with_source_serial Names.NFunction name term NONE (range name 1) s

  val explicit = register
  fun generated name term s = Names.mark_automatic s #> register name term s
  fun method name term s =
    Names.mark_automatic s #> Names.mark_method_only s #> register name term s

  fun entries ctxt name = Names.lookups ctxt Names.NFunction name

  fun serials entries = sort int_ord (map #serial entries)

  fun eligible ctxt filters name =
    serials (Names.eligible_entries ctxt filters (entries ctxt name))

  fun filters_of (Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ payload $ _) =
        #4 (the (Micro_Rust_Dispatch.dest_payload payload))
    | filters_of _ = error "expected a dispatch marker"

  fun position_key position =
    (Position.offset_of position, Position.end_offset_of position, Position.id_of position)

  fun positions_key ({terminal_pos, qualifier_positions, backend_only_positions}:
      Micro_Rust_Dispatch.marker_positions) =
    (position_key terminal_pos, map position_key qualifier_positions,
     map position_key backend_only_positions)

  fun owners ctxt name =
    Names.associated_functions ctxt name
    |> map (fn {self_type, identity, pos} => (identity, self_type, position_key pos))
    |> sort (int_ord o apply2 #1)

  fun self_types ctxt name =
    map #2 (owners ctxt name) |> sort Term_Ord.typ_ord

  (* Everything a client can observe about one key, with dispatch at an occurrence type. *)
  fun observe concrete ctxt key originals =
    let
      val filter_sets =
        [[], [Names.Exclude_Generated], [Names.Exclude_Method_Only],
         [Names.Only_Sources originals]]
    in
      (entries ctxt key
       |> map (fn entry =>
            (#serial entry, Names.is_automatic ctxt entry, Names.is_method_only ctxt entry,
             apsnd position_key (Names.navigation_target ctxt entry),
             position_key (#reg_pos entry)))
       |> sort (int_ord o apply2 #1),
       map (fn filters => Names.has_eligible_entries ctxt filters Names.NFunction key)
         filter_sets,
       map (fn filters =>
           serials (map #entry
             (Micro_Rust_Dispatch.filtered_candidates ctxt filters Names.NFunction key
               concrete)))
         filter_sets,
       map (Pretty.pure_string_of o Micro_Rust_Notation_Print.pretty_entry ctxt)
         (filter (fn (_, name, _) => name = key) (Names.dump ctxt)) |> sort_strings)
    end
end
\<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    structure Dispatch = Micro_Rust_Dispatch
    val word = backend \<^context> "registry_filter_word"
    val other_word = backend \<^context> "registry_filter_other_word"
    val bool = backend \<^context> "registry_filter_bool"
    val nat = backend \<^context> "registry_filter_nat"
    val method_word = serial ()
    val method_bool = serial ()
    val generated_word = serial ()
    val generated_bool = serial ()
    val explicit_word = serial ()
    val explicit_bool = serial ()
    val mixed_method = serial ()
    val mixed_generated = serial ()
    val mixed_explicit = serial ()
    val mixed_other = serial ()
    val ctxt =
      Context.Proof \<^context>
      |> method "RegistryMethodOnly" word method_word
      |> method "RegistryMethodOnly" bool method_bool
      |> generated "RegistryGenerated" word generated_word
      |> generated "RegistryGenerated" bool generated_bool
      |> explicit "RegistryExplicit" word explicit_word
      |> explicit "RegistryExplicit" bool explicit_bool
      |> method "RegistryMixed" word mixed_method
      |> generated "RegistryMixed" bool mixed_generated
      |> explicit "RegistryMixed" nat mixed_explicit
      |> explicit "RegistryMixed" other_word mixed_other
      |> Context.proof_of

    (* Marks. *)
    fun status name = map (fn entry =>
        (#serial entry, Names.is_automatic ctxt entry, Names.is_method_only ctxt entry))
      (entries ctxt name) |> sort (int_ord o apply2 #1)
    val _ = require "method-only marks"
      (status "RegistryMixed" =
        sort (int_ord o apply2 #1)
          [(mixed_method, true, true), (mixed_generated, true, false),
           (mixed_explicit, false, false), (mixed_other, false, false)])
    val _ = require "plain automatic or explicit entries are method-only"
      (forall (not o #3) (status "RegistryGenerated" @ status "RegistryExplicit"))
    val _ = require "method entries lost their marks"
      (forall (fn (_, automatic, method_only) => automatic andalso method_only)
        (status "RegistryMethodOnly"))

    (* Eligibility under every filter, combination and source list. *)
    val sources = Names.Only_Sources
    val _ = List.app (fn (label, filters, expected) =>
        require ("eligible entries: " ^ label) (eligible ctxt filters "RegistryMixed" =
          sort int_ord expected))
      [("none", [], [mixed_method, mixed_generated, mixed_explicit, mixed_other]),
       ("generated", [Names.Exclude_Generated], [mixed_explicit, mixed_other]),
       ("method-only", [Names.Exclude_Method_Only], [mixed_generated, mixed_explicit, mixed_other]),
       ("one source", [sources [mixed_method]], [mixed_method]),
       ("several sources", [sources [mixed_method, mixed_explicit, generated_word]],
          [mixed_method, mixed_explicit]),
       ("no sources", [sources []], []),
       ("generated and method-only", [Names.Exclude_Generated, Names.Exclude_Method_Only],
          [mixed_explicit, mixed_other]),
       ("method-only and sources", [Names.Exclude_Method_Only, sources [mixed_method, mixed_generated]],
          [mixed_generated]),
       ("generated and sources", [Names.Exclude_Generated, sources [mixed_generated]], []),
       ("two source sets intersect", [sources [mixed_method, mixed_other], sources [mixed_other]],
          [mixed_other])]

    (* Report-free existence of eligible entries. *)
    fun has filters name = Names.has_eligible_entries ctxt filters Names.NFunction name
    val _ = List.app (fn (label, filters, name, expected) =>
        require ("has_eligible_entries: " ^ label) (has filters name = expected))
      [("all method-only, unfiltered", [], "RegistryMethodOnly", true),
       ("all method-only, direct call", [Names.Exclude_Method_Only], "RegistryMethodOnly", false),
       ("all method-only, turbofish", [Names.Exclude_Generated], "RegistryMethodOnly", false),
       ("all generated, direct call", [Names.Exclude_Method_Only], "RegistryGenerated", true),
       ("all generated, turbofish", [Names.Exclude_Generated], "RegistryGenerated", false),
       ("mixed, direct call", [Names.Exclude_Method_Only], "RegistryMixed", true),
       ("mixed, both exclusions", [Names.Exclude_Generated, Names.Exclude_Method_Only],
          "RegistryMixed", true),
       ("mixed, method source only, direct call",
          [Names.Exclude_Method_Only, sources [mixed_method]], "RegistryMixed", false),
       ("mixed, no sources", [sources []], "RegistryMixed", false),
       ("explicit only, turbofish", [Names.Exclude_Generated], "RegistryExplicit", true),
       ("explicit only, direct call", [Names.Exclude_Method_Only], "RegistryExplicit", true),
       ("unregistered", [], "RegistryUnregistered", false)]
    val _ = require "has_eligible_entries emitted reports"
      (null (snd (Parser_Test_Reports.markup (fn () =>
        has [Names.Exclude_Method_Only] "RegistryMethodOnly"))))

    (* Payload encoding round-trips every filter set, with and without reported positions. *)
    val positions =
      {terminal_pos = range "registry-payload-terminal" 20,
       qualifier_positions = [range "registry-payload-qualifier" 10],
       backend_only_positions = [range "registry-payload-backend" 30]}
    val no_positions =
      {terminal_pos = Position.none, qualifier_positions = [], backend_only_positions = []}
    val filter_sets =
      [[], [Names.Exclude_Generated], [Names.Exclude_Method_Only], [sources [mixed_method]],
       [sources [mixed_method, mixed_other, 7]], [sources []],
       [Names.Exclude_Method_Only, Names.Exclude_Generated],
       [Names.Exclude_Generated, sources [3, 1, 2], Names.Exclude_Method_Only, sources []]]
    fun round_trip label marker_positions filters =
      (case Dispatch.dest_payload
          (Dispatch.mk_filtered_payload_positions filters Names.NFunction "Registry::Path"
            marker_positions) of
         SOME (kind, name, decoded, decoded_filters) =>
           require ("payload round trip: " ^ label)
             (kind = Names.NFunction andalso name = "Registry::Path" andalso
              positions_key decoded = positions_key marker_positions andalso
              decoded_filters = filters)
       | NONE => error "payload was not recognized")
    val _ = List.app (round_trip "positions" positions) filter_sets
    val _ = List.app (round_trip "no positions" no_positions) filter_sets
    val _ = require "an unfiltered payload changed its encoding"
      (Dispatch.mk_filtered_payload_positions [] Names.NFunction "Registry::Path" positions =
        Dispatch.mk_payload_positions Names.NFunction "Registry::Path" positions)

    (* restrict_backends rewrites every marker of a call head and accumulates filters. *)
    val marker = Dispatch.mk_marker_term NONE
      (Dispatch.mk_payload_positions Names.NFunction "RegistryMixed" positions)
    val witness_marker =
      Dispatch.mk_marker_positions Names.NFunction "RegistryMixed"
        (#terminal_pos positions) [] (Free ("RegistryMixed", dummyT))
    val _ = require "restriction by no filter changed the marker"
      (Dispatch.restrict_backends [] marker = marker)
    val _ = List.app (fn filters =>
        require "restriction did not install its filters"
          (filters_of (Dispatch.restrict_backends filters marker) = filters))
      filter_sets
    val accumulated =
      marker |> Dispatch.restrict_backends [sources [mixed_method]]
      |> Dispatch.restrict_backends [Names.Exclude_Method_Only, sources [mixed_method]]
      |> Dispatch.exclude_generated_backends
    val _ = require "restrictions did not accumulate in order"
      (filters_of accumulated =
        [sources [mixed_method], Names.Exclude_Method_Only, Names.Exclude_Generated])
    val _ = require "turbofish entry point is not the generated exclusion"
      (Dispatch.exclude_generated_backends marker =
        Dispatch.restrict_backends [Names.Exclude_Generated] marker)
    val restricted_witness = Dispatch.restrict_backends [Names.Exclude_Method_Only] witness_marker
    val _ = require "restriction lost the witness or positions"
      (case restricted_witness of
         Const _ $ payload $ (Const (\<^const_name>\<open>Witness\<close>, _) $ Free ("RegistryMixed", _)) =>
           positions_key (#3 (the (Dispatch.dest_payload payload))) =
             positions_key {terminal_pos = #terminal_pos positions, qualifier_positions = [],
               backend_only_positions = []}
       | _ => false)
    val head = Abs ("x", dummyT, marker $ (witness_marker $ Bound 0))
    fun markers (t as Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ _ $ _) = [t]
      | markers (t $ u) = markers t @ markers u
      | markers (Abs (_, _, body)) = markers body
      | markers _ = []
    val _ = require "a nested marker was not restricted"
      (map filters_of (markers (Dispatch.restrict_backends [Names.Exclude_Method_Only] head)) =
        [[Names.Exclude_Method_Only], [Names.Exclude_Method_Only]])

    (* Dispatch considers exactly the eligible backends. *)
    val any_type = TVar (("'occurrence", 0), [])
    fun candidates filters typ =
      serials (map #entry (Dispatch.filtered_candidates ctxt filters Names.NFunction
        "RegistryMixed" typ))
    val word_type = fastype_of word
    val _ = List.app (fn (label, filters, typ, expected) =>
        require ("dispatch candidates: " ^ label) (candidates filters typ = sort int_ord expected))
      [("none", [], any_type, [mixed_method, mixed_generated, mixed_explicit, mixed_other]),
       ("generated", [Names.Exclude_Generated], any_type, [mixed_explicit, mixed_other]),
       ("method-only", [Names.Exclude_Method_Only], any_type,
          [mixed_generated, mixed_explicit, mixed_other]),
       ("sources", [sources [mixed_generated, mixed_other]], any_type,
          [mixed_generated, mixed_other]),
       ("no sources", [sources []], any_type, []),
       ("word, none", [], word_type, [mixed_method, mixed_other]),
       ("word, method-only", [Names.Exclude_Method_Only], word_type, [mixed_other]),
       ("word, method source", [sources [mixed_method]], word_type, [mixed_method])]
    fun dispatch filters typ =
      Navigation.capture (fn () =>
        Syntax.check_term ctxt
          (Type.constraint typ (Dispatch.mk_marker_term NONE
            (Dispatch.mk_filtered_payload_positions filters Names.NFunction "RegistryMixed"
              positions)))) |> fst
    val concrete_word = \<^typ>\<open>8 word \<Rightarrow> (unit, 8 word, unit, unit, unit) function_body\<close>
    val concrete_bool = \<^typ>\<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
    fun selects label filters typ name =
      require ("dispatch selection: " ^ label)
        (case Type.strip_constraints (dispatch filters typ) of
           Const (selected, _) => selected = name
         | _ => false)
    val _ = selects "method-only exclusion resolves the overload" [Names.Exclude_Method_Only]
      concrete_word \<^const_name>\<open>registry_filter_other_word\<close>
    val _ = selects "source selection resolves the overload" [sources [mixed_method]]
      concrete_word \<^const_name>\<open>registry_filter_word\<close>
    val _ = selects "generated bool backend without filters" [] concrete_bool
      \<^const_name>\<open>registry_filter_bool\<close>
    val ambiguous = Exn.result (fn () => dispatch [] concrete_word) () |> message
    val _ = require "unfiltered same-typed backends were not ambiguous"
      (String.isSubstring "Ambiguous uRust notation" ambiguous)
    val excluded = Exn.result (fn () => dispatch [Names.Exclude_Generated] concrete_bool) ()
      |> message
    val _ = require "excluded generated backend was dispatched"
      (String.isSubstring "no backend matches the use-site type" excluded andalso
        String.isSubstring "Generic arguments exclude generated functions" excluded andalso
        not (String.isSubstring "registry_filter_bool" excluded))
    val empty_sources = Exn.result (fn () => dispatch [sources []] concrete_word) () |> message
    val _ = require "an empty source list dispatched"
      (String.isSubstring "no backend matches the use-site type" empty_sources)
  in val _ = () end
\<close>

section\<open> Explicit registrations replace covering automatic entries \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    val word = backend \<^context> "registry_filter_word"
    (* Automatic entries in the shapes of an impl member: a path entry and a method-only entry. *)
    fun automatic_with name term method_only s state =
      let
        val thy = Toplevel.theory_of state |> Context.Theory
          |> (if method_only then method name term s else generated name term s)
          |> Context.the_theory
      in initial thy end
    fun automatic name term method_only state =
      automatic_with name term method_only (serial ()) state
    fun explicit_command name backend_name state =
      run_from state ("registry-explicit-" ^ name)
        ("micro_rust_notation (call) " ^ backend_name ^ " (" ^ quote name ^ ")")
    val status_ord =
      prod_ord bool_ord (prod_ord bool_ord string_ord) o
        (fn ((a, b, c), (d, e, f)) => ((a, (b, c)), (d, (e, f))))
    fun stored state name = map (fn entry =>
        (Names.is_automatic (Toplevel.context_of state) entry,
         Names.is_method_only (Toplevel.context_of state) entry,
         Term.head_of (#hol_term entry) |> dest_Const_name))
      (entries (Toplevel.context_of state) name)
      |> sort status_ord
    val word_name = \<^const_name>\<open>registry_filter_word\<close>
    val bool_name = \<^const_name>\<open>registry_filter_bool\<close>
    val base = initial \<^theory>
    fun check (key, method_only) =
      let
        val auto_status = (true, method_only)
        fun expect label state expected =
          require (key ^ ": " ^ label) (stored state key = sort status_ord expected)
        val after_serial = serial ()
        val after = base |> automatic_with key word method_only after_serial
          |> explicit_command key "registry_filter_word"
        val _ = expect "explicit after automatic, same backend" after [(false, false, word_name)]
        val prior = base |> explicit_command key "registry_filter_word"
          |> automatic key word method_only
        val _ = expect "explicit before automatic, same backend" prior [(false, false, word_name)]
        val other_after = base |> automatic key word method_only
          |> explicit_command key "registry_filter_bool"
        val _ = expect "explicit after automatic, other backend" other_after
          [(#1 auto_status, #2 auto_status, word_name), (false, false, bool_name)]
        val other_before = base |> explicit_command key "registry_filter_bool"
          |> automatic key word method_only
        val _ = expect "explicit before automatic, other backend" other_before
          [(#1 auto_status, #2 auto_status, word_name), (false, false, bool_name)]
        val replayed = after |> explicit_command key "registry_filter_word"
          |> automatic_with key word method_only after_serial
        val _ = expect "replays after the replacement" replayed [(false, false, word_name)]
      in () end
    val _ = List.app check [("RegistryReplace::get", false), ("registry_replace_get", true)]

    (* A specialization that an automatic scheme covers does not cover it, so nothing is replaced. *)
    val identity_name = \<^const_name>\<open>signature_plain_identity\<close>
    val generic = Const (identity_name, declared_type \<^context> "signature_plain_identity")
    val specialized = base |> automatic "RegistryReplaceGeneric" generic false
      |> (fn state => run_from state "registry-explicit-specialization"
        ("micro_rust_notation (call) " ^ cartouche
          " signature_plain_identity :: nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body " ^
          " (\"RegistryReplaceGeneric\")"))
    val _ = require "a covered explicit specialization replaced its automatic scheme"
      (stored specialized "RegistryReplaceGeneric" = [(true, false, identity_name)])

    (* Turbofish reaches the explicit registration that replaced the generated function. *)
    val declared = run_from base "registry-turbofish-function"
      (command "" "registry_turbo" "fn RegistryTurbo(first: u8, second: u8) -> u8 { second }")
    val generated_only = Exn.result (fn () => run_from declared "registry-turbofish-generated"
      ("urust_expr registry_turbo_generated " ^ cartouche " RegistryTurbo::<1>(2u8) ")) ()
      |> message
    val _ = require "turbofish reached a generated function"
      (String.isSubstring "generic arguments are not supported on generated Rust function paths"
        generated_only)
    val replaced = run_from declared "registry-turbofish-explicit"
      ("micro_rust_notation (call) registry_turbo (\"RegistryTurbo\")\n" ^
       "micro_rust_notation (call) registry_turbo (\"RegistryTurboExplicitOnly\")\n" ^
       "urust_expr registry_turbo_explicit " ^ cartouche " RegistryTurbo::<1>(2u8) " ^ "\n" ^
       "urust_expr registry_turbo_control " ^ cartouche " RegistryTurboExplicitOnly::<1>(2u8) " ^
       "\n" ^
       "urust_expr registry_turbo_plain " ^ cartouche " RegistryTurbo(1, 2u8) ")
    val replaced_ctxt = Toplevel.context_of replaced
    val _ = require "turbofish after an explicit-after-automatic registration did not dispatch"
      (stored replaced "RegistryTurbo" =
        [(false, false, Proof_Context.intern_const replaced_ctxt "registry_turbo")] andalso
       Term.aconv (rhs replaced_ctxt "registry_turbo_explicit",
         rhs replaced_ctxt "registry_turbo_control"))
    val _ = require "the plain call lost the replaced function"
      (Term.exists_subterm (fn Const (name, _) =>
          name = Proof_Context.intern_const replaced_ctxt "registry_turbo"
        | _ => false) (rhs replaced_ctxt "registry_turbo_plain"))
  in val _ = () end
\<close>

section\<open> Order-independent registration view \<close>

text\<open>
Every registry fact visible to clients is a function of the set of registrations: an explicit
registration before or after an automatic one, or strictly covering it, gives the same view
within one theory and across sibling branches merged in either order.
\<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    structure Dispatch = Micro_Rust_Dispatch
    val word = backend \<^context> "registry_filter_word"
    val word_unit =
      Const (\<^const_name>\<open>registry_filter_word\<close>,
        \<^typ>\<open>8 word \<Rightarrow> (unit, 8 word, unit, unit, unit) function_body\<close>)
    val concrete = fastype_of word_unit
    fun extend name parents declaration =
      Theory.begin_theory (name, Position.none) parents |> Context.Theory |> declaration
      |> Context.the_theory |> Theory.end_theory
    fun merge name theories =
      Theory.begin_theory (name, Position.none) theories |> Proof_Context.init_global

    (* One scenario: an automatic registration and an explicit one of a key, in every order. *)
    fun scenario label key method_only automatic_term explicit_term expected =
      let
        val automatic_serial = serial ()
        val explicit_serial = serial ()
        val explicit_pos = range ("registry-view-" ^ label) 10
        val add_automatic =
          (if method_only then method else generated) key automatic_term automatic_serial
        val add_explicit =
          Names.register_with_source_serial Names.NFunction key explicit_term NONE explicit_pos
            explicit_serial
        fun name suffix = "Registry_View_" ^ label ^ "_" ^ suffix
        val after = extend (name "After") [\<^theory>] (add_automatic #> add_explicit)
        val prior = extend (name "Before") [\<^theory>] (add_explicit #> add_automatic)
        val common = extend (name "Common") [\<^theory>] add_automatic
        val replacing = extend (name "Replacing") [common] add_explicit
        val untouched = extend (name "Untouched") [common] I
        val explicit_branch = extend (name "Explicit") [\<^theory>] add_explicit
        val automatic_branch = extend (name "Automatic") [\<^theory>] add_automatic
        fun view theories =
          observe concrete (merge (name "View") theories) key [automatic_serial]
        val reference = view [after]
        val variants =
          [("explicit before automatic", [prior]),
           ("explicit after automatic, replacing branch", [replacing]),
           ("explicit after automatic, replacing then untouched", [replacing, untouched]),
           ("explicit after automatic, untouched then replacing", [untouched, replacing]),
           ("explicit before automatic, explicit then automatic sibling",
              [explicit_branch, automatic_branch]),
           ("explicit before automatic, automatic then explicit sibling",
              [automatic_branch, explicit_branch])]
        val _ = List.app (fn (variant, theories) =>
            require (label ^ ": " ^ variant ^ " changed the view") (view theories = reference))
          variants
        val _ = require (label ^ ": unexpected view")
          (reference = expected automatic_serial explicit_serial (position_key explicit_pos))
        val untouched_view = view [untouched]
        val _ = require (label ^ ": the untouched branch is not automatic")
          (map #2 (#1 untouched_view) = [true] andalso map #3 (#1 untouched_view) = [method_only])
      in () end

    fun row key tags = key ^ " \<longmapsto> registry_filter_word  (" ^ commas ("function" :: tags) ^ ")"
    fun same_backend key a e pos =
      ([(a, false, false, (e, pos), pos)], [true, true, true, true], [[a], [a], [a], [a]],
       [row key []])
    fun strict_covering key a e pos =
      ([(a, false, false, (e, pos), pos), (e, false, false, (e, pos), pos)],
       [true, true, true, true], [[e], [e], [e], [a]], [row key [], row key []])
    val _ = scenario "Same_Path" "RegistryView::get" false word word
      (same_backend "RegistryView::get")
    val _ = scenario "Same_Method" "registry_view_get" true word word
      (same_backend "registry_view_get")
    val _ = scenario "Covering_Path" "RegistryViewCovering::get" false word_unit word
      (strict_covering "RegistryViewCovering::get")
    val _ = scenario "Covering_Method" "registry_view_covering_get" true word_unit word
      (strict_covering "registry_view_covering_get")

    (* Status is computed under the entry's own key: an explicit registration of the same backend
       under another key changes nothing, and a serial cannot name registrations of two keys. *)
    val shared = serial ()
    val keyed = Context.Proof \<^context>
      |> generated "RegistryViewKeyed::get" word shared
      |> explicit "registry_view_keyed_get" word (serial ())
    val _ = require "an explicit registration under another key changed the status"
      (forall (Names.is_automatic (Context.proof_of keyed))
        (entries (Context.proof_of keyed) "RegistryViewKeyed::get"))
    val reused = Exn.result (fn () => keyed |> register "registry_view_keyed_other" word shared) ()
      |> message
    val _ = require "a serial was registered under two keys"
      (String.isSubstring "registration serial is reused under" reused)

    (* Two branches that register the same backend explicitly agree in either merge order. *)
    val path_key = "RegistryViewTwo::get"
    val automatic_serial = serial ()
    val first_explicit = serial ()
    val second_explicit = serial ()
    val common = extend "Registry_View_Two_Common" [\<^theory>]
      (generated path_key word automatic_serial)
    fun explicit_at s offset =
      Names.register_with_source_serial Names.NFunction path_key word NONE
        (range "registry-view-two" offset) s
    val first = extend "Registry_View_Two_First" [common] (explicit_at first_explicit 10)
    val second = extend "Registry_View_Two_Second" [common] (explicit_at second_explicit 30)
    fun target theories =
      let val ctxt = merge "Registry_View_Two" theories
      in apsnd position_key (Names.navigation_target ctxt (the_single (entries ctxt path_key))) end
    val _ = require "the covering explicit registration depends on merge order"
      (target [first, second] = target [second, first] andalso
       target [first, second] = (first_explicit, position_key (range "registry-view-two" 10)))

    (* The impl identity still selects a path entry registered explicitly with its own backend. *)
    val identity = serial ()
    val identity_ctxt =
      Context.Proof \<^context>
      |> Names.reserve_associated_function
           {name = "RegistryIdentity::get", self_type = \<^typ>\<open>8 word\<close>, identity = identity,
            pos = range "registry-identity" 40}
      |> generated "RegistryIdentity::get" word identity
      |> explicit "RegistryIdentity::get" word (serial ())
      |> Context.proof_of
    val _ = require "Only_Sources lost an impl after an explicit same-backend registration"
      (Names.has_eligible_entries identity_ctxt [Names.Only_Sources [identity]] Names.NFunction
         "RegistryIdentity::get" andalso
       map #serial (entries identity_ctxt "RegistryIdentity::get") = [identity] andalso
       map #identity (Names.associated_functions identity_ctxt "RegistryIdentity::get") =
         [identity])
    val selected = Navigation.capture (fn () =>
      Syntax.check_term identity_ctxt
        (Type.constraint concrete (Dispatch.mk_marker_term NONE
          (Dispatch.mk_filtered_payload_positions [Names.Only_Sources [identity]]
            Names.NFunction "RegistryIdentity::get"
            {terminal_pos = Position.none, qualifier_positions = [],
             backend_only_positions = []})))) |> fst |> Type.strip_constraints
    val _ = require "identity selection did not dispatch to the explicitly registered entry"
      (case selected of
         Const (name, _) => name = \<^const_name>\<open>registry_filter_word\<close>
       | _ => false)
  in val _ = () end
\<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    (* Ordinary commands: a locale function registered automatically by interpretation, and an
       explicit call notation of a backend that covers the instance, before or after it. *)
    fun branch name parents text =
      Theory.begin_theory (name, Position.none) parents |> initial
      |> (fn state => if text = "" then state else run_from state name text)
      |> Toplevel.theory_of |> Theory.end_theory
    val located = branch "Registry_Commands_Locale" [\<^theory>]
      ("locale registry_view_locale =\n  fixes registry_view_witness :: " ^
         cartouche " 'a itself " ^ "\nbegin\n" ^
       command "[register_notation]" "registry_view_turbo"
         "fn RegistryViewTurbo(first: u8, second: u8) -> u8 { second }" ^ "\n" ^
       command "[register_notation]" "registry_view_id"
         "fn RegistryViewId(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { value }" ^ "\nend")
    val explicit_text =
      "micro_rust_notation (call) registry_view_locale.registry_view_turbo " ^
        "(\"RegistryViewTurbo\")\n" ^
      "micro_rust_notation (call) registry_view_locale.registry_view_turbo " ^
        "(\"RegistryViewTurboOnly\")\n" ^
      "micro_rust_notation (call) registry_view_locale.registry_view_id (\"RegistryViewId\")"
    fun interpretation label =
      "interpretation " ^ label ^ ": registry_view_locale " ^ quote "TYPE(nat)" ^
        "\nby unfold_locales"
    val automatic_branch = branch "Registry_Commands_Automatic" [located]
      (interpretation "registry_commands_automatic")
    val explicit_branch = branch "Registry_Commands_Explicit" [located] explicit_text
    val after = branch "Registry_Commands_After" [automatic_branch] explicit_text
    val prior = branch "Registry_Commands_Before" [explicit_branch]
      (interpretation "registry_commands_before")
    val untouched = branch "Registry_Commands_Untouched" [automatic_branch]
      ("definition registry_commands_unrelated where " ^
        cartouche " registry_commands_unrelated = () ")
    fun theory_of theories = Theory.begin_theory ("Registry_Commands_View", Position.none) theories
    val automatic_ctxt = Proof_Context.init_global automatic_branch
    val turbo_serial = #serial (the_single (entries automatic_ctxt "RegistryViewTurbo"))
    val id_serial = #serial (the_single (entries automatic_ctxt "RegistryViewId"))
    val nat_id = \<^typ>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
    fun check label theories =
      let
        val thy = theory_of theories
        val ctxt = Proof_Context.init_global thy
        val turbo = the_single (entries ctxt "RegistryViewTurbo")
        val ids = entries ctxt "RegistryViewId"
        val _ = require (label ^ ": the same-backend entry changed")
          (#serial turbo = turbo_serial andalso not (Names.is_automatic ctxt turbo) andalso
           fst (Names.navigation_target ctxt turbo) <> turbo_serial andalso
           Names.has_eligible_entries ctxt [Names.Only_Sources [turbo_serial]] Names.NFunction
             "RegistryViewTurbo")
        val _ = require (label ^ ": the strictly covered entry changed")
          (length ids = 2 andalso member (op =) (map #serial ids) id_serial andalso
           forall (not o Names.is_automatic ctxt) ids andalso
           Names.has_eligible_entries ctxt [Names.Only_Sources [id_serial]] Names.NFunction
             "RegistryViewId" andalso
           map (#serial o #entry)
             (Micro_Rust_Dispatch.filtered_candidates ctxt [] Names.NFunction "RegistryViewId"
               nat_id) <> [id_serial])
        val state = run_from (initial thy) label
          ("urust_expr registry_view_turbofish " ^
             cartouche " RegistryViewTurbo::<1>(2u8) " ^ "\n" ^
           "urust_expr registry_view_control " ^ cartouche " RegistryViewTurboOnly::<1>(2u8) ")
        val state_ctxt = Toplevel.context_of state
      in
        require (label ^ ": turbofish did not reach the explicit registration")
          (Term.aconv (rhs state_ctxt "registry_view_turbofish",
            rhs state_ctxt "registry_view_control"))
      end
    val _ = List.app (fn (label, theories) => check label theories)
      [("registry-commands-after", [after]),
       ("registry-commands-before", [prior]),
       ("registry-commands-after-untouched", [after, untouched]),
       ("registry-commands-untouched-after", [untouched, after]),
       ("registry-commands-explicit-automatic", [explicit_branch, automatic_branch]),
       ("registry-commands-automatic-explicit", [automatic_branch, explicit_branch])]
    val generated_only = Exn.result (fn () =>
      run_from (initial (theory_of [untouched])) "registry-commands-generated-only"
        ("urust_expr registry_view_generated " ^ cartouche " RegistryViewTurbo::<1>(2u8) ")) ()
      |> message
    val _ = require "the automatic branch accepted generic arguments on a generated function"
      (String.isSubstring "generic arguments are not supported on generated Rust function paths"
        generated_only)
  in val _ = () end
\<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    (* A generated function, an explicit call notation of the same backend in one branch, an
       unrelated sibling branch, and a turbofish call in their merge, in both import orders. *)
    fun branch name parents text =
      Theory.begin_theory (name, Position.none) parents |> initial
      |> (fn state => if text = "" then state else run_from state name text)
      |> Toplevel.theory_of |> Theory.end_theory
    val common = branch "Registry_Turbofish_Common" [\<^theory>]
      (command "" "registry_diamond_turbo"
        "fn RegistryDiamondTurbo(first: u8, second: u8) -> u8 { second }")
    val replacing = branch "Registry_Turbofish_Replacing" [common]
      ("micro_rust_notation (call) registry_diamond_turbo (\"RegistryDiamondTurbo\")\n" ^
       "micro_rust_notation (call) registry_diamond_turbo (\"RegistryDiamondTurboOnly\")")
    val sibling = branch "Registry_Turbofish_Sibling" [common]
      ("definition registry_turbofish_unrelated where " ^
        cartouche " registry_turbofish_unrelated = () ")
    fun turbofish label theories =
      let
        val state =
          run_from (initial (Theory.begin_theory (label, Position.none) theories)) label
            ("urust_expr registry_diamond_turbofish " ^
               cartouche " RegistryDiamondTurbo::<1>(2u8) " ^ "\n" ^
             "urust_expr registry_diamond_control " ^
               cartouche " RegistryDiamondTurboOnly::<1>(2u8) ")
        val ctxt = Toplevel.context_of state
      in
        require (label ^ ": turbofish did not reach the explicit registration")
          (Term.aconv (rhs ctxt "registry_diamond_turbofish", rhs ctxt "registry_diamond_control"))
      end
    val _ = turbofish "Registry_Turbofish_Replacing_Only" [replacing]
    val _ = turbofish "Registry_Turbofish_Replacing_Sibling" [replacing, sibling]
    val _ = turbofish "Registry_Turbofish_Sibling_Replacing" [sibling, replacing]
    val generated_only = Exn.result (fn () =>
      turbofish "Registry_Turbofish_Sibling_Only" [sibling]) () |> message
    val _ = require "the sibling branch accepted generic arguments on a generated function"
      (String.isSubstring "generic arguments are not supported on generated Rust function paths"
        generated_only)
  in val _ = () end
\<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    val word = backend \<^context> "registry_filter_word"
    val word_unit =
      Const (\<^const_name>\<open>registry_filter_word\<close>,
        \<^typ>\<open>8 word \<Rightarrow> (unit, 8 word, unit, unit, unit) function_body\<close>)
    val concrete = fastype_of word_unit
    fun extend name parents declaration =
      Theory.begin_theory (name, Position.none) parents |> Context.Theory |> declaration
      |> Context.the_theory |> Theory.end_theory
    fun merge name theories =
      Theory.begin_theory (name, Position.none) theories |> Proof_Context.init_global
    fun explicit_at key term s offset =
      Names.register_with_source_serial Names.NFunction key term NONE
        (range ("registry-follow-up-" ^ key) offset) s

    (* Review 03 probe P7b: an automatic entry covered by an explicit registration of its own
       backend and by a strictly covering one navigates to the maximal one everywhere. *)
    val key = "RegistryCovers::get"
    val automatic_serial = serial ()
    val same_serial = serial ()
    val covering_serial = serial ()
    val common = extend "Registry_Covers_Common" [\<^theory>]
      (generated key word_unit automatic_serial)
    val add_same = explicit_at key word_unit same_serial 10
    val add_covering = explicit_at key word covering_serial 30
    val same_then_covering = extend "Registry_Covers_Same_First" [common]
      (add_same #> add_covering)
    val covering_then_same = extend "Registry_Covers_Covering_First" [common]
      (add_covering #> add_same)
    val same_branch = extend "Registry_Covers_Same" [common] add_same
    val covering_branch = extend "Registry_Covers_Covering" [common] add_covering
    fun view theories =
      observe concrete (merge "Registry_Covers_View" theories) key [automatic_serial]
    val reference = view [same_then_covering]
    val covering_pos = position_key (range ("registry-follow-up-" ^ key) 30)
    val _ = List.app (fn (label, theories) =>
        require ("P7b " ^ label ^ " changed the view") (view theories = reference))
      [("covering first", [covering_then_same]),
       ("siblings, same first", [same_branch, covering_branch]),
       ("siblings, covering first", [covering_branch, same_branch])]
    val _ = require "P7b: the automatic entry does not navigate to the maximal registration"
      (#1 reference =
        [(automatic_serial, false, false, (covering_serial, covering_pos), covering_pos),
         (covering_serial, false, false, (covering_serial, covering_pos), covering_pos)] andalso
       #3 reference =
        [[covering_serial], [covering_serial], [covering_serial], [automatic_serial]])

    (* Review 03 probe P7a: explicit registrations without an automatic one, either identical
       or strictly covering, give the same view in one theory, in both insertion orders, and
       across siblings in both merge orders: only the preferred registration is visible. *)
    fun explicit_pair label lower_term upper_term expected =
      let
        val pair_key = "RegistryPair" ^ label ^ "::get"
        val lower = serial ()
        val upper = serial ()
        val add_lower = explicit_at pair_key lower_term lower 10
        val add_upper = explicit_at pair_key upper_term upper 20
        fun name suffix = "Registry_Pair_" ^ label ^ "_" ^ suffix
        val lower_first = extend (name "Lower_First") [\<^theory>] (add_lower #> add_upper)
        val upper_first = extend (name "Upper_First") [\<^theory>] (add_upper #> add_lower)
        val lower_branch = extend (name "Lower") [\<^theory>] add_lower
        val upper_branch = extend (name "Upper") [\<^theory>] add_upper
        fun pair_view theories =
          observe concrete (merge (name "View") theories) pair_key [lower, upper]
        val reference = pair_view [lower_first]
        val _ = List.app (fn (variant, theories) =>
            require ("P7a " ^ label ^ ": " ^ variant ^ " changed the view")
              (pair_view theories = reference))
          [("upper first", [upper_first]),
           ("siblings, lower first", [lower_branch, upper_branch]),
           ("siblings, upper first", [upper_branch, lower_branch])]
        fun stored theories =
          Names.registrations (merge (name "Raw") theories) Names.NFunction pair_key
          |> map #serial |> sort int_ord
        val _ = List.app (fn theories =>
            require ("P7a " ^ label ^ ": the stored registrations depend on the layout")
              (stored theories = sort int_ord [lower, upper]))
          [[lower_first], [upper_first], [lower_branch, upper_branch],
           [upper_branch, lower_branch]]
      in
        require ("P7a " ^ label ^ ": unexpected view")
          (reference = expected pair_key lower upper
            (position_key (range ("registry-follow-up-" ^ pair_key) 10))
            (position_key (range ("registry-follow-up-" ^ pair_key) 20)))
      end
    fun pair_row pair_key = pair_key ^ " \<longmapsto> registry_filter_word  (function)"
    val _ = explicit_pair "Identical" word word (fn pair_key => fn lower => fn _ => fn pos => fn _ =>
      ([(lower, false, false, (lower, pos), pos)], [true, true, true, true],
       [[lower], [lower], [lower], [lower]], [pair_row pair_key]))
    val _ = explicit_pair "Covering" word_unit word (fn pair_key => fn _ => fn upper => fn _ =>
      fn pos =>
        ([(upper, false, false, (upper, pos), pos)], [true, true, true, true],
         [[upper], [upper], [upper], [upper]], [pair_row pair_key]))

    (* A serial reused under two keys in sibling branches is the same positioned error in either
       merge order, and the error on insertion names both uses as well. *)
    val reused = serial ()
    val path_pos = range "registry-reuse-path" 50
    val bare_pos = range "registry-reuse-bare" 60
    val path_branch = extend "Registry_Reuse_Path" [\<^theory>]
      (Names.register_with_source_serial Names.NFunction "RegistryReuse::get" word NONE path_pos
        reused)
    val bare_branch = extend "Registry_Reuse_Bare" [\<^theory>]
      (Names.register_with_source_serial Names.NFunction "registry_reuse_get" word NONE bare_pos
        reused)
    fun reuse_failure theories =
      Exn.result (fn () => merge "Registry_Reuse_Merge" theories) () |> message
    val failures =
      [reuse_failure [path_branch, bare_branch], reuse_failure [bare_branch, path_branch]]
    fun names_both failure =
      String.isSubstring "urust: notation registration serial is reused under" failure andalso
      String.isSubstring (quote "RegistryReuse::get") failure andalso
      String.isSubstring (quote "registry_reuse_get") failure andalso
      forall (member (op =) (diagnostic_ranges failure) o range_of) [path_pos, bare_pos]
    val _ = require "serial reuse across branches is not one positioned error"
      (forall names_both failures andalso nth failures 0 = nth failures 1)
    val inserted = Exn.result (fn () =>
      Context.Theory path_branch
      |> Names.register_with_source_serial Names.NFunction "registry_reuse_get" word NONE
        bare_pos reused) () |> message
    val _ = require "serial reuse on insertion differs from the merge error"
      (inserted = nth failures 0)
  in val _ = () end
\<close>

section\<open> Associated-function owners \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    val key = "RegistryAssoc::get"
    fun reserve name self_type identity pos =
      Names.reserve_associated_function
        {name = name, self_type = self_type, identity = identity, pos = pos}
    val first_pos = range "registry-assoc-first" 10
    val second_pos = range "registry-assoc-second" 20
    val third_pos = range "registry-assoc-third" 30
    val first = serial ()
    val second = serial ()
    val third = serial ()
    val base = Context.Theory \<^theory>
    val nat_list = \<^typ>\<open>nat list\<close>
    val bool_list = \<^typ>\<open>bool list\<close>
    fun list_of T = Type (\<^type_name>\<open>list\<close>, [T])
    val generic_list = list_of (TFree ("'a", \<^sort>\<open>type\<close>))
    fun ctxt_of context = Context.proof_of context

    (* Replays with the same identity are idempotent, also after schematic renaming. *)
    val reserved = base |> reserve key nat_list first first_pos
    val replayed = reserved |> reserve key nat_list first second_pos
    val _ = require "a same-identity replay added an owner"
      (owners (ctxt_of replayed) key = [(first, nat_list, position_key first_pos)])
    val generic_reserved = base |> reserve key generic_list first first_pos
    val generic_replayed = generic_reserved
      |> reserve key (list_of (TVar (("'renamed", 7), \<^sort>\<open>type\<close>))) first second_pos
    val _ = require "a renamed schematic replay added an owner"
      (length (owners (ctxt_of generic_replayed) key) = 1)
    val _ = require "a theory-level Self type was not generalized"
      (case self_types (ctxt_of generic_reserved) key of
         [Type (\<^type_name>\<open>list\<close>, [TVar _])] => true
       | _ => false)

    (* The lookup lists every owner with its identity, Self type and position. *)
    val both = reserved |> reserve key bool_list second second_pos
    val _ = require "associated_functions lost an owner"
      (owners (ctxt_of both) key =
        [(first, nat_list, position_key first_pos), (second, bool_list, position_key second_pos)])
    val _ = require "is_associated_function"
      (Names.is_associated_function (ctxt_of both) key andalso
       not (Names.is_associated_function (ctxt_of both) "RegistryAssoc::missing"))
    val _ = require "a key without owners listed owners"
      (null (Names.associated_functions (ctxt_of both) "RegistryAssoc::missing"))
    val function_owned = both |> Names.reserve_declaration Names.Function_Declaration
      "RegistryAssoc::free" first_pos
    val _ = require "a function owner is an associated function"
      (not (Names.is_associated_function (ctxt_of function_owned) "RegistryAssoc::free"))
    val _ = require "associated_functions emitted reports"
      (null (snd (Parser_Test_Reports.markup (fn () =>
        Names.associated_functions (ctxt_of both) key))))

    (* Different identities conflict exactly when their Self types unify. *)
    fun conflict label context =
      let
        val failure = Exn.result (fn () => ignore (context ())) () |> message
      in
        require (label ^ ": overlapping impls were accepted")
          (String.isSubstring "is defined in more than one impl with overlapping Self types"
            failure);
        failure
      end
    fun reports_both label failure positions =
      require (label ^ ": conflict lost a position")
        (forall (member (op =) (diagnostic_ranges failure) o range_of) positions)
    val same = conflict "same Self type" (fn () => reserved |> reserve key nat_list third third_pos)
    val _ = reports_both "same Self type" same [first_pos, third_pos]
    val generic = conflict "generic Self type"
      (fn () => reserved |> reserve key generic_list third third_pos)
    val _ = reports_both "generic Self type" generic [first_pos, third_pos]
    val generic_first = conflict "generic owner first"
      (fn () => generic_reserved |> reserve key nat_list third third_pos)
    val _ = reports_both "generic owner first" generic_first [first_pos, third_pos]
    val accepted = both |> reserve key \<^typ>\<open>nat option\<close> third third_pos
    val _ = require "non-unifiable Self types were rejected"
      (length (owners (ctxt_of accepted) key) = 3)

    (* Associated functions conflict with constructor owners in both orders. *)
    fun constructor_conflict label context =
      require (label ^ ": constructor ownership did not reject")
        (String.isSubstring "already owned by a Rust constructor item"
          (Exn.result (fn () => ignore (context ())) () |> message))
    val _ = constructor_conflict "associated first" (fn () =>
      reserved |> Names.reserve_declaration Names.Constructor_Declaration key second_pos)
    val _ = constructor_conflict "constructor first" (fn () =>
      base |> Names.reserve_declaration Names.Constructor_Declaration key second_pos
      |> reserve key nat_list first first_pos)
  in val _ = () end
\<close>

section\<open> Merged and interpreted impl-member registrations \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    val key = "MergeCell::get"
    val left = \<^theory>\<open>Parser_Test_Fixtures_Left\<close>
    val right = \<^theory>\<open>Parser_Test_Fixtures_Right\<close>
    val parent = \<^theory>\<open>Parser_Test_Fixtures\<close>
    fun merge name theories =
      Theory.begin_theory (name, Position.none) theories |> Proof_Context.init_global
    fun marks ctxt name =
      map (fn entry => (Names.is_automatic ctxt entry, Names.is_method_only ctxt entry))
        (entries ctxt name)

    (* Owners and marks of the two branches survive theory merge in both orders. *)
    val left_owner = the_single (Names.associated_functions (Proof_Context.init_global left) key)
    val right_owner = the_single (Names.associated_functions (Proof_Context.init_global right) key)
    val branch_types = sort Term_Ord.typ_ord [\<^typ>\<open>nat list\<close>, \<^typ>\<open>bool list\<close>]
    fun merged_ok ctxt =
      (require "merged owners differ from the union of the branches"
         (self_types ctxt key = branch_types andalso
          map #1 (owners ctxt key) = sort int_ord [#identity left_owner, #identity right_owner]);
       require "merged method entries lost their marks"
         (marks ctxt "merge_cell_get" = [(true, true), (true, true)]);
       require "merged path entries changed their marks"
         (marks ctxt key = [(true, false), (true, false)]))
    val left_right = merge "Registry_Merge_Left_Right" [left, right]
    val right_left = merge "Registry_Merge_Right_Left" [right, left]
    val _ = List.app merged_ok [left_right, right_left, \<^context>]
    val _ = require "merge order changed the owners"
      (owners left_right key = owners right_left key)

    (* An overlapping impl or a constructor of another branch is rejected in both merge orders. *)
    fun branch name declaration =
      Theory.begin_theory (name, Position.none) [parent] |> Context.Theory |> declaration
      |> Context.the_theory |> Theory.end_theory
    val overlapping_pos = range "registry-merge-overlapping" 40
    val overlapping = branch "Registry_Merge_Overlapping"
      (Names.reserve_associated_function
        {name = key, self_type = Type (\<^type_name>\<open>list\<close>, [TFree ("'a", \<^sort>\<open>type\<close>)]),
         identity = serial (), pos = overlapping_pos})
    val disjoint = branch "Registry_Merge_Disjoint"
      (Names.reserve_associated_function
        {name = key, self_type = \<^typ>\<open>nat option\<close>, identity = serial (),
         pos = range "registry-merge-disjoint" 50})
    val constructor = branch "Registry_Merge_Constructor"
      (Names.reserve_declaration Names.Constructor_Declaration key
        (range "registry-merge-constructor" 60))
    fun rejected label theories needle =
      let
        val failure = Exn.result (fn () =>
          Names.associated_functions (merge label theories) key) () |> message
      in
        require (label ^ ": merge did not reject") (String.isSubstring needle failure);
        failure
      end
    val overlap = "is defined in more than one impl with overlapping Self types"
    val failures =
      [rejected "Registry_Merge_Left_Overlapping" [left, overlapping] overlap,
       rejected "Registry_Merge_Overlapping_Left" [overlapping, left] overlap]
    val _ = List.app (fn failure =>
        require "merge conflict lost a position"
          (String.isSubstring (Position.here (#pos left_owner)) failure andalso
           member (op =) (diagnostic_ranges failure) (range_of overlapping_pos)))
      failures
    val _ = require "merge conflict depends on merge order" (nth failures 0 = nth failures 1)
    val _ = List.app (fn (label, theories) =>
        ignore (rejected label theories "already owned by a Rust constructor item"))
      [("Registry_Merge_Left_Constructor", [left, constructor]),
       ("Registry_Merge_Constructor_Left", [constructor, left])]
    val _ = List.app (fn (label, theories) =>
        require (label ^ ": disjoint Self types were rejected")
          (length (owners (merge label theories) key) = 3))
      [("Registry_Merge_Disjoint_Both", [left, right, disjoint]),
       ("Registry_Merge_Both_Disjoint", [disjoint, right, left])]

    (* Locale interpretations morph the Self type: differently typed instances of one impl are
       accepted and same-typed replays are idempotent. *)
    val locale_key = "RegistryLocalePair::get"
    val located = run_from (initial \<^theory>) "registry-assoc-locale"
      ("locale registry_assoc_locale =\n  fixes registry_assoc_witness :: " ^
        cartouche " 'a itself ")
    val locale_thy = Toplevel.theory_of located
    val identity = serial ()
    val member_pos = range "registry-assoc-locale-member" 70
    val locale_lthy =
      Named_Target.init [] (Locale.intern locale_thy "registry_assoc_locale") locale_thy
    val self_type = Syntax.read_typ locale_lthy "'a list"
    val declared = locale_lthy
      |> Local_Theory.declaration {pervasive = false, syntax = false, pos = member_pos}
        (fn phi => Names.reserve_associated_function
          {name = locale_key, self_type = Morphism.typ phi self_type, identity = identity,
           pos = member_pos})
    val _ = require "the locale owner lost its fixed Self type"
      (self_types declared locale_key = [self_type])
    val interpreted_thy = Local_Theory.exit_global declared
    val _ = require "a locale owner leaked into the theory"
      (null (owners (Proof_Context.init_global interpreted_thy) locale_key))
    fun interpret state label instance =
      run_from state label
        ("interpretation " ^ label ^ ": registry_assoc_locale " ^ quote instance ^
          "\nby unfold_locales")
    val nat_state = interpret (initial interpreted_thy) "registry_assoc_nat" "TYPE(nat)"
    val nat_again = interpret nat_state "registry_assoc_nat_again" "TYPE(nat)"
    val bool_state = interpret nat_again "registry_assoc_bool" "TYPE(bool)"
    val _ = require "an interpretation did not register its instance"
      (self_types (Toplevel.context_of nat_state) locale_key = [\<^typ>\<open>nat list\<close>])
    val _ = require "a same-typed interpretation was not idempotent"
      (self_types (Toplevel.context_of nat_again) locale_key = [\<^typ>\<open>nat list\<close>])
    val _ = require "differently typed interpretations of one impl were not accepted"
      (map #1 (owners (Toplevel.context_of bool_state) locale_key) = [identity, identity] andalso
       self_types (Toplevel.context_of bool_state) locale_key = branch_types)
    val _ = require "an interpreted instance lost the member position"
      (forall (fn state =>
          forall (fn (_, _, pos) => pos = position_key member_pos)
            (owners (Toplevel.context_of state) locale_key))
        [nat_state, nat_again, bool_state] andalso
       map #3 (owners declared locale_key) = [position_key member_pos])
    val overlapping_instance = Exn.result (fn () =>
      Toplevel.theory_of bool_state |> Context.Theory
      |> Names.reserve_associated_function
        {name = locale_key, self_type = \<^typ>\<open>nat list\<close>, identity = serial (),
         pos = range "registry-assoc-locale-overlap" 80}) () |> message
    val _ = require "another impl overlapping an interpreted instance was accepted"
      (String.isSubstring overlap overlapping_instance)
  in val _ = () end
\<close>

section\<open> Notation listing tags \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    open Parser_Registry_Test
    val word = backend \<^context> "registry_filter_word"
    val ctxt =
      Context.Proof \<^context>
      |> generated "RegistryPrint::get" word (serial ())
      |> method "registry_print_get" word (serial ())
      |> explicit "RegistryPrintExplicit" word (serial ())
      |> Context.proof_of
    val names = ["RegistryPrint::get", "registry_print_get", "RegistryPrintExplicit"]
    val lines =
      Names.dump ctxt
      |> filter (fn (_, name, _) => member (op =) names name)
      |> map (Pretty.pure_string_of o Micro_Rust_Notation_Print.pretty_entry ctxt)
      |> sort_strings
    val expected = sort_strings
      ["RegistryPrint::get \<longmapsto> registry_filter_word  (function, generated)",
       "registry_print_get \<longmapsto> registry_filter_word  (function, generated, method-only)",
       "RegistryPrintExplicit \<longmapsto> registry_filter_word  (function)"]
    val _ = require ("notation listing tags: " ^ commas_quote lines) (lines = expected)
    val listing = Pretty.pure_string_of (Micro_Rust_Notation_Print.pretty_notations ctxt)
    val _ = require "the notation listing omitted a tagged entry"
      (forall (fn line => String.isSubstring line listing) expected)
  in val _ = () end
\<close>

chapter\<open> Semantic function types \<close>

section\<open> Full declaration types and kernel equalities \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun same_type name expected =
      require (name ^ ": full declaration type changed")
        (Sign.typ_equiv (Proof_Context.theory_of ctxt)
          (declared_type ctxt name, Logic.varifyT_global expected))
    val _ =
      same_type "semantic_identity"
        \<^typ>\<open>nat \<Rightarrow>
          ('s::cancellative_sepalg, nat, bool, nat prompt, unit prompt_output) function_body\<close>
    val _ =
      same_type "semantic_unused_callback"
        \<^typ>\<open>nat \<Rightarrow> (nat \<Rightarrow> ('s::cancellative_sepalg, unit, 'abort, 'i, 'o) function_body) \<Rightarrow>
          ('s, nat, 'abort, 'i, 'o) function_body\<close>
    val _ =
      same_type "semantic_fixed_caller"
        \<^typ>\<open>nat \<Rightarrow> (unit, nat, bool, nat prompt, unit prompt_output) function_body\<close>
    val (state, _, abort, input, output) =
      channels (declared_type ctxt "semantic_polymorphic_identity")
    val _ = independent "unannotated channels no longer generalize" [state, abort, input, output]
  in val _ = () end
\<close>

section\<open> Holes, shared names and independent call instances \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    val typ = declared_type ctxt "semantic_channel_sharing"
    val (state, result, abort, input, output) = channels typ
    val _ = require "channel and signature names did not share" (result = abort andalso
      binder_types typ = [result] andalso input = output)
    val _ = require "shared channel sort was lost"
      (Sign.subsort (Proof_Context.theory_of ctxt) (sort_of result, \<^sort>\<open>linorder\<close>))
    val _ = independent "unrelated shared names were captured" [state, result, input]
    val holes = declared_type ctxt "semantic_sorted_holes"
    val (s, r, a, i, o') = channels holes
    val _ = require "omitted result is not unit" (r = \<^typ>\<open>unit\<close>)
    val _ = independent "sorted holes became identified" (binder_types holes @ [s, a, i, o'])
    val _ =
      List.app (fn (typ, expected) =>
        require "channel hole lost its sort"
          (Sign.subsort (Proof_Context.theory_of ctxt) (sort_of typ, expected)))
        [(s, \<^sort>\<open>cancellative_sepalg\<close>), (a, \<^sort>\<open>linorder\<close>),
         (i, \<^sort>\<open>finite\<close>), (o', \<^sort>\<open>order\<close>)]
  in val _ = () end
\<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    val typ = declared_type ctxt "semantic_independent_holes"
    val [left, right] = binder_types typ
    val (state, result, abort, input, output) = channels typ
    val _ = require "result is not connected to the used parameter" (left = result)
    val _ = require "concrete abort was lost" (abort = \<^typ>\<open>bool\<close>)
    val _ = independent "independent annotation holes became identified" [left, right, state, input, output]
    val _ = require "signature variable names failed to share"
      (hd (binder_types (declared_type ctxt "semantic_shared_names")) =
        #2 (channels (declared_type ctxt "semantic_shared_names")))
    val _ = require "semantic type synonym changed the full declaration scheme"
      (Sign.typ_equiv (Proof_Context.theory_of ctxt)
        (declared_type ctxt "semantic_synonym_identity", declared_type ctxt "semantic_identity"))
    val pointer_type = declared_type ctxt "semantic_pointer_identity"
    val _ = require "annotation lost a pointer backend parameter"
      (Sign.typ_equiv (Proof_Context.theory_of ctxt)
        (pointer_type, Logic.varifyT_global
          \<^typ>\<open>('addr, 'global, 8 word) Global_Store.ref \<Rightarrow>
            ('s::cancellative_sepalg, ('addr, 'global, 8 word) Global_Store.ref,
              bool, nat prompt, unit prompt_output) function_body\<close>))
  in val _ = () end
\<close>

section\<open> Locale fixes and interpreted contexts \<close>

context semantic_type_locale
begin

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val typ =
      Syntax.read_term \<^context>
        ("semantic_locale_unused :: " ^
          "('s \<Rightarrow> ('s, unit, bool, 'i, 'o) function_body) \<Rightarrow> " ^
          "('s, unit, bool, 'i, 'o) function_body")
      |> fastype_of
    val callback = hd (binder_types typ)
    val (state, _, _, _, _) = channels typ
    val _ = require "locale state became flexible" (state = \<^typ>\<open>'s\<close>)
    val _ = require "locale callback state link was lost" (hd (binder_types callback) = state)
  in val _ = () end
\<close>

end

section\<open> Every channel combination and default unit results \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val entries =
      [("state", "'s::cancellative_sepalg"),
       ("abort", "bool"), ("input", "nat prompt"), ("output", "unit prompt_output")]
    fun subsets [] = [[]]
      | subsets (entry :: rest) =
          let val smaller = subsets rest in smaller @ map (cons entry) smaller end
    fun check selected =
      let
        val options =
          if null selected then ""
          else "[" ^ commas (map (fn (name, typ) => name ^ " = " ^ cartouche typ) selected) ^ "]"
        fun channel name fallback =
          the_default fallback (AList.lookup (op =) selected name)
        val expected =
          "nat \<Rightarrow> (" ^ commas
            [channel "state" "'s", "unit", channel "abort" "'abort",
             channel "input" "'input", channel "output" "'output"] ^ ") function_body"
        fun run annotation =
          run_from base ("semantic-combination-" ^ space_implode "-" (map fst selected))
            (command options "semantic_combination"
              ("fn SemanticCombination(value: \<tau>" ^ cartouche "nat" ^ ")" ^
                annotation ^ " { () }"))
          |> Toplevel.context_of
        val omitted = run ""
        val explicit = run " -> ()"
        val _ =
          List.app (fn context =>
            require ("channel combination changed its complete type: " ^ options)
              (Sign.typ_equiv (Proof_Context.theory_of context)
                (declared_type context "semantic_combination",
                 Logic.varifyT_global (Syntax.read_typ ctxt expected))))
            [omitted, explicit]
        val _ = require "default unit changed the definition"
          (Term.aconv (rhs omitted "semantic_combination", rhs explicit "semantic_combination"))
      in () end
    val _ = List.app check (subsets entries)
  in val _ = () end
\<close>

section\<open> Artifacts, options, positioned failures and rollback \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val semantic_type =
      "nat \<Rightarrow> (unit, nat, bool, nat prompt, unit prompt_output) function_body"
    val channel_options =
      "state = " ^ cartouche "unit" ^ ", abort = " ^ cartouche "bool" ^
      ", input = " ^ cartouche "nat prompt" ^ ", output = " ^ cartouche "unit prompt_output"
    val option = "[" ^ channel_options ^ "]"
    val item = "fn SemanticArtifact(value: \<tau>" ^ cartouche "nat" ^
      ") -> \<tau>" ^ cartouche "nat" ^ " { value }"
    fun run options target = run_from base "semantic-artifact" (command options target item)
    val normal = run option "semantic_artifact" |> Toplevel.context_of
    val application =
      run ("[" ^ channel_options ^ ", application_def]") "semantic_application"
      |> Toplevel.context_of
    val abbreviated =
      run ("[" ^ channel_options ^ ", abbrev]") "semantic_abbreviated"
      |> Toplevel.context_of
    val suppressed =
      run ("[register_notation = false, " ^ channel_options ^ "]") "semantic_suppressed"
      |> Toplevel.context_of
    val _ = require "application definition lost source argument"
      (is_Const (fst (Logic.dest_equals (Thm.prop_of (theorem normal "semantic_artifact")))) andalso
        not (is_Const (fst (Logic.dest_equals (Thm.prop_of (theorem application "semantic_application"))))))
    val _ = require "abbreviation installed a definition theorem"
      (is_none (try (fn () => theorem abbreviated "semantic_abbreviated") ()))
    val _ = require "registration suppression lost the constant"
      (Sign.typ_equiv (Proof_Context.theory_of suppressed)
        (declared_type suppressed "semantic_suppressed", Syntax.read_typ ctxt semantic_type))
    val _ = registry_unchanged "suppressed semantic function" ctxt suppressed
    val anonymous = run option "_" |> Toplevel.context_of
    val _ = require "anonymous semantic declaration installed a constant"
      (constant_snapshot ctxt = constant_snapshot anonymous)
    val _ = registry_unchanged "anonymous semantic function" ctxt anonymous

    fun reject_text label expected text =
      let
        val (result, reports) =
          Parser_Test_Reports.markup (fn () =>
            Exn.capture (run_from base label) text)
        val diagnostic = message result
        val _ = require (label ^ ": wrong diagnostic")
          (String.isSubstring expected diagnostic)
        val _ = require (label ^ ": no source position")
          (String.isSubstring label diagnostic andalso not (null (diagnostic_ranges diagnostic)))
        val _ = require (label ^ ": installed declaration markup")
          (null (declaration_definitions reports))
        val _ = require (label ^ ": mutated constant table")
          (constant_snapshot ctxt = constant_snapshot (Toplevel.context_of base))
        val _ = registry_unchanged label ctxt (Toplevel.context_of base)
        val _ = ignore (run_from base (label ^ "-recovery") (command option "semantic_failure" item))
      in () end
    fun reject label expected options body =
      reject_text label expected (command options "semantic_failure" body)
    fun typed name typ = "[" ^ name ^ " = " ^ cartouche typ ^ "]"
    val _ = reject "semantic-removed-type" "unknown uRust command option \"type\""
      (typed "type" semantic_type) item
    val _ = reject "semantic-removed-type-malformed" "unknown uRust command option \"type\""
      "[type = [broken]]" item
    val _ = reject "semantic-omitted-nonunit" "Type unification failed"
      "" "fn SemanticMismatch(value: u64) { value }"
    val _ = reject "semantic-omitted-nonunit-channels" "Type unification failed"
      option "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) { value }"
    val _ = reject "semantic-explicit-unit-mismatch" "Type unification failed"
      "" "fn SemanticMismatch(value: u64) -> () { value }"
    val _ = reject "semantic-return-mismatch" "Type unification failed"
      option "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) -> bool { value }"
    val _ = reject "semantic-parameter-mismatch" "Type unification failed"
      option "fn SemanticMismatch(value: bool) -> \<tau>\<open>nat\<close> { value }"
    val _ = reject "semantic-incompatible-sort" "Type unification failed"
      (typed "state" "'a::cancellative_sepalg")
      "fn SemanticMismatch(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>nat\<close> { value }"
    val _ = reject "semantic-body-mismatch" "Type unification failed"
      option "fn SemanticMismatch(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { true }"
    val _ = reject "semantic-state-mismatch" "Type unification failed"
      (typed "state" "bool")
      "fn SemanticMismatch() -> \<tau>\<open>nat\<close> { \<epsilon>\<open>get (\<lambda>s::nat. s)\<close> }"
    val _ = reject "semantic-abort-mismatch" "Type unification failed"
      (typed "abort" "unit")
      "fn SemanticMismatch() { \<epsilon>\<open>abort (CustomAbort True)\<close> }"
    val fixed_body =
      "fn SemanticMismatch() { \<epsilon>\<open>literal () :: " ^
      "(unit, unit, unit, bool, nat prompt, unit prompt_output) expression\<close> }"
    val _ = reject "semantic-input-mismatch" "Type unification failed"
      (typed "input" "bool") fixed_body
    val _ = reject "semantic-output-mismatch" "Type unification failed"
      (typed "output" "bool") fixed_body
    val _ = reject "semantic-shared-sort-concrete" "Type unification failed"
      (typed "abort" "'a::cancellative_sepalg")
      "fn SemanticMismatch(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { \<llangle>0::nat\<rrangle> }"
    val _ =
      List.app (fn name =>
        (reject ("semantic-duplicate-" ^ name) "duplicate uRust command option"
          ("[" ^ name ^ " = " ^ cartouche "unit" ^ ", " ^ name ^ " = " ^ cartouche "unit" ^ "]") item;
         reject ("semantic-missing-" ^ name) "expects a HOL type" ("[" ^ name ^ "]") item;
         reject ("semantic-wrong-" ^ name) "expects a HOL type" ("[" ^ name ^ " = true]") item;
         reject ("semantic-integer-" ^ name) "expects a HOL type" ("[" ^ name ^ " = 1]") item;
         reject ("semantic-malformed-" ^ name) "Failed to parse type"
           (typed name "unit \<Rightarrow>") item))
        ["state", "abort", "input", "output"]
    val _ = reject_text "semantic-rigid-locale" "Type unification failed"
      ("context semantic_type_locale begin\n" ^
        command (typed "state" "'s")
          "semantic_failure"
          "fn SemanticMismatch() { \<epsilon>\<open>put (\<lambda>_::unit. ())\<close> }")
  in val _ = () end
\<close>

chapter\<open> Scoped channel defaults \<close>

section\<open> Inherited and overridden channels \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun same_type label (name, expected) =
      require (label ^ ": " ^ name)
        (Sign.typ_equiv (Proof_Context.theory_of ctxt)
          (declared_type ctxt name, Logic.varifyT_global expected))
    val _ =
      same_type "default differs from the inline channels"
        ("default_identity", Logic.unvarifyT_global (declared_type ctxt "semantic_identity"))
    val _ =
      same_type "override replaced more than its channel"
        ("default_abort_override",
         \<^typ>\<open>nat \<Rightarrow>
           ('s::cancellative_sepalg, nat, unit, nat prompt, unit prompt_output) function_body\<close>)
    val (state, _, abort, input, output) = channels (declared_type ctxt "default_outside_scope")
    val _ = independent "default escaped its context block" [state, abort, input, output]

    (* The readable examples in Parser_Function_Tests. *)
    val _ =
      same_type "scoped example differs from the inline channels"
        ("scoped_identity", Logic.unvarifyT_global (declared_type ctxt "semantic_identity"))
    val _ =
      same_type "scoped example override replaced more than its channel"
        ("scoped_unit_abort_identity", Logic.unvarifyT_global (declared_type ctxt "default_abort_override"))
    val (state, _, _, _, _) = channels (declared_type ctxt "scoped_any_state_identity")
    val _ = require "scoped example hole kept the state default"
      (generic state andalso
        not (Sign.subsort (Proof_Context.theory_of ctxt)
          (sort_of state, \<^sort>\<open>cancellative_sepalg\<close>)))
  in val _ = () end
\<close>

section\<open> Members of an item list \<close>

context
  notes [[urust_state = \<open>'s::cancellative_sepalg\<close>, urust_abort = \<open>bool\<close>]]
begin

urust \<open>
  fn DefaultChunkInherited(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }

  \<omega>\<open>abort = \<open>unit\<close>\<close>
  fn DefaultChunkOverride(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }
\<close>

end

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    fun check name expected_abort =
      let
        val (state, _, abort, input, output) = channels (declared_type ctxt name)
      in
        require (name ^ ": inherited state was lost")
          (generic state andalso
            Sign.subsort (Proof_Context.theory_of ctxt)
              (sort_of state, \<^sort>\<open>cancellative_sepalg\<close>));
        require (name ^ ": wrong abort channel") (abort = expected_abort);
        independent (name ^ ": unset channels became constrained") [state, input, output]
      end
    val _ = check "default_chunk_inherited" \<^typ>\<open>bool\<close>
    val _ = check "default_chunk_override" \<^typ>\<open>unit\<close>
  in val _ = () end
\<close>

section\<open> Equivalence, precedence, removal and sharing \<close>

ML\<open>
structure Parser_Channel_Default_Test =
struct
  open Parser_Function_Regression_Test

  val channel_names = ["state", "abort", "input", "output"]

  fun subsets [] = [[]]
    | subsets (entry :: rest) =
        let val smaller = subsets rest in smaller @ map (cons entry) smaller end

  fun inline_options [] = ""
    | inline_options entries =
        "[" ^ commas (map (fn (name, typ) => name ^ " = " ^ cartouche typ) entries) ^ "]"

  fun declare_defaults [] = ""
    | declare_defaults entries =
        "declare [[" ^
          commas (map (fn (name, typ) => "urust_" ^ name ^ " = " ^ cartouche typ) entries) ^
          "]]\n"

  fun context_after base label text = run_from base label text |> Toplevel.context_of

  fun same_scheme label (context, name) expected =
    require label
      (Sign.typ_equiv (Proof_Context.theory_of context)
        (declared_type context name, Logic.varifyT_global expected))

  fun file_markup label =
    exists (fn (_, properties) => Properties.get properties Markup.fileN = SOME label)
end
\<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val defaults =
      [("state", "'s::cancellative_sepalg"), ("abort", "bool"),
       ("input", "nat prompt"), ("output", "unit prompt_output")]
    val overrides =
      [("state", "unit"), ("abort", "nat"), ("input", "bool prompt"), ("output", "nat prompt_output")]
    val item = "fn DefaultCombination(value: \<tau>" ^ cartouche "nat" ^ ") { () }"
    fun expected selected fallback =
      let
        fun channel name = the_default (fallback name) (AList.lookup (op =) selected name)
      in
        Syntax.read_typ ctxt
          ("nat \<Rightarrow> (" ^
            commas [channel "state", "unit", channel "abort", channel "input", channel "output"] ^
            ") function_body")
      end
    fun label prefix selected = space_implode "-" (prefix :: map fst selected)

    (* Scoped defaults agree exactly with the same inline options. *)
    fun inherit selected =
      let
        val inherited =
          context_after base (label "default-inherit" selected)
            (declare_defaults selected ^ command "" "default_combination" item)
        val inline =
          context_after base (label "default-inline" selected)
            (command (inline_options selected) "default_combination" item)
        val _ =
          same_scheme ("inherited channels changed the complete type: " ^ inline_options selected)
            (inherited, "default_combination")
            (expected selected (fn name => "'" ^ name))
      in
        require "inherited channels changed the definition"
          (Term.aconv (rhs inherited "default_combination", rhs inline "default_combination"))
      end
    val _ = List.app inherit (subsets defaults)

    (* Each inline option replaces exactly its own channel. *)
    fun override selected =
      same_scheme ("override changed another channel: " ^ inline_options selected)
        (context_after base (label "default-override" selected)
          (declare_defaults defaults ^
            command (inline_options selected) "default_combination" item),
         "default_combination")
        (expected selected (the o AList.lookup (op =) defaults))
    val _ = List.app override (subsets overrides)

    (* A hole option, a removed default and a nested removal all mean an omitted channel. *)
    fun removal name =
      let
        val remaining = filter_out (fn (channel, _) => channel = name) defaults
        val reference =
          context_after base ("default-reference-" ^ name)
            (declare_defaults remaining ^ command "" "default_combination" item)
        fun agrees how context =
          same_scheme (how ^ " " ^ name ^ " differs from an omitted channel")
            (context, "default_combination")
            (Logic.unvarifyT_global (declared_type reference "default_combination"))
        val _ =
          agrees "inline hole"
            (context_after base ("default-hole-" ^ name)
              (declare_defaults defaults ^
                command (inline_options [(name, "_")]) "default_combination" item))
        val _ =
          agrees "removed default"
            (context_after base ("default-removed-" ^ name)
              (declare_defaults defaults ^ declare_defaults [(name, "_")] ^
                command "" "default_combination" item))
        val nested =
          context_after base ("default-nested-" ^ name)
            (declare_defaults defaults ^
              "context notes [[urust_" ^ name ^ " = " ^ cartouche "_" ^ "]] begin\n" ^
              command "" "default_combination" item ^ "\nend\n" ^
              command "" "default_restored"
                ("fn DefaultRestored(value: \<tau>" ^ cartouche "nat" ^ ") { () }"))
        val _ = agrees "nested removal" nested
      in
        same_scheme ("nested removal did not restore the outer " ^ name ^ " default")
          (nested, "default_restored") (expected [] (the o AList.lookup (op =) defaults))
      end
    val _ = List.app removal channel_names

    val sorted_holes =
      context_after base "default-sorted-holes"
        (declare_defaults [("input", "_::finite"), ("output", "_::finite")] ^
          command "" "default_sorted_holes" item)
    val (_, _, _, input, output) = channels (declared_type sorted_holes "default_sorted_holes")
    val _ = independent "sorted hole defaults became identified" [input, output]
    val _ =
      List.app (fn typ =>
        require "sorted hole default lost its sort"
          (Sign.subsort (Proof_Context.theory_of sorted_holes) (sort_of typ, \<^sort>\<open>finite\<close>)))
        [input, output]

    val later = context_after base "default-later-duplicate"
      ("declare [[urust_abort = " ^ cartouche "bool" ^ ", urust_abort = " ^ cartouche "unit" ^
        "]]\n" ^ command "" "default_combination" item)
    val (_, _, abort, _, _) = channels (declared_type later "default_combination")
    val _ = require "the later duplicate default did not win" (abort = \<^typ>\<open>unit\<close>)
  in val _ = () end
\<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>

    (* Named variables of defaults, inline options and HOL escapes share one environment. *)
    val escape_sharing =
      context_after base "default-escape-sharing"
        (declare_defaults [("abort", "'value::linorder")] ^
          command "" "default_sharing"
            ("fn DefaultSharing(value: \<tau>" ^ cartouche "'value" ^ ") -> \<tau>" ^
              cartouche "'value" ^ " { value }"))
    val typ = declared_type escape_sharing "default_sharing"
    val (state, result, abort, input, output) = channels typ
    val _ = require "default and escape names did not share"
      (abort = result andalso binder_types typ = [result])
    val _ = require "default sort was lost"
      (Sign.subsort (Proof_Context.theory_of escape_sharing) (sort_of abort, \<^sort>\<open>linorder\<close>))
    val _ = independent "unrelated channels were captured" [state, result, input, output]

    val option_sharing =
      context_after base "default-option-sharing"
        (declare_defaults [("input", "'channel")] ^
          command (inline_options [("output", "'channel")]) "default_sharing"
            "fn DefaultSharing() {}")
    val (_, _, _, input, output) = channels (declared_type option_sharing "default_sharing")
    val _ = require "default and inline option names did not share" (input = output)

    (* Every inheriting function reads its own fresh variables. *)
    val fresh =
      context_after base "default-fresh-names"
        (declare_defaults [("state", "'s"), ("abort", "'s")] ^
          command "" "default_first" "fn DefaultFirst() {}" ^ "\n" ^
          command "" "default_second"
            ("fn DefaultSecond(callback: \<tau>" ^
              cartouche "('s, unit, 's, unit, unit) function_body" ^ ") {}"))
    val (first_state, _, first_abort, _, _) = channels (declared_type fresh "default_first")
    val _ = require "one default name did not share across channels" (first_state = first_abort)
    val second = declared_type fresh "default_second"
    val (second_state, _, _, _, _) = channels second
    val (callback_state, _, _, _, _) = channels (hd (binder_types second))
    val _ = require "default name did not share with a later escape" (second_state = callback_state)
  in val _ = () end
\<close>

section\<open> Context scoping, locales and interpretation \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    fun abort_of context name =
      let val (_, _, abort, _, _) = channels (declared_type context name) in abort end

    (* Theory declarations persist; nested blocks shadow and then restore. *)
    val scoped =
      context_after base "default-scoping"
        (declare_defaults [("abort", "bool")] ^
          command "" "default_first" "fn DefaultFirst() {}" ^ "\n" ^
          "context notes [[urust_abort = " ^ cartouche "nat" ^ "]] begin\n" ^
          "context notes [[urust_abort = " ^ cartouche "unit" ^ "]] begin\n" ^
          command "" "default_inner" "fn DefaultInner() {}" ^ "\nend\n" ^
          command "" "default_middle" "fn DefaultMiddle() {}" ^ "\nend\n" ^
          command "" "default_second" "fn DefaultSecond() {}")
    val _ =
      List.app (fn (name, expected) =>
        require ("wrong scoped abort for " ^ name) (abort_of scoped name = expected))
        [("default_first", \<^typ>\<open>bool\<close>), ("default_inner", \<^typ>\<open>unit\<close>),
         ("default_middle", \<^typ>\<open>nat\<close>), ("default_second", \<^typ>\<open>bool\<close>)]

    val locale_text =
      "locale default_scope_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
      "\nbegin\n" ^ declare_defaults [("state", "'s")]
    fun locale_function name =
      command "[register_notation = false]" name
        ("fn " ^ name ^ "() -> () { \<llangle>let _ = seed in ()\<rrangle> }")
    fun local_state context name =
      let val (state, _, _, _, _) = channels (fastype_of (rhs context name)) in state end
    val rigid = \<^typ>\<open>'s::cancellative_sepalg\<close>

    (* A locale default reads the locale's fixed variable, stays in the locale and returns with
       it. A theory bundle opened in the locale is captured by the same rigid variable. *)
    val inside =
      context_after base "default-locale-inside" (locale_text ^ locale_function "default_inside")
    val _ = require "locale default state became flexible" (local_state inside "default_inside" = rigid)
    val reentered =
      context_after base "default-locale-reentered"
        (locale_text ^ locale_function "default_inside" ^ "\nend\n" ^
          command "" "default_outside" "fn DefaultOutside() {}" ^ "\n" ^
          "context default_scope_locale begin\n" ^ locale_function "default_reentered")
    val _ = require "re-entered locale lost its default"
      (local_state reentered "default_reentered" = rigid)
    val (outside, _, _, _, _) =
      channels (declared_type (Proof_Context.init_global (Proof_Context.theory_of reentered))
        "default_outside")
    val _ = independent "locale default escaped to the theory" [outside]
    val bundled =
      context_after base "default-locale-bundle"
        ("bundle default_scope_bundle = [[urust_state = " ^ cartouche "'s" ^ "]]\n" ^
          "locale default_scope_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
          "\ncontext default_scope_locale opening default_scope_bundle begin\n" ^
          locale_function "default_bundled")
    val _ = require "bundled default was not captured by the locale variable"
      (local_state bundled "default_bundled" = rigid)

    (* Native locale notes replay a locale declaration into every global interpretation, both
       later and existing ones; each replay rereads the source in the interpreting theory. *)
    val interpreted =
      context_after base "default-interpretation"
        ("locale default_interpreted_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
          "\nbegin\n" ^ declare_defaults [("state", "'s"), ("abort", "bool")] ^
          locale_function "default_inside" ^ "\nend\n" ^
          "interpretation default_unit: default_interpreted_locale " ^ cartouche "()" ^ " .\n" ^
          command "" "default_after_interpretation" "fn DefaultAfterInterpretation() {}")
    val (state, _, abort, _, _) = channels (declared_type interpreted "default_after_interpretation")
    val _ = require "interpretation did not replay the locale default"
      (abort = \<^typ>\<open>bool\<close> andalso generic state)
    val (instantiated, _, _, _, _) =
      channels (declared_type interpreted "default_unit.default_inside")
    val _ = require "interpreted function lost its instantiated state"
      (instantiated = \<^typ>\<open>unit\<close>)
    val existing =
      context_after base "default-existing-interpretation"
        ("locale default_interpreted_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
          "\ninterpretation default_unit: default_interpreted_locale " ^ cartouche "()" ^ " .\n" ^
          "context default_interpreted_locale begin\n" ^ declare_defaults [("abort", "bool")] ^
          "end\n" ^
          command "" "default_after_declaration" "fn DefaultAfterDeclaration() {}")
    val _ = require "existing interpretation did not receive the locale default"
      (abort_of existing "default_after_declaration" = \<^typ>\<open>bool\<close>)
  in val _ = () end
\<close>

section\<open> Reports \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val declaration = "default-markup-declaration"

    (* The declaration reports once in its own command. Inheriting functions, item-list members
       and interpretation replays report only in their own sources. *)
    val (declared, declaration_reports) =
      Parser_Test_Reports.markup (fn () =>
        run_from base declaration
          ("locale default_markup_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
            "\nbegin\n" ^ declare_defaults [("abort", "bool"), ("output", "_::finite")] ^ "end\n" ^
            declare_defaults [("abort", "bool"), ("output", "_::finite")]))
    val _ = require "the default declaration reported no markup"
      (file_markup declaration
        (filter (fn (name, _) => name = Markup.entityN) declaration_reports))
    fun quiet label text =
      let
        val (_, reports) = Parser_Test_Reports.markup (fn () => run_from declared label text)
        val _ = require (label ^ ": captured no markup of its own") (file_markup label reports)
      in
        require (label ^ ": reported into the default declaration")
          (not (file_markup declaration reports))
      end
    val _ =
      quiet "default-markup-function"
        (command "" "default_markup" "fn DefaultMarkup(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }")
    val _ =
      quiet "default-markup-chunk"
        ("urust " ^ cartouche "fn DefaultMarkupChunk(value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { value }")
    val _ =
      quiet "default-markup-interpretation"
        ("interpretation default_markup_unit: default_markup_locale " ^ cartouche "()" ^ " .\n" ^
          command "" "default_markup" "fn DefaultMarkup() {}")
  in val _ = () end
\<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val label = "default-markup-keyword-option"

    (* The output option is spelled like the Pure minor keyword. Inline and in an annotation it is
       reported as unhighlighted after any keyword report, so it renders as an option name. *)
    val text =
      command (inline_options [("output", "unit")]) "default_keyword_inline"
        "fn DefaultKeywordInline() {}" ^ "\n" ^
      "urust " ^
        cartouche
          ("\n  \<omega>" ^ cartouche ("output = " ^ cartouche "unit") ^
            "\n  fn DefaultKeywordAnnotated() {}\n")
    val (_, markup) = Parser_Test_Reports.markup (fn () => run_from base label text)
    (* Colour reports at one range in report order; the last one determines the rendering. *)
    fun colours position =
      markup
      |> filter (fn (name, properties) =>
          member (op =) [Markup.keyword2N, Markup.delimiterN] name andalso
            has_position properties position)
      |> map #1
    val inline = token_position text (start label) "output" 0
    val annotated =
      token_position text (start label) "output" (find_from text "output" 0 + 1)
    val _ = require "inline keyword option name was not reported as unhighlighted"
      (colours inline = [Markup.delimiterN])
    val _ = require "annotation keyword option name kept the keyword colour"
      (colours annotated = [Markup.keyword2N, Markup.delimiterN])
  in val _ = () end
\<close>

section\<open> Commands that read no channels \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val defaults =
      declare_defaults
        [("state", "unit"), ("abort", "bool"), ("input", "unit"), ("output", "unit")]
    val expression = "urust_expr default_expression " ^ cartouche "()"
    val plain = context_after base "default-expression-plain" expression
    val inherited = context_after base "default-expression-inherited" (defaults ^ expression)
    val _ = same_scheme "urust_expr inherited a function channel default"
      (inherited, "default_expression") (Logic.unvarifyT_global (declared_type plain "default_expression"))

    fun elaborate context =
      Parser_Test_Elaboration.function context
        {raw_type = ("nat \<Rightarrow> _", start "default-api-type"),
         parameters = [("value", start "default-api-parameter")],
         parameters_pos = start "default-api-parameter",
         body = source "default-api-body" "value"}
    val _ = require "the typed-body API inherited function channel defaults"
      (Term.aconv (elaborate (Toplevel.context_of base), elaborate inherited) andalso
        fastype_of (elaborate (Toplevel.context_of base)) = fastype_of (elaborate inherited))
  in val _ = () end
\<close>

section\<open> Positioned failures and rollback \<close>

ML_val\<open>
  local
    open Parser_Channel_Default_Test
    val base = initial \<^theory>
    val item = "fn DefaultFailure(value: \<tau>" ^ cartouche "nat" ^ ") -> \<tau>" ^ cartouche "nat" ^
      " { value }"

    (* An inline option overrides a broken default, so recovery bypasses all four. *)
    val recovery =
      command (inline_options (map (rpair "_") channel_names)) "default_recovery" item

    fun rejected_from state label expected text =
      let
        val (result, reports) =
          Parser_Test_Reports.markup (fn () => Exn.capture (run_from state label) text)
        val diagnostic = message result
        val _ = require (label ^ ": wrong diagnostic " ^ quote diagnostic)
          (String.isSubstring expected diagnostic)
        val _ = require (label ^ ": no source position")
          (String.isSubstring label diagnostic andalso not (null (diagnostic_ranges diagnostic)))
        val _ = require (label ^ ": installed declaration markup")
          (null (declaration_definitions reports))
        val _ = ignore (run_from state (label ^ "-recovery") recovery)
      in diagnostic end
    fun reject_declaration label expected text = ignore (rejected_from base label expected text)

    (* Declaration-time failures. *)
    val _ = reject_declaration "default-malformed" "Failed to parse type"
      (declare_defaults [("state", "unit \<Rightarrow>")])
    val _ = reject_declaration "default-undefined" "Undefined type name"
      (declare_defaults [("abort", "default_missing_type")])
    val _ = reject_declaration "default-missing-value" "Bad arguments"
      "declare [[urust_input]]"
    val _ = reject_declaration "default-inline-spelling"
      "unknown uRust command option \"urust_output\""
      (command (inline_options [("urust_output", "unit")]) "default_failure" item)

    (* Signature failures cite the inheriting function and the default declaration. Body
       mismatches against the resolved type are positioned in the body, as for inline options. *)
    fun reject_use_with cites label expected defaults text =
      let
        val declaration = label ^ "-declaration"
        val declared = run_from base declaration defaults
        val diagnostic = rejected_from declared label expected text
      in
        require (label ^ ": wrong default declaration citation")
          (String.isSubstring declaration diagnostic = cites)
      end
    val reject_use = reject_use_with true
    val _ = reject_use "default-sort-clash" "Inconsistent sort constraints"
      (declare_defaults [("abort", "'value::linorder")])
      (command "" "default_failure"
        ("fn DefaultFailure(value: \<tau>" ^ cartouche "'value::cancellative_sepalg" ^ ") {}"))
    val _ = reject_use "default-hidden-type" "scoped default urust_abort"
      ("typedecl default_hidden_type\n" ^ declare_defaults [("abort", "default_hidden_type")] ^
        "hide_type default_hidden_type\n")
      (command "" "default_failure" item)
    val _ = reject_use "default-locale-capture" "Sort constraint"
      ("bundle default_capture_bundle = [[urust_state = " ^ cartouche "'s::linorder" ^ "]]\n" ^
        "locale default_capture_locale =\n  fixes seed :: " ^ cartouche "'s::cancellative_sepalg" ^
        "\n")
      ("context default_capture_locale opening default_capture_bundle begin\n" ^
        command "[register_notation = false]" "default_failure" "fn DefaultFailure() {}")
    val fixed_body =
      "fn DefaultFailure() { \<epsilon>\<open>literal () :: " ^
      "(unit, unit, unit, bool, nat prompt, unit prompt_output) expression\<close> }"
    val _ =
      List.app (fn (channel, body) =>
        reject_use_with false ("default-" ^ channel ^ "-mismatch") "Type unification failed"
          (declare_defaults [(channel, "bool")]) (command "" "default_failure" body))
        [("state", "fn DefaultFailure() -> \<tau>\<open>nat\<close> { \<epsilon>\<open>get (\<lambda>s::nat. s)\<close> }"),
         ("abort", "fn DefaultFailure() { \<epsilon>\<open>abort (CustomAbort (0::nat))\<close> }"),
         ("input", fixed_body), ("output", fixed_body)]
  in val _ = () end
\<close>

chapter\<open> Typed receivers \<close>

section\<open> Name collisions and nested lexical scope \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

micro_rust_notation (literal) \<open>True\<close> ("self")

urust_fn \<open> fn TypedSelfLiteralShadow(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { self } \<close>

urust_fn \<open> fn TypedSelfValueLiteralShadow(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { self_value } \<close>

urust_fn \<open>
    fn TypedSelfNameCollision(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      let self_value = true;
      self
    }
  \<close>

urust_fn \<open>
    fn TypedSelfValueNameCollision(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
      let other_value = true;
      self_value
    }
  \<close>

urust_fn \<open>
    fn TypedSelfClosure(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> {
      |self_value| \<llangle>self + self_value\<rrangle>
    }
  \<close>

urust_fn \<open>
    fn TypedSelfValueClosure(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close> {
      |other_value| \<llangle>self_value + other_value\<rrangle>
    }
  \<close>

context
  fixes self :: bool
begin

urust_fn \<open> fn TypedSelfContextShadow(self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self + 1\<rrangle> } \<close>

urust_fn \<open> fn TypedSelfValueContextShadow(self_value: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { \<llangle>self_value + 1\<rrangle> } \<close>

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
      [("receiver-untyped-self", "receiver shorthand is only allowed in impl members",
        "fn BadReceiver(self) -> u8 { self }"),
       ("receiver-borrowed-shorthand", "receiver shorthand is only allowed in impl members",
        "fn BadReceiver(&self) -> u8 { self }"),
       ("receiver-mut-borrowed-shorthand", "receiver shorthand is only allowed in impl members",
        "fn BadReceiver(&mut self) -> u8 { self }"),
       ("receiver-borrowed-pattern", "unsupported function parameter pattern",
        "fn BadReceiver(&self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { self }"),
       ("receiver-implicit-Self", "Self is only available inside an impl block", "fn BadReceiver(self: Self) -> Self { self }"),
       ("receiver-rust-reference", "shared Rust references", "fn BadReceiver(self: &u8) -> u8 { 0 }"),
       ("receiver-duplicate", "duplicate parameter \"self\"",
        "fn BadReceiver(self: u8, self: bool) -> u8 { self }"),
       ("receiver-body-type", "Type unification failed", "fn BadReceiver(self: bool) -> u8 { self }")]
  in val _ = () end
\<close>

chapter\<open> Mutable references and erased lifetimes \<close>

section\<open> Mutable references and lifetimes in function signatures \<close>

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

    val bound_text = "fn Bound<'a, /* \<alpha> */ 'b: 'a>(value: &'b mut u8) { () }"
    val bound = parse ctxt "lifetime-position-bound" bound_text
    val _ = require "retained lifetime bound preserves the original colon token range"
      (case #parameters (URust_AST.function_generics bound) of
         [_, URust_AST.Generic_Lifetime_Bounds (_, _, layout)] =>
           map range_of (URust_AST.source_token_positions layout (URust_AST.Delimiter_Token ":")) =
             [range_of (nth_position bound_text "lifetime-position-bound" ":" 0)]
       | _ => false)
  in val _ = () end
\<close>

section\<open> Body and call-site semantics \<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> reference_test_read
adhoc_overloading store_reference_const \<rightleftharpoons> reference_test_allocate
adhoc_overloading store_update_const \<rightleftharpoons> reference_test_write

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
      command ("[state = " ^ cartouche "unit" ^ ", abort = " ^ cartouche "unit" ^
        ", input = " ^ cartouche "unit" ^ ", output = " ^ cartouche "unit" ^ "]")
        "reference_failure" "fn ReferenceRecovery(value: &mut u32) -> u32 { *value }"
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
       ("reference-lifetime-argument", "undeclared lifetime",
        "fn BadReference(value: RefOption<'a>) -> u8 { 0 }"),
       ("reference-lifetime-without-reference", "syntax error",
        "fn BadReference<'a>(value: 'a) -> u8 { 0 }"),
       ("reference-missing-target", "syntax error",
        "fn BadReference(value: &'a mut) -> u8 { 0 }"),
       ("reference-shorthand-receiver", "receiver shorthand is only allowed in impl members",
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

chapter\<open> Datatype composition \<close>

section\<open> Complete const arguments and radix discriminants \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

no_adhoc_overloading store_dereference_const \<rightleftharpoons> reference_test_read
no_adhoc_overloading store_reference_const \<rightleftharpoons> reference_test_allocate
no_adhoc_overloading store_update_const \<rightleftharpoons> reference_test_write

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
  val function = the (Parser_Test_Calls.lookup ctxt "CompositionRead")
  val _ = require "typed receiver function lost default callable registration"
    (dest_Const_name ((fn (entry: Micro_Rust_Names.entry) => #hol_term entry) function) =
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
  val _ = if is_none (Parser_Test_Calls.lookup ctxt "CompositionScopedOff") andalso
    is_some (Parser_Test_Calls.lookup ctxt "CompositionScopedOn") andalso
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
    forall (is_none o Parser_Test_Calls.lookup ctxt)
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
      ", backend = hol, hol_names = [\"Stored\" \<rightarrow> \<open>CompositionReplayStored\<close>]] " ^
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
    (length (Parser_Test_Calls.dump plain) = length (Parser_Test_Calls.dump replayed))
  val _ = List.app (fn name =>
    require (name ^ ": composed replay changed the complete HOL type or body")
      (Sign.typ_equiv thy (declared_type plain name, declared_type replayed name) andalso
       Term.aconv (rhs plain name, rhs replayed name)))
    ["composition_replay_identity", "composition_replay_client"]
in val _ = () end
\<close>

section\<open> Dispatch marker source positions \<close>

text\<open>
Dispatch and semantic-navigation markers carry their use-site positions in the name of a payload
\<^verbatim>\<open>Free\<close>. The payload keeps every position property, including a file whose path would make
the name qualified, so each use-site report stays in the source that contains the use. A payload
name with a malformed escape, position field or qualifier count is rejected with the diagnostic of
its owner.
\<close>

ML \<open>
structure Marker_Position_Test =
struct
  structure Dispatch = Micro_Rust_Dispatch

  fun positioned line offset end_offset label file =
    Position.make0 line offset end_offset label file ""
    |> Position.copy_id (Position.thread_data ())

  (* Control characters that YXML and the payload fields leave free, each repeated and followed
     by letters and a dot, and every printable ASCII character. *)
  val controls =
    [1, 2, 3, 4, 7, 9, 10, 31]
    |> map (fn code =>
        let val c = String.str (Char.chr code)
        in c ^ c ^ "s" ^ c ^ "e" ^ c ^ "." end)
    |> implode
  val printable = implode (map (String.str o Char.chr) (32 upto 126))
  val dotted = positioned 3 17 29 "" "~/marker-position.d/../Marker_Position.thy"
  val labelled = positioned 4 31 37 "marker-position.label" "marker-position.Qualified.name"
  val unfiled = positioned 0 41 47 "" ""
  val hostile =
    positioned 5 53 54 ""
      ("./marker-position" ^ controls ^ printable ^ "\<alpha>/.thy.")
  val positions =
    {terminal_pos = dotted,
     qualifier_positions = [labelled, Position.none, unfiled],
     backend_only_positions = [hostile]}

  fun same_positions left right =
    map Position.properties_of left = map Position.properties_of right

  fun same_marker_positions
      ({terminal_pos, qualifier_positions, backend_only_positions} :
        Dispatch.marker_positions)
      (decoded : Dispatch.marker_positions) =
    same_positions [terminal_pos] [#terminal_pos decoded] andalso
    same_positions qualifier_positions (#qualifier_positions decoded) andalso
    same_positions backend_only_positions (#backend_only_positions decoded)

  (* The term decoder reads a qualified Free name as a constant. *)
  fun decodes_as_free ctxt (payload as Free (name, _)) =
        not (Long_Name.is_qualified name) andalso
        (case Syntax_Phases.decode_term ctxt ([], Exn.Res payload) of
           (_, Exn.Res (Free (decoded, _))) => decoded = name
         | _ => false)
    | decodes_as_free _ _ = false

  fun payload_name (Free (name, _)) = name
    | payload_name _ = error "payload is not a free variable"

  (* An action is rejected with an ERROR whose message contains the expected text. *)
  fun rejected expected action =
    (case Exn.result action () of
       Exn.Exn (ERROR message) => String.isSubstring expected message
     | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else false
     | Exn.Res _ => false)

  val escape = String.str (Char.chr 1)
  val separator = String.str (Char.chr 0)

  (* Corruptions of an encoded payload name that keep its prefix and leading fields. Its
     positions end with the three-character YXML close of their list element. *)
  fun corruptions name =
    let val (fields, _) = split_last (String.fields (fn c => c = Char.chr 0) name)
    in
      [("garbage positions", space_implode separator (fields @ ["garbage"])),
       ("truncated positions", String.substring (name, 0, size name - 3)),
       ("raw separator", name ^ "."),
       ("bad escape", name ^ escape ^ "x")]
    end
end
\<close>

ML_val \<open>
local
  open Parser_Function_Regression_Test
  open Marker_Position_Test
  val ctxt = Context_Position.set_visible true \<^context>

  (* Every backend filter form, alone and combined; no filter is the unrestricted payload. *)
  fun round_trip filters =
    let
      val name = "MarkerPosition::callee"
      val payload =
        Dispatch.mk_filtered_payload_positions filters
          Micro_Rust_Names.NFunction name positions
    in
      require "dispatch payload is not a free variable for the term decoder"
        (decodes_as_free ctxt payload);
      (case Dispatch.dest_payload payload of
         SOME (decoded_kind, decoded_name, decoded, decoded_filters) =>
           require "dispatch payload did not round-trip its tag and positions"
             (decoded_kind = Micro_Rust_Names.NFunction andalso
               decoded_name = name andalso decoded_filters = filters andalso
               same_marker_positions positions decoded)
       | NONE => error "dispatch payload was not recognised")
    end
  val _ =
    List.app round_trip
      [[], [Micro_Rust_Names.Exclude_Generated], [Micro_Rust_Names.Exclude_Method_Only],
       [Micro_Rust_Names.Only_Sources [1, 2]], [Micro_Rust_Names.Only_Sources []],
       [Micro_Rust_Names.Only_Sources [1, 1]],
       [Micro_Rust_Names.Exclude_Generated, Micro_Rust_Names.Exclude_Method_Only]]

  val _ =
    (case Dispatch.dest_payload
        (Dispatch.mk_payload Micro_Rust_Names.NFunction "MarkerPositionCallee" hostile) of
       SOME (_, _, decoded, []) =>
         require "single-position payload did not round-trip its position"
           (same_marker_positions
             {terminal_pos = hostile, qualifier_positions = [],
              backend_only_positions = []}
             decoded)
     | _ => error "single-position payload was not recognised")

  (* A turbofish call head re-encodes the decoded positions of its marker. *)
  val restricted =
    Dispatch.mk_marker_positions_with_backend_targets Micro_Rust_Names.NFunction
      "MarkerPosition::callee" dotted [labelled, Position.none, unfiled] [hostile]
      (Free ("callee", dummyT))
    |> Dispatch.exclude_generated_backends
  val _ =
    (case Dispatch.dest_marker_untyped restricted of
       SOME ((_, _, decoded, [Micro_Rust_Names.Exclude_Generated]),
             SOME (Free ("callee", _))) =>
         require "restricted marker did not keep its positions"
           (same_marker_positions positions decoded)
     | _ => error "restricted marker lost its explicit scope or witness")

  val navigation_positions = [dotted, labelled, hostile]
  val (marked, _) =
    Navigation.capture (fn () =>
      Navigation.with_source navigation_positions (fn () =>
        Navigation.mark Navigation.Primary \<^term>\<open>Suc\<close>))
  val _ =
    (case marked of
       Const (\<^const_name>\<open>semantic_navigation_target\<close>, _) $ payload $ _ =>
         require "navigation payload is not a free variable for the term decoder"
           (decodes_as_free ctxt payload)
     | _ => error "navigation target was not marked")
  val (_, deferred) = Navigation.capture (fn () => Syntax.check_term ctxt marked)
  val ((), replayed) =
    Parser_Test_Reports.markup (fn () => Navigation.replay ctxt deferred)
  val _ =
    List.app
      (fn position =>
        require "navigation target was not reported at its exact position"
          (exists
            (fn (markup_name, properties) =>
              markup_name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME Markup.constantN andalso
              Properties.get properties Markup.nameN = SOME \<^const_name>\<open>Suc\<close> andalso
              same_positions [Position.of_properties properties] [position])
            replayed))
      navigation_positions
in val _ = () end
\<close>

ML_val \<open>
local
  open Parser_Function_Regression_Test
  open Marker_Position_Test

  (* The shared codec inverts exactly its own encodings. *)
  val all_positions = [dotted, labelled, Position.none, unfiled, hostile]
  val _ =
    require "shared position codec did not round-trip"
      (case Navigation.decode_positions (Navigation.encode_positions all_positions) of
         SOME decoded => same_positions all_positions decoded
       | NONE => false)
  val hostile_name = the (Position.file_of hostile)
  val _ =
    require "shared payload-name escape did not round-trip"
      (Navigation.unescape_payload_name (Navigation.escape_payload_name hostile_name) =
        SOME hostile_name)
  val _ =
    require "shared codec accepted input that no encoding produced"
      (forall (is_none o Navigation.decode_positions) ["garbage", "\005\006:\005"] andalso
       forall (is_none o Navigation.unescape_payload_name)
         ["marker.position", escape, escape ^ "x", "marker" ^ escape])
in val _ = () end
\<close>

ML_val \<open>
local
  open Parser_Function_Regression_Test
  open Marker_Position_Test
  val ctxt = Context_Position.set_visible true \<^context>

  val dispatch_name =
    payload_name
      (Dispatch.mk_payload_positions
        Micro_Rust_Names.NFunction "MarkerPosition::callee" positions)
  val dispatch_corruptions =
    (case String.fields (fn c => c = Char.chr 0) dispatch_name of
       [tag, name, _, encoded] =>
         [("non-numeric count", space_implode separator [tag, name, "x", encoded]),
          ("negative count", space_implode separator [tag, name, "~1", encoded]),
          ("count beyond the positions", space_implode separator [tag, name, "9", encoded])] @
         map (fn field => ("malformed filters " ^ quote field,
           space_implode separator [tag, name, "2", encoded, field]))
           ["", "bogus", "sources", "sources x", "sources ~1", "sources 1 ",
            "generated,", ",generated", "generated,generated",
            "method_only,method_only", "empty_sources,empty_sources", "sources 1,sources 1"]
     | _ => error "dispatch payload has an unexpected layout")
  val _ =
    List.app
      (fn (label, corrupted) =>
        require ("dispatch payload with " ^ label ^ " was not rejected as malformed")
          (rejected "malformed urust_dispatch payload"
            (fn () => Dispatch.dest_payload (Free (corrupted, dummyT)))))
      (corruptions dispatch_name @ dispatch_corruptions)

  val navigation_name =
    (case
        Navigation.capture (fn () =>
          Navigation.with_source [dotted, labelled, hostile] (fn () =>
            Navigation.mark Navigation.Primary \<^term>\<open>Suc\<close>)) of
       (_ $ payload $ _, _) => payload_name payload
     | _ => error "navigation target was not marked")
  val _ =
    List.app
      (fn (label, corrupted) =>
        require ("navigation payload with " ^ label ^ " was not rejected as malformed")
          (rejected "Micro_Rust_Semantic_Navigation: malformed target payload"
            (fn () =>
              Navigation.capture (fn () =>
                Syntax.check_term ctxt
                  (Const (\<^const_name>\<open>semantic_navigation_target\<close>, dummyT) $
                    Free (corrupted, dummyT) $ \<^term>\<open>Suc\<close>)))))
      (corruptions navigation_name)
in val _ = () end
\<close>

ML_val \<open>
local
  open Parser_Function_Regression_Test
  val declared =
    run_from (initial \<^theory>) "marker-position-declaration"
      (command "" "marker_position_callee"
        "fn MarkerPositionCallee(value: u8) -> u8 { value }" ^
       "\nmicro_rust_notation (call) marker_position_callee (\"MarkerPosition::callee\")" ^
       "\nmicro_rust_notation (call) marker_position_callee (\"MarkerPosition::callee!\")" ^
       "\ndefinition marker_position_value :: " ^ cartouche "8 word" ^
         " where " ^ cartouche "marker_position_value = 3" ^
       "\nmicro_rust_notation (literal) marker_position_value (\"MarkerPosition::VALUE\")")
  val callee =
    Proof_Context.intern_const (Toplevel.context_of declared) "marker_position_callee"
  val value =
    Proof_Context.intern_const (Toplevel.context_of declared) "marker_position_value"

  val label = "marker-position-client"
  val text =
    command "[register_notation = false]" "marker_position_client"
      "fn MarkerPositionClient(value: u8) -> u8 { \
      \let first = MarkerPositionCallee(value); \
      \let second = MarkerPosition::callee(first); \
      \let third = MarkerPosition::VALUE; \
      \MarkerPosition::callee!(second) }"
  val (_, markup) =
    Parser_Test_Reports.markup (fn () => run_from declared label text)

  fun site context offset needle =
    token_position text (start label) needle (find_from text context 0 + offset)
  val plain = site "MarkerPositionCallee(" 0 "MarkerPositionCallee"
  val path_qualifier = site "MarkerPosition::callee(" 0 "MarkerPosition"
  val path_terminal = site "MarkerPosition::callee(" 16 "callee"
  val literal_qualifier = site "MarkerPosition::VALUE" 0 "MarkerPosition"
  val literal_terminal = site "MarkerPosition::VALUE" 16 "VALUE"
  val macro_qualifier = site "MarkerPosition::callee!(" 0 "MarkerPosition"
  val macro_terminal = site "MarkerPosition::callee!(" 16 "callee"
  val macro_bang = site "MarkerPosition::callee!(" 22 "!"

  fun at position =
    filter (fn (_, properties) => has_position properties position) markup
  fun entity_at kind name position =
    exists
      (fn (markup_name, properties) =>
        markup_name = Markup.entityN andalso
        Properties.get properties Markup.kindN = SOME kind andalso
        Properties.get properties Markup.nameN = SOME name)
      (at position)
  fun styled_at position =
    exists (fn (markup_name, _) => markup_name = Markup.keyword3N) (at position)

  val _ =
    List.app
      (fn (notation, backend, position) =>
        (require (notation ^ ": use site lost its constant reference")
           (entity_at Markup.constantN backend position);
         require (notation ^ ": use site lost its keyword3 styling") (styled_at position);
         require (notation ^ ": use site lost its notation reference")
           (entity_at Micro_Rust_Names.notationN notation position)))
      [("MarkerPositionCallee", callee, plain),
       ("MarkerPosition::callee", callee, path_terminal),
       ("MarkerPosition::VALUE", value, literal_terminal),
       ("MarkerPosition::callee!", callee, macro_terminal)]
  val _ =
    List.app
      (fn (notation, position) =>
        require (notation ^ ": qualifier lost its notation reference")
          (entity_at Micro_Rust_Names.notationN notation position))
      [("MarkerPosition::callee", path_qualifier),
       ("MarkerPosition::VALUE", literal_qualifier),
       ("MarkerPosition::callee!", macro_qualifier)]
  val _ =
    require "macro bang lost its selected backend target"
      (entity_at Markup.constantN callee macro_bang)

  (* PIDE assigns a report with a foreign file to that file, never to the node at its offsets.
     Every positioned report of the client, dispatch or not, must therefore keep its file. *)
  val positioned =
    filter (fn (_, properties) => is_some (Properties.get properties Markup.offsetN)) markup
  val _ =
    require "the client reported no use-site markup"
      (forall (not o null o at)
        [plain, path_qualifier, path_terminal, literal_qualifier, literal_terminal,
         macro_qualifier, macro_terminal, macro_bang])
  val _ =
    require "a use-site report lost the file of its source"
      (forall
        (fn (_, properties) => Properties.get properties Markup.fileN = SOME label)
        positioned)
in val _ = () end
\<close>

chapter\<open> Declared HOL types \<close>

section\<open> Literal Rust type surface \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    val declared_text = "nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body"
    val expected_type = \<^typ>\<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
    val expected_body = \<^term>\<open>\<lambda>x::nat. FunctionBody (literal x)
      :: (unit, nat, unit, unit, unit) function_body\<close>
    val base = initial \<^theory>
    fun check (label, item) =
      let
        val function = parse ctxt label item
        val printed = URust_Printer.string_of_function URust_Printer.serialized_options function
        val reparsed = parse ctxt (label ^ "-printed") printed
        val _ = require (label ^ ": native type printer added a HOL escape")
          (not (String.isSubstring "\<tau>" printed))
        val _ = require (label ^ ": type syntax did not round-trip")
          (URust_Printer.tokens_of_function URust_Printer.serialized_options function =
            URust_Printer.tokens_of_function URust_Printer.serialized_options reparsed)
        val result = run_from base label
          (command "[pp_test]" ("native_surface :: " ^ cartouche declared_text) item)
          |> Toplevel.context_of
        val _ = require (label ^ ": Rust surface constrained the declared HOL type")
          (declared_type result "native_surface" = expected_type)
        val _ = require (label ^ ": Rust surface changed the function body")
          (Term.aconv_untyped (rhs result "native_surface", expected_body))
      in () end
    val _ = List.app check
      [("native-function-pointer", "fn NativeSurface(value: fn(&Element) -> bool) -> bool { value }"),
       ("native-function-pointer-unit", "fn NativeSurface(value: fn()) { value }"),
       ("native-function-pointer-one", "fn NativeSurface(value: fn(u32)) { value }"),
       ("native-function-pointer-one-trailing", "fn NativeSurface(value: fn(u32,)) { value }"),
       ("native-function-pointer-two", "fn NativeSurface(value: fn(u32, u64)) { value }"),
       ("native-function-pointer-trailing-comma",
        "fn NativeSurface(value: fn(u8, bool,) -> fn() -> u64) { value }"),
       ("native-lifetime-argument",
        "fn NativeSurface<'a, 'b>(value: Cursor<'a, Inner<'b, Element>>) \
        \-> Cursor<'static, Inner<'_, Element>> { value }"),
       ("native-associated-type",
        "fn NativeSurface(value: Iterator<Item = (Element, &Unknown)>) { value }"),
       ("native-impl-trait",
        "fn NativeSurface(value: Element) -> impl Iterator<Item = (Element, u64)> { value }"),
       ("native-const-parameter",
        "fn NativeSurface(value: Buffer<{ Flavor::Small as usize }>) { value }"),
       ("native-const-result",
        "fn NativeSurface(value: Element) -> Buffer<{ (Flavor::Small as usize) + 1 }> { value }"),
       ("native-const-nested-block",
        "fn NativeSurface(value: Buffer<{ { let size = 1; /* \<alpha> */ size + 1 } }>) { value }"),
       ("native-const-after-adjacent-closers",
        "fn NativeSurface(value: Outer<Middle<Inner<u32>>, {1}>) { value }"),
       ("native-const-after-spaced-closers",
        "fn NativeSurface(value: Outer<Middle<Inner<u32> >, {1}>) { value }"),
       ("native-const-result-after-adjacent-closers",
        "fn NativeSurface(value: Element) -> Outer<Middle<Inner<u32>>, {1}> { value }"),
       ("native-const-two-adjacent-closer-groups",
        "fn NativeSurface(value: Outer<Next<Middle<Inner<u32>>, {1}>, {2}>) { value }"),
       ("native-macro-type",
        "fn NativeSurface(value: $Scalar) -> FieldValue<$Scalar, Register> { value }")]

    fun reject (label, expected, item) =
      let
        val result = Exn.capture (run_from base label)
          (command "" ("native_surface :: " ^ cartouche declared_text) item)
        val diagnostic = message result
        val _ = require (label ^ ": wrong native syntax diagnostic")
          (String.isSubstring expected diagnostic)
        val _ = require (label ^ ": missing native source position")
          (not (null (diagnostic_ranges diagnostic)))
      in () end
    val _ = List.app reject
      [("native-undeclared-lifetime", "undeclared lifetime \"'a\"",
        "fn NativeSurface(value: Cursor<'a, Element>) { value }"),
       ("native-associated-type-missing", "syntax error",
        "fn NativeSurface(value: Iterator<Item = >) { value }"),
       ("native-function-pointer-missing", "syntax error",
        "fn NativeSurface(value: fn(&)) { value }"),
       ("native-function-pointer-double-trailing", "syntax error",
        "fn NativeSurface(value: fn(u32,,)) { value }"),
       ("native-function-pointer-two-double-trailing", "syntax error",
        "fn NativeSurface(value: fn(u32, u64,,)) { value }"),
       ("native-const-unclosed", "syntax error",
        "fn NativeSurface(value: Buffer<{ 1 >) { value }")]
  in val _ = () end
\<close>

section\<open> Complete declared schemes \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt
    fun same_type name expected =
      require (name ^ ": declared type changed")
        (Sign.typ_equiv thy (declared_type ctxt name, Logic.varifyT_global expected))
    val _ =
      same_type "declared_identity"
        \<^typ>\<open>nat \<Rightarrow>
          ('s::cancellative_sepalg, nat, bool, nat prompt, unit prompt_output) function_body\<close>
    val _ =
      same_type "declared_unsupported_types"
        \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
    val _ =
      same_type "declared_omitted_return" \<^typ>\<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
    val _ =
      same_type "declared_ignored_escapes" \<^typ>\<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
    val _ =
      same_type "declared_successor"
        \<^typ>\<open>64 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close>
    val _ = require "declared type differs from the equal Rust-resolved type"
      (Sign.typ_equiv thy (declared_type ctxt "declared_successor", declared_type ctxt "rust_successor"))
    val inferred = declared_type ctxt "declared_inferred_channels"
    val (state, result, abort, input, output) = channels inferred
    val _ = require "terminal hole lost the declared parameter or result"
      (binder_types inferred = [\<^typ>\<open>nat\<close>] andalso result = \<^typ>\<open>nat\<close>)
    val _ = independent "terminal hole channels became identified" [state, abort, input, output]
    val (state, _, _, input, output) = channels (declared_type ctxt "declared_caller")
    val _ = independent "a call fixed the declared function's channels" [state, input, output]
    val ignoring = declared_type ctxt "declared_ignores_defaults"
    val (state, _, abort, input, output) = channels ignoring
    val _ = require "scoped defaults replaced a declared channel" (abort = \<^typ>\<open>unit\<close>)
    val _ = independent "scoped defaults constrained a declared channel" [state, input, output]
  in val _ = () end
\<close>

context semantic_type_locale
begin

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val typ =
      Syntax.read_term \<^context>
        "declared_locale_identity :: 's \<Rightarrow> ('s, 's, bool, 'i, 'o) function_body"
      |> fastype_of
    val (state, result, _, _, _) = channels typ
    val _ = require "declared locale state became flexible"
      (state = \<^typ>\<open>'s\<close> andalso result = state andalso binder_types typ = [state])
  in val _ = () end
\<close>

end

section\<open> Ignored Rust types and reports \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    (* The Rust types of a declared function report no mapping use; the declared type reports its
       own native markup in the command. *)
    fun markup_of label declared =
      let
        val text =
          command "" ("declared_reports" ^ declared)
            "fn DeclaredReports(value: u64) -> u64 { value }"
        val (_, markup) = Parser_Test_Reports.markup (fn () => run_from base label text)
      in (text, markup) end
    val (resolved_text, resolved) = markup_of "declared-reports-rust" ""
    val (declared_text, declared) =
      markup_of "declared-reports-declared"
        (" :: " ^ cartouche "64 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body")
    fun rust_types text label =
      [token_position text (start label) "u64" (find_from text "value:" 0),
       token_position text (start label) "u64" (find_from text "->" 0)]
    fun mapping_at markup position =
      exists (fn (_, properties) => has_position properties position)
        (entities "micro_rust_type_mapping" markup)
    val _ = require "the Rust signature control reported no mapping use"
      (forall (mapping_at resolved) (rust_types resolved_text "declared-reports-rust"))
    val _ = require "an ignored Rust type reported a mapping use"
      (null (entities "micro_rust_type_mapping" declared))
    val word = token_position declared_text (start "declared-reports-declared") "word" 0
    val _ = require "the declared type lost its native type markup"
      (exists (fn (_, properties) => has_position properties word)
        (entities Markup.type_nameN declared))
  in val _ = () end
\<close>

section\<open> Artifacts, options, positioned failures and rollback \<close>

ML_val\<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val ctxt = Toplevel.context_of base
    val declared_text = "nat \<Rightarrow> (unit, nat, bool, nat prompt, unit prompt_output) function_body"
    val declared = " :: " ^ cartouche declared_text
    val item = "fn DeclaredArtifact(value: Unregistered) -> Unregistered { value }"
    fun run options target = run_from base "declared-artifact" (command options target item)
    val normal = run "" ("declared_artifact" ^ declared) |> Toplevel.context_of
    val application = run "[application_def]" ("declared_application" ^ declared) |> Toplevel.context_of
    val abbreviated = run "[abbrev]" ("declared_abbreviated" ^ declared) |> Toplevel.context_of
    val suppressed =
      run "[register_notation = false]" ("declared_suppressed" ^ declared) |> Toplevel.context_of
    val inferred_name = run "" declared |> Toplevel.context_of
    val _ = require "declared definition changed its type"
      (Sign.typ_equiv (Proof_Context.theory_of normal)
        (declared_type normal "declared_artifact", Syntax.read_typ ctxt declared_text))
    val _ = require "declared application definition lost its source argument"
      (is_Const (fst (Logic.dest_equals (Thm.prop_of (theorem normal "declared_artifact")))) andalso
        not (is_Const
          (fst (Logic.dest_equals (Thm.prop_of (theorem application "declared_application"))))))
    val _ = require "declared abbreviation installed a definition theorem"
      (is_none (try (fn () => theorem abbreviated "declared_abbreviated") ()))
    val _ = require "declared abbreviation changed its type"
      (Sign.typ_equiv (Proof_Context.theory_of abbreviated)
        (declared_type abbreviated "declared_abbreviated", Syntax.read_typ ctxt declared_text))
    val _ = registry_unchanged "suppressed declared function" ctxt suppressed
    val _ = require "an omitted name with a declared type lost the inferred binding"
      (Sign.typ_equiv (Proof_Context.theory_of inferred_name)
        (declared_type inferred_name "declared_artifact", Syntax.read_typ ctxt declared_text))
    val anonymous = run "" ("_" ^ declared) |> Toplevel.context_of
    val _ = require "anonymous declared function installed a constant"
      (constant_snapshot ctxt = constant_snapshot anonymous)
    val _ = registry_unchanged "anonymous declared function" ctxt anonymous

    fun reject_text label expected text =
      let
        val (result, reports) =
          Parser_Test_Reports.markup (fn () => Exn.capture (run_from base label) text)
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
        val _ =
          ignore (run_from base (label ^ "-recovery")
            (command "" ("declared_failure" ^ declared) item))
      in diagnostic end
    fun reject label expected options typ body =
      ignore (reject_text label expected
        (command options ("declared_failure :: " ^ cartouche typ) body))
    (* A count mismatch is positioned at the first surplus Rust parameter, or else at the
       declared type that expects the missing ones. *)
    fun reject_at label expected typ body needle =
      let
        val text = command "" ("declared_failure :: " ^ cartouche typ) body
        val diagnostic = reject_text label expected text
        val position = token_position text (start label) needle 0
      in
        require (label ^ ": wrong diagnostic position")
          (member (op =) (diagnostic_ranges diagnostic) (range_of position))
      end
    val _ =
      reject_at "declared-surplus-parameter" "declared type expects 1 parameter, but 2 names"
        "nat \<Rightarrow> _" "fn DeclaredFailure(value: u64, surplus: u64) -> u64 { value }" "surplus"
    val _ =
      reject_at "declared-missing-parameter" "declared type expects 2 parameters, but 1 name"
        "nat \<Rightarrow> nat \<Rightarrow> _" "fn DeclaredFailure(value: u64) -> u64 { value }"
        (cartouche "nat \<Rightarrow> nat \<Rightarrow> _")
    val body = "fn DeclaredFailure(value: u64) -> u64 { value }"
    val _ = reject "declared-terminal" "declared result type must be function_body"
      "" "nat \<Rightarrow> nat" body
    val _ = reject "declared-malformed" "Failed to parse type" "" "nat \<Rightarrow>" body
    val _ = reject "declared-undefined" "Undefined type name" "" "declared_missing_type \<Rightarrow> _" body
    val _ = reject "declared-body-mismatch" "Type unification failed"
      "" "nat \<Rightarrow> ('s, bool, _, _, _) function_body" body
    val _ = reject "declared-rigid-variable" "Type unification failed"
      "" "'a \<Rightarrow> ('s, nat, _, _, _) function_body" body
    val _ = reject "declared-abort-mismatch" "Type unification failed"
      "" "('s, unit, unit, _, _) function_body"
      "fn DeclaredFailure() { \<epsilon>\<open>abort (CustomAbort True)\<close> }"
    val _ = reject "declared-undeclared-lifetime" "undeclared lifetime \"'a\""
      "" "nat \<Rightarrow> _" "fn DeclaredFailure(value: &'a u8) -> u8 { value }"
    val _ = reject "declared-reserved-lifetime" "cannot be declared as a lifetime parameter"
      "" "nat \<Rightarrow> _" "fn DeclaredFailure<'static>(value: u8) -> u8 { value }"
    val _ =
      List.app (fn name =>
        reject ("declared-with-" ^ name) ("option " ^ quote name ^ " cannot be combined")
          ("[" ^ name ^ " = " ^ cartouche "unit" ^ "]") declared_text item)
        ["state", "abort", "input", "output"]
    val _ = reject_text "declared-rigid-locale" "Type unification failed"
      ("context semantic_type_locale begin\n" ^
        command "[register_notation = false]"
          ("declared_failure :: " ^ cartouche "('s, unit, _, _, _) function_body")
          "fn DeclaredFailure() { \<epsilon>\<open>put (\<lambda>_::unit. ())\<close> }")
    val _ = reject_text "declared-chunk-annotation" "unknown uRust command option \"type\""
      ("urust " ^
        cartouche
          ("\n  \<omega>" ^ cartouche ("type = " ^ cartouche declared_text) ^ "\n  " ^ item ^ "\n"))
  in val _ = () end
\<close>

section\<open> Implicit mapping signature sharing and complete types \<close>

ML_val\<open>
local
  open URust_AST
  structure Types = URust_Type_Mappings
  val ctxt = \<^context>
  val thy = \<^theory>
  fun require label ok = if ok then () else error ("implicit signature audit: " ^ label)
  val layout = make_source_layout Position.none []
  fun named name =
    Path_Type ([Rust_Type_Path_Segment (name, Position.none, NONE, layout)], layout)
  val primitive = Primitive_Type (DPT_U8, Position.none)
  val pointer = Raw_Pointer_Type (RPM_Mut, primitive, layout)
  val reference = Reference_Type (BM_Mut, NONE, primitive, layout)
  fun captured action = #1 (Micro_Rust_Semantic_Navigation.capture action)
  fun resolved_signature rust = captured (fn () => Types.resolve_signature ctxt rust)
  fun check_order rust =
    let
      val types = resolved_signature rust
      val address = get_first (fn Type (name, [slot]) =>
          if name = \<^type_name>\<open>function_address_model\<close> then SOME slot else NONE
        | _ => NONE) types |> the
      val global = get_first (fn Type (name, [slot]) =>
          if name = \<^type_name>\<open>function_global_model\<close> then SOME slot else NONE
        | _ => NONE) types |> the
      val pair = get_first (fn Type (name, [Type (gref, [a, g]), global, _]) =>
          if name = \<^type_name>\<open>focused\<close> andalso
            gref = \<^type_name>\<open>gref\<close> andalso g = global
          then SOME (a, g) else NONE
        | _ => NONE) types |> the
    in require "pointer/reference arrival changed a named singleton slot"
      (pair = (address, global) andalso address <> global) end
  val _ = List.app check_order
    [[named "FunctionAddress", pointer, named "FunctionGlobal"],
     [pointer, named "FunctionAddress", named "FunctionGlobal"],
     [named "FunctionGlobal", pointer, named "FunctionAddress"],
     [pointer, named "FunctionGlobal", named "FunctionAddress"],
     [named "FunctionAddress", reference, named "FunctionGlobal"],
     [reference, named "FunctionAddress", named "FunctionGlobal"],
     [named "FunctionGlobal", reference, named "FunctionAddress"],
     [reference, named "FunctionGlobal", named "FunctionAddress"]]
  val _ = List.app check_order
    [[named "FunctionTransportAddress", pointer, named "FunctionTransportAlias"],
     [pointer, named "FunctionTransportAddress", named "FunctionTransportAlias"],
     [named "FunctionTransportAlias", reference, named "FunctionTransportAddress"],
     [reference, named "FunctionTransportAlias", named "FunctionTransportAddress"]]
  fun transported_scheme name roles source_indexes =
    let
      val entry = the (Types.lookup ctxt name)
      val expected = map (pair "_urust_type") source_indexes @
        map (fn Types.Address => ("_urust_backend", 0)
          | Types.Global => ("_urust_backend", 1)) roles
      val actual = Term.add_tvarsT (Types.entry_template entry) []
    in require (name ^ ": locale export changed a canonical slot, role or sort")
      (Types.entry_backend_roles entry = roles andalso
        eq_set (op =) (map fst actual, expected) andalso
        forall (fn (_, sort) => sort = \<^sort>\<open>type\<close>) actual)
    end
  val _ = List.app (fn (name, roles, sources) => transported_scheme name roles sources)
    [("FunctionTransportAddress", [Types.Address], []),
     ("FunctionTransportGlobal", [Types.Global], []),
     ("FunctionTransportAlias", [Types.Global], []),
     ("FunctionTransportPair", [Types.Address, Types.Global], []),
     ("FunctionTransportPairAlias", [Types.Address, Types.Global], []),
     ("FunctionTransportWrapped", [Types.Address, Types.Global], [0]),
     ("FunctionTransportWrappedAlias", [Types.Address, Types.Global], [0]),
     ("FunctionRolePacket", [Types.Address, Types.Global], [])]
  val first = resolved_signature [named "FunctionAddress"]
  val second = resolved_signature [named "FunctionAddress"]
  val _ = require "independent resolutions reused flexible backend variables" (first <> second)
  val repeated = resolved_signature [named "FunctionAddress", named "FunctionAddress"]
  val _ = require "repeated mappings allocated separate address roles" (hd repeated = nth repeated 1)

  val fixed = TFree ("'urust_address", \<^sort>\<open>type\<close>)
  val fixed_ctxt = Variable.declare_typ fixed ctxt
  val channel = Types.Authored_Channel (Input.string "'urust_address")
  val complete = captured (fn () => Types.resolve_function_signature fixed_ctxt
    {state = SOME channel, abort = NONE, input = NONE, output = NONE} []
    [named "FunctionAddress"] (named "FunctionGlobal"))
  val [Type (_, [address])] = binder_types complete
  val Type (_, [state, Type (_, [global]), _, _, _]) = body_type complete
  val _ = require "role sort/spelling captured an ambient variable or computation channel"
    (state = fixed andalso address <> fixed andalso global <> fixed andalso address <> global)

  fun canonical_type typ =
    let
      val variables = Term.add_tvarsT typ [] |> rev
      val substitutions = variables |> map_index (fn (index, variable as (_, sort)) =>
        (variable, TVar (("backend_type", index), sort))) |> TVars.make
    in Term_Subst.instantiateT substitutions typ end
  fun constant_type name =
    Sign.the_const_type thy (Proof_Context.intern_const ctxt name) |> canonical_type
  val _ = List.app (fn (native, escaped) =>
    require (native ^ ": complete type/sort/channel relationships differ from escape twin")
      (constant_type native = constant_type escaped))
    [("function_address_native", "function_address_escape"),
     ("function_global_native", "function_global_escape"),
     ("function_pair_native", "function_pair_escape"),
     ("function_combined_native", "function_combined_escape")]

  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun run base label text =
    Outer_Syntax.parse_text base (K base)
      (Position.make0 1 1 0 "" label "" |> Position.copy_id (Position.thread_data ())) text
    |> (fn transitions => fold (Toplevel.command_exception false) transitions
      (Toplevel.make_state (SOME base)))
    |> Toplevel.context_of
  val aliases = captured (fn () => run thy "implicit-morphism-alias-replay"
    ("urust_type_alias " ^ cartouche "type FunctionTransportAlias = FunctionTransportGlobal;" ^
      " urust_type_alias " ^ cartouche "type FunctionTransportPairAlias = FunctionTransportPair;" ^
      " urust_type_alias " ^
        cartouche "type FunctionTransportWrappedAlias<Value> = FunctionTransportWrapped<Value>;"))
  val _ = List.app (fn name =>
    require (name ^ ": transported captured meaning was not idempotent")
      (Types.entry_identity (the (Types.lookup ctxt name)) =
        Types.entry_identity (the (Types.lookup aliases name))))
    ["FunctionTransportAlias", "FunctionTransportPairAlias", "FunctionTransportWrappedAlias"]
  val sorted = run thy "implicit-sort-fixtures"
    ("urust_type [implicit = " ^ cartouche "address = 'a" ^ "] \"FunctionFinite\" = " ^
      cartouche "'a::finite function_address_model")
  val sorted_thy = Proof_Context.theory_of sorted
  val [Type (_, [sorted_address]), Type (_, [plain_global]),
      Type (_, [Type (_, [pointer_address, pointer_global]), pointer_global', _])] =
    captured (fn () => Types.resolve_signature sorted
      [named "FunctionFinite", named "FunctionGlobal", pointer])
  val _ = require "sort refinement split or conflated roles"
    (sorted_address = pointer_address andalso plain_global = pointer_global andalso
      pointer_global = pointer_global' andalso
      Type.sort_of_atyp sorted_address = \<^sort>\<open>finite\<close> andalso
      Type.sort_of_atyp plain_global = \<^sort>\<open>type\<close>)
  val succeeded = captured (fn () => run sorted_thy "implicit-sort-compatible"
    ("urust_fn [register_notation = false] _ " ^
      cartouche ("fn FunctionSortCompatible(value: FunctionFinite) -> FunctionFinite { " ^
        "\<llangle>value :: bool function_address_model\<rrangle> }")))
  val _ = require "sort-compatible anonymous declaration leaked its generic scope"
    (is_none (Types.generic_scope succeeded))
  val incompatible = Exn.capture (fn () => captured (fn () =>
    run sorted_thy "implicit-sort-incompatible"
      ("urust_fn [register_notation = false] _ " ^
        cartouche ("fn FunctionSortIncompatible(value: FunctionFinite) -> FunctionFinite { " ^
          "\<llangle>value :: nat function_address_model\<rrangle> }")))) ()
  val _ = (case incompatible of
    Exn.Exn exn => require "concrete backend sort conflict lost native type failure"
      (String.isSubstring "Type unification failed" (Runtime.exn_message exn))
  | _ => error "implicit signature audit: an infinite backend satisfied finite")
in val _ = writeln "implicit signature roles, fresh scopes, full twins and sort controls passed" end
\<close>

ML_val\<open>
local
  val ctxt = \<^context>
  val thy = \<^theory>
  val actual = Sign.the_const_type thy \<^const_name>\<open>function_erased_backend\<close>
  val expected = Sign.the_const_type thy \<^const_name>\<open>function_erased_backend_twin\<close>
  val _ = if actual = expected andalso
    not (exists (fn ((name, _), _) => String.isPrefix "'urust_" name) (Term.add_tvarsT actual []))
    then () else error "erased function signature allocated an unused implicit backend"
  val _ = if is_none (URust_Type_Mappings.generic_scope ctxt) then ()
    else error "erased function signature leaked its generic scope"
  val _ = writeln "U2 known implicit source-only signature/native complete type twin PASS"
in end
\<close>

section\<open> Inherited impl lifetimes and isolated member headers \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  fun require label condition = if condition then () else error ("inherited lifetime regression: " ^ label)
  val ctxt = Context_Position.set_visible true \<^context>
  fun pos offset = Position.make0 1 offset 0 "" "s2-inherited-lifetimes" "s2-inherited-lifetimes"
  fun collect (XML.Text _) acc = acc
    | collect (XML.Elem (markup, body)) acc = fold collect body (markup :: acc)
  fun capture action =
    let val chunks = Unsynchronized.ref ([]: string list)
      val result = Unsynchronized.setmp Private_Output.report_fn
        (fn output => chunks := output @ !chunks)
        (fn () => Print_Mode.with_modes [Print_Mode.PIDE] action ()) ()
    in (result, fold collect (maps YXML.parse_body (!chunks)) []) end
  fun parse text offset = URust_Parser.parse_function_source ctxt
    (Parser_Lex_Util.positioned_content_source text (pos offset)) |> the
  val (prepared, declaration_reports) = capture (fn () => M.with_header_lifetimes
    [URust_AST.Rust_Lifetime ("'a", pos 1)] ctxt)
  val scoped_parameter: M.generic_parameter = {rust = "T", pos = pos 11,
    kind = URust_AST.Type_Parameter, hol = ("'lifetime_parent", \<^sort>\<open>type\<close>),
    bounds = [], report_reference = K ()}
  val prepared_with_scope = prepared |> M.with_generic_scope {parameters = [scoped_parameter]}
    |> M.with_impl_self {canonical_path = "LifetimeParent", self_type = \<^typ>\<open>nat\<close>,
      target_pos = pos 21, report_reference = K ()}
  val member_ctxt = M.inherit_header_lifetimes prepared_with_scope ctxt
  val _ = require "lifetime inheritance copies no generic, Self or availability state"
    (is_none (M.generic_scope member_ctxt) andalso is_none (M.impl_self member_ctxt) andalso
      not (M.declared_generic_scope member_ctxt))
  val (_, first) = capture (fn () => M.check_function_header member_ctxt
    (parse "fn First<'b>(one: &'a mut u8, two: &'b mut u8) {}" 101))
  val (_, second) = capture (fn () => M.check_function_header member_ctxt
    (parse "fn Second(one: &'a mut u8) {}" 201))
  fun lifetime_reports reports = reports |> map_filter (fn (name, props) =>
    if name = Markup.entityN andalso Properties.get props Markup.kindN = SOME "urust_lifetime"
      then SOME props else NONE)
  val declarations = lifetime_reports declaration_reports
  val inherited_identity = the (Properties.get (the_single declarations) Markup.defN)
  val first_lifetimes = lifetime_reports first
  val second_lifetimes = lifetime_reports second
  val _ = require "impl lifetime is declared exactly once and both members retain that identity"
    (length declarations = 1 andalso
      length (filter (fn props => Properties.get props Markup.refN = SOME inherited_identity)
        first_lifetimes) = 1 andalso
      length (filter (fn props => Properties.get props Markup.refN = SOME inherited_identity)
        second_lifetimes) = 1 andalso
      not (exists (fn props => Properties.get props Markup.defN = SOME inherited_identity)
        (first_lifetimes @ second_lifetimes)))
  val local_declarations = filter (is_some o (fn props => Properties.get props Markup.defN)) first_lifetimes
  val _ = require "member local lifetime has one declaration and one use"
    (length local_declarations = 1 andalso
      length (filter (fn props => Properties.get props Markup.refN =
        Properties.get (hd local_declarations) Markup.defN) first_lifetimes) = 1)
  fun reject label expected text offset =
    (case Exn.capture0 (fn () => M.check_function_header member_ctxt (parse text offset)) () of
       Exn.Exn (ERROR message) => require (label ^ ": " ^ message) (String.isSubstring expected message)
     | Exn.Exn exn => Exn.reraise exn
     | Exn.Res _ => error (label ^ ": unexpectedly accepted"))
  val _ = reject "local lifetime does not leak to sibling" "undeclared lifetime"
    "fn Sibling(one: &'b mut u8) {}" 301
  val _ = reject "local lifetime cannot shadow inherited declaration" "duplicate lifetime parameter"
    "fn Shadow<'a>() {}" 401
  val (_, binder_reports) = capture (fn () => M.check_function_header member_ctxt
    (parse "fn Binder<T: for<'c> Unknown<&'c mut u8>>() {}" 501))
  val _ = require "bound-local lifetime is isolated and has exact navigation"
    (length (lifetime_reports binder_reports) = 2)
  val _ = reject "bound-local lifetime does not leak" "undeclared lifetime"
    "fn AfterBinder(one: &'c mut u8) {}" 601
  val _ = reject "binder cannot shadow inherited declaration" "shadows an enclosing lifetime"
    "fn ShadowBinder<T: for<'a> Unknown<&'a mut u8>>() {}" 701
in end
\<close>


section\<open> Outlives relations reuse inherited lifetime identities \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  open URust_AST
  fun require label condition = if condition then () else error ("outlives lifetime regression: " ^ label)
  val ctxt = Context_Position.set_visible true \<^context>
  fun pos offset = Position.make0 1 offset 0 "" "s3-outlives-lifetimes" "s3-outlives-lifetimes"
  fun collect (XML.Text _) acc = acc
    | collect (XML.Elem (markup, body)) acc = fold collect body (markup :: acc)
  fun capture action =
    let val chunks = Unsynchronized.ref ([]: string list)
      val result = Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn
          (fn output => chunks := output @ !chunks)
          (fn () => Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
    in (result, fold collect (maps YXML.parse_body (!chunks)) []) end
  fun parse text offset = URust_Parser.parse_function_source ctxt
    (Parser_Lex_Util.positioned_content_source text (pos offset)) |> the
  fun lifetime_reports reports = reports |> map_filter (fn (name, props) =>
    if name = Markup.entityN andalso Properties.get props Markup.kindN = SOME "urust_lifetime"
      then SOME props else NONE)
  val (parent, reports) = capture (fn () => M.with_header_lifetimes
    [Rust_Lifetime ("'a", pos 1), Rust_Lifetime ("'b", pos 11)] ctxt)
  val declarations = lifetime_reports reports
  fun declaration name = the_single (map_filter (fn props =>
    if Properties.get props Markup.nameN = SOME name then Properties.get props Markup.defN
    else NONE) declarations)
  val member = M.inherit_header_lifetimes parent ctxt
  val (_, first) = capture (fn () => M.check_function_header member
    (parse "fn First<'c: 'd, 'd: 'c, T: 'a>(one: &'c mut u8) where 'a: 'b + 'a, 'c: 'b, T: 'd {}" 101))
  val (_, second) = capture (fn () => M.check_function_header member
    (parse "fn Second<'c: 'a>() where 'b: 'a {}" 301))
  val first_reports = lifetime_reports first
  val second_reports = lifetime_reports second
  fun definitions reports = map_filter (fn props =>
    Option.map (pair (the (Properties.get props Markup.nameN)))
      (Properties.get props Markup.defN)) reports
  val _ = require "inherited declarations are emitted once and retained through member bounds"
    (length declarations = 2 andalso length (definitions first_reports) = 2 andalso
      length (definitions second_reports) = 1 andalso
      forall (fn name => exists (fn props => Properties.get props Markup.refN = SOME (declaration name))
        first_reports) ["'a", "'b"])
  val first_c = the (AList.lookup (op =) (definitions first_reports) "'c")
  val first_d = the (AList.lookup (op =) (definitions first_reports) "'d")
  val second_c = the (AList.lookup (op =) (definitions second_reports) "'c")
  val _ = require "forward/cyclic member bounds navigate to actual local declarations"
    (exists (fn props => Properties.get props Markup.refN = SOME first_d) first_reports andalso
      exists (fn props => Properties.get props Markup.refN = SOME first_c) first_reports andalso
      first_c <> second_c andalso first_d <> second_c)
  fun reject text expected offset =
    (case Exn.capture0 (fn () => M.check_function_header member (parse text offset)) () of
      Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else
        require "mis-scoped member bound retains native error"
          (String.isSubstring expected (Runtime.exn_message exn))
    | Exn.Res _ => error "mis-scoped member bound was accepted")
  val _ = reject "fn Sibling() where 'c: 'a {}" "undeclared lifetime" 501
  val _ = reject "fn Shadow<'a: 'b>() {}" "duplicate lifetime parameter" 601
  val _ = reject "fn Local<T: for<'z> Unknown<&'z u8>>() where T: 'z {}" "undeclared lifetime" 701
  val (_, placeholder) = capture (fn () => M.check_function_header ctxt
    (parse "fn Placeholder(value: &'_ mut u8) -> &'_ mut u8 { value }" 801))
  val _ = require "reference-use placeholders retain their existing scope behavior"
    (null (lifetime_reports placeholder))
  val _ = require "outlives reference erasure preserves every channel and native type variable"
    (Sign.the_const_type \<^theory> \<^const_name>\<open>function_outlives_carry\<close> =
      Sign.the_const_type \<^theory> \<^const_name>\<open>function_outlives_carry_plain\<close>)
  val _ = require "lifetime checks do not publish generic or Self scopes"
    (is_none (M.generic_scope member) andalso is_none (M.impl_self member))
  val _ = writeln "S3 inherited/local/forward/cyclic/repeated lifetime IDs, sibling isolation, placeholder compatibility and exact reference channels PASS"
in end
\<close>

section\<open> Scoped model parameter boundaries \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  structure P = URust_Model_Parameters
  val ctxt = \<^context>
  fun require label condition = if condition then () else error ("scoped model parameters: " ^ label)
  fun source text = Input.string text
  fun binding key text = ((key, Position.none), source text)
  fun rejects expected action =
    case Exn.capture0 action () of
      Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else
        require expected (String.isSubstring expected (Runtime.exn_message exn))
    | Exn.Res _ => error ("scoped model parameters accepted " ^ expected)
  val requirements = M.model_parameter_requirements ctxt
  val fixed = M.with_model_parameters [binding "address" "nat", binding "global" "unit"] ctxt
  val _ = require "bindings retain concrete types"
    (#typ (the (P.lookup fixed M.Address)) = HOLogic.natT andalso
      #typ (the (P.lookup fixed M.Global)) = HOLogic.unitT)
  val _ = require "the caller context is unchanged" (is_none (P.lookup ctxt M.Address))
  val removed = M.with_model_parameters [binding "address" "_"] fixed
  val _ = require "removal leaves other selected roles intact"
    (#typ (the (P.lookup removed M.Address)) = dummyT andalso
      #typ (the (P.lookup removed M.Global)) = HOLogic.unitT)
  val _ = rejects "unknown model parameter" (fn () =>
    M.with_model_parameters [binding "unregistered_family" "nat"] ctxt)
  val _ = rejects "duplicate model parameter" (fn () =>
    M.with_model_parameters [binding "address" "nat", binding "address" "int"] ctxt)
  val _ = rejects "conflicting model parameter" (fn () =>
    P.merge_bindings (Symtab.make [("address", {typ = HOLogic.natT, pos = Position.none})],
      Symtab.make [("address", {typ = \<^typ>\<open>int\<close>, pos = Position.none})]))
  val _ = rejects "conflicting model parameter" (fn () =>
    P.merge_bindings (Symtab.make [("address", {typ = \<^typ>\<open>int\<close>, pos = Position.none})],
      Symtab.make [("address", {typ = HOLogic.natT, pos = Position.none})]))
  val _ = require "named families use independent canonical slots"
    (P.canonical (M.Model "stamp") <> P.canonical M.Address andalso
      P.canonical (M.Model "stamp") <> P.canonical M.Global)
  val _ = require "canonical family order is stable"
    (P.order [M.Model "z", M.Global, M.Model "a", M.Address] =
      [M.Address, M.Global, M.Model "a", M.Model "z"])
  val holder = the (M.lookup ctxt "ScopedParameterHolder")
  val alias = the (M.lookup ctxt "ScopedParameterAlias")
  val inner_alias = the (M.lookup ctxt "ScopedParameterInnerAlias")
  val _ = require "aliases retain complete model-family metadata"
    (M.entry_backend_roles holder = [M.Model "stamp"] andalso
      M.entry_backend_roles alias = [M.Model "stamp"] andalso
      M.entry_backend_roles inner_alias = [M.Model "stamp"] andalso
      M.entry_template holder = M.entry_template inner_alias)
  val _ = require "all model template variables have canonical family identities"
    (map fst (Term.add_tvarsT (M.entry_template holder) []) = [P.canonical (M.Model "stamp")])
  val probe = TFree ("'scoped_morphism_probe", \<^sort>\<open>type\<close>)
  val probe_context = Variable.declare_typ probe ctxt
  val morph = Morphism.typ_morphism "scoped model test"
    (Term.typ_subst_atomic [(probe, \<^typ>\<open>int\<close>)])
  val declaration = M.model_parameters_declaration probe_context
    [binding "address" "'scoped_morphism_probe"]
  val moved = Context.proof_of (Morphism.form (Morphism.transform morph declaration)
    (Context.Proof ctxt))
  val _ = require "checked default values are morphism transported"
    (#typ (the (P.lookup moved M.Address)) = \<^typ>\<open>int\<close>)
  fun canonical typ =
    let val variables = rev (Term.add_tvarsT typ [])
    in Term_Subst.instantiateT (TVars.make (map_index
      (fn (index, variable as (_, sort)) => (variable, TVar (("scoped", index), sort)))
      variables)) typ end
  fun constant name = Sign.the_const_type \<^theory>
    (Proof_Context.intern_const ctxt name) |> canonical
  val _ = List.app (fn name => require (name ^ ": full installed type/sort differs from twin")
      (constant name = constant (name ^ "_escape")))
    ["scoped_parameter_ignored", "scoped_parameter_alias", "scoped_parameter_override",
     "scoped_parameter_removed", "scoped_parameter_outside", "scoped_parameter_fresh_model",
     "scoped_parameter_inner_alias_reused"]
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun run base label text =
    Outer_Syntax.parse_text base (K base)
      (Position.make0 1 1 0 "" label "" |> Position.copy_id (Position.thread_data ())) text
    |> (fn transitions => fold (Toplevel.command_exception false) transitions
      (Toplevel.make_state (SOME base))) |> Toplevel.context_of
  fun captured action = #1 (URust_Report_Transaction.capture action)
  val merge_parent = Theory.end_theory \<^theory>
  fun branch name text =
    let
      val pos = Position.of_properties [(Markup.fileN, name), (Markup.lineN, "1")]
      val source = Input.source false text (pos, pos)
      val declaration = captured (fn () =>
        M.model_parameters_declaration ctxt [(("address", pos), source)])
    in Theory.begin_theory (name, Position.none) [merge_parent]
      |> Context.Theory |> Morphism.form declaration
      |> Context.the_theory |> Theory.end_theory end
  val left = branch "Scoped_Model_Merge_Nat" "nat"
  val same = branch "Scoped_Model_Merge_Nat_Again" "nat"
  val right = branch "Scoped_Model_Merge_Int" "int"
  fun merge name parents = Theory.begin_theory (name, Position.none) parents
    |> Proof_Context.init_global
  val _ = List.app (fn (label, parents) =>
    require "native compatible merge lost the selected role"
      (#typ (the (P.lookup (merge label parents) M.Address)) = HOLogic.natT))
    [("Scoped_Model_Merge_Same_Left", [left, same]),
     ("Scoped_Model_Merge_Same_Right", [same, left])]
  val _ = List.app (fn (label, parents) =>
    let
      val result = Exn.capture0 (fn () => merge label parents) ()
      val message = case result of Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
        | Exn.Res _ => error "native conflicting model-default merge was accepted"
    in require "native merge conflict lost its family or either authored position"
      (String.isSubstring "conflicting model parameter" message andalso
       String.isSubstring "Scoped_Model_Merge_Nat" message andalso
       String.isSubstring "Scoped_Model_Merge_Int" message) end)
    [("Scoped_Model_Merge_Different_Left", [left, right]),
     ("Scoped_Model_Merge_Different_Right", [right, left])]
  val sorted = captured (fn () => run \<^theory> "scoped-lazy-sort-fixture"
    ("urust_type [implicit = " ^ cartouche "address = 'a" ^ "] \"ScopedFiniteAddress\" = " ^
      cartouche "'a::finite function_address_model"))
  val infinite = M.with_model_parameters [binding "address" "int"] sorted
  val layout = URust_AST.make_source_layout Position.none []
  val pointer = URust_AST.Raw_Pointer_Type (URust_AST.RPM_Const,
    URust_AST.Primitive_Type (URust_AST.DPT_U8, Position.none), layout)
  val holes = M.with_model_parameters
    [binding "address" "_ option", binding "global" "_ option"] ctxt
  val [hole_first, hole_repeated] = captured (fn () => M.resolve_signature holes [pointer, pointer])
  val hole_again = the_single (captured (fn () => M.resolve_signature holes [pointer]))
  val _ = require "nested contextual holes are shared per role but fresh per resolution"
    (hole_first = hole_repeated andalso hole_first <> hole_again andalso
      length (Term.add_tvarsT hole_first []) = 2)
  val borrow_probe = TFree ("'scoped_borrow_probe", \<^sort>\<open>type\<close>)
  val declaration = M.model_parameters_declaration (Variable.declare_typ borrow_probe ctxt)
    [binding "address" "'scoped_borrow_probe"]
  val borrowed = TVar (("'scoped_borrowed", 9000), \<^sort>\<open>type\<close>)
  val phi = Morphism.typ_morphism "borrowed model slot"
    (Term.typ_subst_atomic [(borrow_probe, borrowed)])
  val imported = Context.proof_of (Morphism.form (Morphism.transform phi declaration)
    (Context.Proof ctxt)) |> M.with_model_parameters [binding "global" "_ option"]
  val result = the_single (#1 (URust_Report_Transaction.capture
    (fn () => M.resolve_signature imported [pointer])))
  val variables = Term.add_tvarsT result []
  val expected = (("?'scoped_borrowed", 9000), \<^sort>\<open>type\<close>)
  val _ = if member (op =) variables expected andalso
      forall (fn ((_, index), _) => index >= 9000) variables
    then writeln "imported variable keeps established parameterization PASS"
    else error ("borrowed variable was renamed: " ^ ML_Syntax.print_typ result)
  val spec: M.binding_spec =
    {parameter = {rust = "F", pos = Position.none, kind = URust_AST.Type_Parameter,
      hol = ("'f", \<^sort>\<open>type\<close>), bounds = ["Fn"], report_reference = K ()},
     declaration = M.fresh_generic_declaration_identity (),
     callables = [{origin = {path = "Fn", identity = serial (), declaration_pos = Position.none,
       bound_pos = Position.none}, inputs = [pointer, pointer],
       output = SOME (URust_AST.HOL_Type_Source (Input.string "bool"))}]}
  val scoped = M.with_binding_scope (M.prepare_binding_scope [spec] holes) holes
  val callback = URust_AST.Path_Type
    ([URust_AST.Rust_Type_Path_Segment ("F", Position.none, NONE, layout)], layout)
  fun resolve () = #1 (URust_Report_Transaction.capture (fn () =>
    M.resolve_function_signature_with_bindings scoped
      {state = NONE, abort = NONE, input = NONE, output = NONE} [] [callback]
      (URust_AST.HOL_Type_Source (Input.string "bool"))))
  fun role_variables result =
    let
      val relation = M.scope_bindings (#scope result) |> the_single
        |> M.binding_callable_relation |> the
      val [(first, _), (repeated, _)] = #inputs relation
      val _ = if first = repeated then () else error "callable repeated roles lost sharing"
    in map fst (Term.add_tvarsT first []) end
  val first_callable = role_variables (resolve ())
  val second_callable = role_variables (resolve ())
  val _ = if length first_callable = 2 andalso length second_callable = 2 andalso
      null (inter (op =) first_callable second_callable)
    then writeln "callable nested roles fresh per resolution PASS"
    else error "callable nested role freshness failed"

  val recipe = the_single (#callables spec)
  val schematic_spec: M.binding_spec =
    {parameter = #parameter spec, declaration = M.fresh_generic_declaration_identity (),
     callables = [{origin = #origin recipe,
       inputs = [URust_AST.HOL_Type_Source (Input.string "?'a.9999")],
       output = #output recipe}]}
  val schematic_context = M.with_binding_scope
    (M.prepare_binding_scope [schematic_spec] holes) holes
  val schematic_result = Exn.capture0 (fn () =>
    #1 (URust_Report_Transaction.capture (fn () =>
      M.resolve_function_signature_with_bindings schematic_context
        {state = NONE, abort = NONE, input = NONE, output = NONE} [] [callback]
        (URust_AST.HOL_Type_Source (Input.string "bool"))))) ()
  val _ = case schematic_result of Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else if String.isSubstring "Illegal schematic type variable" (Runtime.exn_message exn)
        then writeln "authored schematic callable source remains rejected PASS"
      else Exn.reraise exn
    | Exn.Res _ => error "authored schematic callable source was accepted"

  val combined = M.with_binding_scope (M.prepare_binding_scope [spec] imported) imported
  fun resolve_combined context = #1 (URust_Report_Transaction.capture (fn () =>
    M.resolve_function_signature_with_bindings context
      {state = NONE, abort = NONE, input = NONE, output = NONE} [] [callback]
      (URust_AST.HOL_Type_Source (Input.string "bool"))))
  val combined_first = resolve_combined combined
  val combined_again = resolve_combined combined
  val _ = if eq_set (op =) (inter (op =) (role_variables combined_first)
        (role_variables combined_again), [fst expected]) then
      writeln "callable imported role preserved and local hole fresh PASS"
    else error "callable import lost its variable or shared independent holes"
  val inherited = M.with_binding_scope (#scope combined_first) imported
  val inherited_result = resolve_combined inherited
  val _ = if member (op =) (role_variables inherited_result) (fst expected) then
      writeln "inherited callable high-index model variable preserved PASS"
    else error "inherited callable variable was renamed"



  val _ = require "unused sorted mapping restricted an ordinary pointer"
    (null (Term.add_tvarsT (the_single (captured (fn () =>
        M.resolve_signature (M.with_model_parameters [binding "global" "unit"] infinite)
          [pointer]))) []))
  val finite = URust_AST.Path_Type
    ([URust_AST.Rust_Type_Path_Segment ("ScopedFiniteAddress", Position.none, NONE, layout)], layout)
  val _ = rejects "does not satisfy" (fn () =>
    captured (fn () => M.resolve_signature infinite [finite]))
  fun collision parameters =
    captured (fn () => run \<^theory> "scoped-generic-collision"
      ("urust_fn [model_parameters = [\"address\" \<rightarrow> " ^ cartouche "'t" ^
        "], register_notation = false] _ " ^ cartouche
        ("fn ScopedCollision<" ^ parameters ^ ">(value: T, pointer: &mut u32) -> T { value }")))
  val _ = rejects "collides with a Rust generic" (fn () => collision "T")
  val _ = rejects "collides with a Rust generic" (fn () => collision "T, F: Fn(T) -> T")
in
  val _ = writeln "scoped model defaults, removal, context isolation, family identity, alias transport and both conflict orders PASS"
end
\<close>


ML_val\<open>
local
  val ctxt = \<^context>
in
  val _ = if forall (is_none o URust_Model_Parameters.lookup ctxt)
      [URust_Model_Parameters.Address, URust_Model_Parameters.Global,
       URust_Model_Parameters.Model "stamp"] then ()
    else error "scoped attribute bindings escaped the locale context"
end
\<close>

section\<open> Checked shared policies and signature selection \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  val thy = Proof_Context.theory_of ctxt
  fun require label condition = if condition then () else error ("shared policy audit: " ^ label)
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun run_from state label text =
    let val base = Toplevel.theory_of state
    in fold (Toplevel.command_exception false)
      (Outer_Syntax.parse_text base (K base) (Position.make0 1 1 0 "" label label)
        ("declare [[urust_verbosity = 0]] " ^ text)) state end
  fun run base label text = Toplevel.context_of (run_from (Toplevel.make_state (SOME base)) label text)
  fun policy name mode = "urust_type [shared = " ^ cartouche mode ^ "] " ^
    quote name ^ " = " ^ cartouche "bool"
  val original_entry = the (M.lookup ctxt "bool")
  val promoted = run thy "z-shared-policy-first" (policy "bool" "value")
  val selected = the (M.lookup promoted "bool")
  val _ = require "primitive policy promotion changed its mapping identity or schema"
    (M.entry_identity original_entry = M.entry_identity selected andalso
      M.entry_origin original_entry = M.entry_origin selected andalso
      M.entry_template original_entry = M.entry_template selected andalso
      M.entry_arities original_entry = M.entry_arities selected andalso
      M.entry_parameter_kinds original_entry = M.entry_parameter_kinds selected andalso
      M.entry_parameter_sorts original_entry = M.entry_parameter_sorts selected andalso
      M.entry_erased_parameters original_entry = M.entry_erased_parameters selected andalso
      M.entry_backend_roles original_entry = M.entry_backend_roles selected andalso
      M.entry_backend_parameter_sorts original_entry = M.entry_backend_parameter_sorts selected andalso
      Position.properties_of (M.entry_declaration_position original_entry) =
        Position.properties_of (M.entry_declaration_position selected))
  val again = run (Proof_Context.theory_of promoted) "a-shared-policy-repeat" (policy "bool" "value")
  val repeated = the (M.lookup again "bool")
  val _ = require "identical declaration changed the first policy's authored position"
    (Option.map (Position.properties_of o #2) (M.entry_shared_policy selected) =
      Option.map (Position.properties_of o #2) (M.entry_shared_policy repeated))
  fun repeat_at base line offset =
    let val label = "shared-policy-repeat-offset"
        val state = fold (Toplevel.command_exception false)
          (Outer_Syntax.parse_text base (K base)
            (Position.make0 line offset 0 "" label label) (policy "bool" "reference"))
          (Toplevel.make_state (SOME base))
    in Toplevel.context_of state end
  val late_author = repeat_at thy 9 900
  val earlier_repeat = repeat_at (Proof_Context.theory_of late_author) 1 1
  val _ = require "a later equal selection at an earlier source position replaced the first author"
    (Option.map (Position.properties_of o #2)
       (M.entry_shared_policy (the (M.lookup late_author "bool"))) =
     Option.map (Position.properties_of o #2)
       (M.entry_shared_policy (the (M.lookup earlier_repeat "bool"))))

  fun failure expected action =
    (case Exn.capture0 action () of
       Exn.Res _ => error ("shared policy audit accepted " ^ expected)
     | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else
         let val message = Runtime.exn_message exn
         in require ("wrong diagnostic for " ^ expected ^ ": " ^ message)
           (String.isSubstring expected message); message end)
  fun branch label text = run (Theory.begin_theory (label, Position.none) [thy]) label text
    |> Proof_Context.theory_of |> Theory.end_theory |> Proof_Context.init_global
  val reference = branch "shared-policy-reference-author" (policy "bool" "reference")
  val readonly = branch "shared-policy-readonly-author" (policy "bool" "readonly")
  fun merge left right = Theory.begin_theory ("Shared_Policy_Merge_" ^ string_of_int (serial ()), Position.none)
    [Proof_Context.theory_of left, Proof_Context.theory_of right] |> Theory.end_theory
  val _ = List.app (fn (left, right) =>
    let val message = failure "conflicting shared representations" (fn () => merge left right)
    in require "policy conflict lost an author's source position"
      (String.isSubstring "shared-policy-reference-author" message andalso
       String.isSubstring "shared-policy-readonly-author" message) end)
    [(reference, readonly), (readonly, reference)]
  val _ = List.app (fn (left, right) => require "absent policy did not join a selection"
    (Option.map #1 (M.entry_shared_policy (the (M.lookup (Proof_Context.init_global
      (merge left right)) "bool"))) = SOME M.Shared_Reference)) [(ctxt, reference), (reference, ctxt)]
  val same = branch "shared-policy-same-author" (policy "bool" "reference")
  val merged1 = M.entry_shared_policy (the (M.lookup (Proof_Context.init_global (merge reference same)) "bool"))
  val merged2 = M.entry_shared_policy (the (M.lookup (Proof_Context.init_global (merge same reference)) "bool"))
  val _ = require "equal-policy merge depends on order"
    (Option.map (fn (mode, pos) => (mode, Position.properties_of pos)) merged1 =
     Option.map (fn (mode, pos) => (mode, Position.properties_of pos)) merged2)
  val _ = ignore (failure "different Rust meanings, HOL templates or parameter sorts" (fn () =>
    run (Proof_Context.theory_of promoted) "shared-policy-schema-first"
      ("urust_type [shared = " ^ cartouche "readonly" ^ "] " ^ quote "bool" ^ " = " ^ cartouche "nat")))

  fun options pairs = "shared_references = [" ^ commas
    (map (fn (key, mode) => quote key ^ " \<rightarrow> " ^ cartouche mode) pairs) ^ "]"
  fun declaration pairs item = "urust_fn [" ^ options pairs ^ "] " ^ cartouche item
  val ordinary = "fn SharedPolicyRejected(value: &bool) -> bool { false }"
  val _ = List.app (fn (label, expected, pairs, item) => ignore
    (failure expected (fn () => run thy label (declaration pairs item))))
    [("shared-policy-unknown-key", "unknown shared-reference key", [("body", "value")], ordinary),
     ("shared-policy-unknown-slot", "unknown shared-reference slot", [("arg:1", "value")], ordinary),
     ("shared-policy-negative-slot", "unknown shared-reference slot", [("arg:-1", "value")], ordinary),
     ("shared-policy-noncanonical-slot", "unknown shared-reference slot", [("arg:00", "value")], ordinary),
     ("shared-policy-duplicate", "duplicate shared-reference override", [("arg:0", "value"), ("arg:0", "reference")], ordinary),
     ("shared-policy-unknown-generic", "unknown shared-reference generic", [("type:Missing", "value")], ordinary),
     ("shared-policy-const-generic", "requires a type parameter", [("type:N", "value")],
       "fn SharedPolicyRejected<const N: usize>(value: bool) -> bool { value }"),
     ("shared-policy-invalid-mode", "expects value, reference, or readonly", [("arg:0", "implicit")], ordinary)]
  val _ = ignore (failure "shared Rust references" (fn () => run thy "shared-policy-missing"
    ("urust_fn " ^ cartouche ordinary)))
  val _ = ignore (failure "Rust reference types" (fn () => run (Proof_Context.theory_of promoted)
    "shared-policy-field-still-unsupported"
    ("urust_datatype " ^ cartouche "struct SharedUnsupportedField { value: &bool }")))
  val _ = ignore (failure "Rust reference types" (fn () => run (Proof_Context.theory_of promoted)
    "shared-policy-alias-still-unsupported"
    ("urust_type_alias " ^ cartouche "type SharedUnsupportedAlias = &bool;")))

  val complete = "urust_fn [" ^ options [("body", "bad"), ("arg:99", "unparsed"),
      ("type:Missing", "_"), ("body", "duplicate ignored")] ^ "] shared_complete_ignored :: " ^
    cartouche "bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body" ^ " " ^
    cartouche "fn SharedCompleteIgnored(value: &UnknownSharedTarget) -> &UnknownSharedTarget { value }"
  val ignored = run thy "shared-policy-complete-ignore" complete
  val _ = require "complete HOL signature gained a denotation constraint"
    (Sign.the_const_type (Proof_Context.theory_of ignored)
      (Proof_Context.intern_const ignored "shared_complete_ignored") =
      \<^typ>\<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>)

  val callback = "fn SharedPolicyCallback<T, F: Fn(&T) -> &T>(callback: F, value: &T) -> &T { callback(value) }"
  val untouched = run thy "shared-policy-callback-slot-isolation"
    (declaration [("type:T", "value"), ("arg:0", "readonly")] callback)
  val _ = ignore (failure "Type unification failed" (fn () => run thy
    "shared-policy-callback-slot-clash"
    (declaration [("type:T", "value"), ("arg:1", "readonly")] callback)))
  val _ = require "callback slot override modified its template"
    (case binder_types (Sign.the_const_type (Proof_Context.theory_of untouched)
      (Proof_Context.intern_const untouched "shared_policy_callback")) of
       [Type ("fun", [input, Type (_, [_, output, _, _, _])]), argument] =>
         input = argument andalso output = argument
     | _ => false)

  fun canonical typ = Term_Subst.instantiateT (TVars.make
    (rev (Term.add_tvarsT typ []) |> map_index
      (fn (index, variable as (_, sort)) => (variable, TVar (("shared_twin", index), sort))))) typ
  fun constant_type name = canonical (Sign.the_const_type thy (Proof_Context.intern_const ctxt name))
  val _ = List.app (fn (native, escaped) => require (native ^ ": principal type/sorts/sharing changed")
    (constant_type native = constant_type escaped))
    [("shared_value_identity", "shared_value_identity_escape"),
     ("shared_storage_identity", "shared_storage_identity_escape"),
     ("shared_readonly_identity", "shared_readonly_identity_escape"),
     ("shared_readonly_conversion", "shared_readonly_conversion_escape"),
     ("shared_nested_signature", "shared_nested_signature_escape"),
     ("shared_slot_value", "shared_slot_value_escape"),
     ("shared_generic_value", "shared_generic_value_escape"),
     ("shared_generic_slot", "shared_generic_value_escape"),
     ("shared_callable_value", "shared_callable_value_escape"),
     ("shared_callable_mut_value", "shared_callable_value_escape"),
     ("shared_callable_once_value", "shared_callable_value_escape"),
     ("shared_alias_current_policy", "shared_alias_current_policy_escape"),
     ("shared_generated_owner_shared_peek", "shared_generated_owner_shared_peek_escape"),
     ("shared_generated_owner_shared_readonly_peek", "shared_generated_owner_shared_readonly_peek_escape")]
in end
\<close>

end
