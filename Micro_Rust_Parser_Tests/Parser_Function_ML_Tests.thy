(* ML audits for urust_fn declarations; the readable examples are in Parser_Function_Examples. *)

theory Parser_Function_ML_Tests
  imports
    Parser_Function_Examples
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
       ("rust-function-generics", "syntax error",
         "fn Generic<T>(x: T) -> T { x }"),
       ("rust-function-where", "syntax error",
         "fn WhereClause(x: u64) -> u64 where X: Y { x }"),
       ("rust-function-bodyless", "syntax error",
         "fn Bodyless(x: u64) -> u64;"),
       ("rust-function-malformed-type", "syntax error",
         "fn Malformed(x: &mut) -> u64 { x }"),
       ("rust-function-lifetime", "undeclared lifetime \"'a\"",
         "fn Lifetime(x: &'a mut u64) -> u64 { 0 }"),
       ("rust-function-function-pointer", "syntax error",
         "fn Pointer(x: fn(u64) -> u64) -> u64 { x }"),
       ("rust-function-associated-binding", "syntax error",
         "fn Associated(x: Iterator<Item = u8>) -> u64 { 0 }"),
       ("rust-function-impl-type", "syntax error",
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
         ("signature-untyped-receiver", "syntax error",
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
          (length (Parser_Test_Calls.entries ctxt "SignatureCoverageReplay") = 2)
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
      [("receiver-untyped-self", "syntax error", "fn BadReceiver(self) -> u8 { self }"),
       ("receiver-borrowed-shorthand", "syntax error", "fn BadReceiver(&self) -> u8 { self }"),
       ("receiver-mut-borrowed-shorthand", "syntax error", "fn BadReceiver(&mut self) -> u8 { self }"),
       ("receiver-borrowed-pattern", "unsupported function parameter pattern",
        "fn BadReceiver(&self: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { self }"),
       ("receiver-implicit-Self", "unknown Rust type", "fn BadReceiver(self: Self) -> Self { self }"),
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

  fun round_trip scope =
    let
      val name = "MarkerPosition::callee"
      val payload =
        Dispatch.mk_scoped_payload_positions scope
          Micro_Rust_Names.NFunction name positions
    in
      require "dispatch payload is not a free variable for the term decoder"
        (decodes_as_free ctxt payload);
      (case Dispatch.dest_payload payload of
         SOME (decoded_kind, decoded_name, decoded, decoded_scope) =>
           require "dispatch payload did not round-trip its tag and positions"
             (decoded_kind = Micro_Rust_Names.NFunction andalso
               decoded_name = name andalso decoded_scope = scope andalso
               same_marker_positions positions decoded)
       | NONE => error "dispatch payload was not recognised")
    end
  val _ = List.app round_trip [Dispatch.All_Backends, Dispatch.Explicit_Backends]

  val _ =
    (case Dispatch.dest_payload
        (Dispatch.mk_payload Micro_Rust_Names.NFunction "MarkerPositionCallee" hostile) of
       SOME (_, _, decoded, Dispatch.All_Backends) =>
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
       SOME ((_, _, decoded, Dispatch.Explicit_Backends), SOME (Free ("callee", _))) =>
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
      (Dispatch.mk_scoped_payload_positions Dispatch.All_Backends
        Micro_Rust_Names.NFunction "MarkerPosition::callee" positions)
  val dispatch_corruptions =
    (case String.fields (fn c => c = Char.chr 0) dispatch_name of
       [tag, name, _, encoded] =>
         [("non-numeric count", space_implode separator [tag, name, "x", encoded]),
          ("negative count", space_implode separator [tag, name, "~1", encoded]),
          ("count beyond the positions", space_implode separator [tag, name, "9", encoded])]
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

end
