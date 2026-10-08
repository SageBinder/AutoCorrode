(* Internal urust_fn regression audits. Read Parser_Function_Tests for command syntax. *)

theory Parser_Function_Regression_Tests
  imports Parser_Function_Tests
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = false]]
declare [[urust_verbosity = 0]]
declare [[urust_abbrev = false]]
declare [[urust_application_def = false]]
declare [[urust_register_notation = true]]
text\<open>
This theory checks the declarations in Parser_Function_Tests and runs isolated negative
commands. Its ML fixtures are test infrastructure; the imported function theory presents
the public syntax through ordinary declarations.
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
      (case URust_Item_Scope.lookup_function ctxt rust_name of
         SOME entry =>
           require (rust_name ^ " selected the wrong HOL artifact")
             (Term.aconv_untyped
               (URust_Item_Scope.function_term entry, Const (hol_name, dummyT)))
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
          (is_none (URust_Item_Scope.lookup_function ctxt name)))
        ["UnregisteredHelper", "ScopedUnregisteredHelper"]
  in
    ()
  end
\<close>

ML_val\<open>
  if is_none (URust_Item_Scope.lookup_function \<^context> "AnonymousProbe")
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
  (case URust_Item_Scope.lookup_function \<^context> "RustAlias" of
     SOME entry =>
       if Term.aconv_untyped
           (URust_Item_Scope.function_term entry,
            Const (\<^const_name>\<open>explicit_hol_name\<close>, dummyT))
       then ()
       else error "anonymous duplicate Rust item replaced the registered function"
   | NONE => error "anonymous duplicate Rust item removed the registered function")
\<close>

ML_val\<open>
  (case URust_Item_Scope.lookup_function \<^context> "LocaleScopedFunction" of
     SOME entry =>
       if Term.aconv_untyped
           (URust_Item_Scope.function_term entry,
            Const (\<^const_name>\<open>global_after_locale_scope\<close>, dummyT))
       then ()
       else error "locale-scoped Rust function registration leaked globally"
   | NONE => error "global declaration after locale scope was not registered");
  if is_none (URust_Item_Scope.lookup_function \<^context> "LocaleScopedClient")
  then ()
  else error "locale-scoped Rust client registration leaked globally"
\<close>

section\<open> Generated equations and declaration artifacts \<close>

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
    reject "rust-function-receiver"
      "receiver parameters are not supported"
      (command "receiver_parameter"
        "fn Receiver(self: u64) -> u64 { self }")
  val _ =
    reject "rust-function-mutable-receiver"
      "receiver parameters are not supported"
      (command "mutable_receiver_parameter"
        "fn MutableReceiver(mut self: u64) -> u64 { self }")
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
        "fn ForwardReference(x: u64) -> u64 { LaterFunction(x) }")
  val _ =
    reject "rust-function-item-as-value"
      "unresolved body name \"RustMaximumCallArity\""
      (command "function_item_as_value"
        "fn FunctionItemAsValue() -> u8 { RustMaximumCallArity }")
  val _ =
    reject "rust-function-existing-function"
      "already owned by a Rust function item"
      (command "duplicate_rust_function"
        "fn RustAlias(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-existing-constructor"
      "already owned by a Rust constructor item"
      (command "constructor_conflict"
        "fn SharedItem(x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-existing-notation"
      "conflicts with an existing micro_rust_notation"
      (command "notation_conflict"
        "fn NotationClash(x: u64) -> u64 { x }")
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
    Position.make0 7 101 0 "" label label

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
    URust_Item_Scope.dump_functions ctxt
    |> map (fn entry =>
        (URust_Item_Scope.function_rust_name entry,
         URust_Item_Scope.function_term entry,
         Position.properties_of
           (URust_Item_Scope.function_position entry)))

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

  fun registry_unchanged label earlier later =
    (require (label ^ ": function registry changed")
       (function_snapshot earlier = function_snapshot later);
     require (label ^ ": generated type registry changed")
       (type_snapshot earlier = type_snapshot later);
     require (label ^ ": constructor registry changed")
       (constructor_snapshot earlier = constructor_snapshot later);
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
          ["urust_item", "urust_constructor", "urust_field", "urust_function",
           "micro_rust_notation", "micro_rust_type_mapping"]
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

lemma signature_custom_shape:
  \<open> signature_custom = (\<lambda>value. FunctionBody (literal value)) \<close>
  by (simp only: signature_custom_def)

lemma signature_mixed_slots_shape:
  \<open> signature_mixed_slots = (\<lambda>_ _ retained _. FunctionBody (literal retained)) \<close>
  by (simp only: signature_mixed_slots_def)

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
      require "omitted return lost its inferred signature type variable"
        (inferred_result = inferred_parameter)
    val _ =
      independent "omitted return specialized an unused type variable"
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
        val entry = URust_Item_Scope.lookup_function ctxt rust
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
                            (URust_Item_Scope.function_term registered_entry),
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
        (is_none (URust_Item_Scope.lookup_function scoped_ctxt "SignatureScopedOff") andalso
          is_none (URust_Item_Scope.lookup_function scoped_ctxt "SignatureNestedOff") andalso
          is_some (URust_Item_Scope.lookup_function scoped_ctxt "SignatureRestoredOn"))

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

definition signature_existing_call ::
  \<open> 8 word \<Rightarrow> ('s, 8 word, 'abort, 'i, 'o) function_body \<close>
  where \<open> signature_existing_call value = FunctionBody (literal value) \<close>

urust_notation (call) signature_existing_call ("SignatureExistingCall")

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
            (null (entities "urust_function" markup))
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
          (is_some (URust_Item_Scope.lookup_function recovered_ctxt "SignatureFailure"));
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
         ("signature-invalid-sort", "does not satisfy sort",
          "fn SignatureFailure(value: SignatureOrdered<SignatureFunction>) { () }"),
         ("signature-unknown-hol-sort", "Undeclared class",
          "fn SignatureFailure(value: \<tau>\<open>'a::missing_signature_sort\<close>) { () }"),
         ("signature-reference", "Rust reference types",
          "fn SignatureFailure(value: &u8) { () }"),
         ("signature-mutable-reference", "Rust reference types",
          "fn SignatureFailure(value: &mut u8) { () }"),
         ("signature-raw-const-pointer", "Rust raw pointer types",
          "fn SignatureFailure(value: *const u8) { () }"),
         ("signature-raw-mut-pointer", "Rust raw pointer types",
          "fn SignatureFailure(value: *mut u8) { () }"),
         ("signature-slice", "Rust slice types",
          "fn SignatureFailure(value: [u8]) { () }"),
         ("signature-array", "Rust array types",
          "fn SignatureFailure(value: [u8; 4]) { () }"),
         ("signature-singleton-tuple", "singleton tuple types",
          "fn SignatureFailure(value: (u8,)) { () }"),
         ("signature-numeric-generic", "numeric generic arguments",
          "fn SignatureFailure(value: SignatureOption<4>) { () }"),
         ("signature-result-reference", "Rust reference types",
          "fn SignatureFailure(value: u8) -> &u8 { value }"),
         ("signature-destructuring", "unsupported function parameter pattern",
          "fn SignatureFailure((left, right): (u8, bool)) -> u8 { left }"),
         ("signature-duplicate-parameter", "duplicate parameter",
          "fn SignatureFailure(value: u8, value: bool) -> u8 { value }"),
         ("signature-receiver", "receiver parameters are not supported",
          "fn SignatureFailure(self: u8) -> u8 { self }"),
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
        [("registration-existing-function", "already owned by a Rust function item",
          "SignaturePrimitive", "u8"),
         ("registration-existing-constructor", "already owned by a Rust constructor item",
          "SignaturePacket", "SignaturePacket"),
         ("registration-existing-notation", "conflicts with an existing micro_rust_notation",
          "SignatureExistingCall", "u8")]

    val _ =
      reject "registration-disabled-still-checks-signature" "unknown Rust type"
        (item "[register_notation = false]"
          "fn SignaturePrimitive(value: MissingSignatureType) { () }")
    val _ =
      reject "registration-disabled-still-checks-body" "Type"
        (item "[register_notation = false]"
          "fn SignaturePrimitive(value: u8) -> bool { value }")
    val _ =
      reject "signature-outer-type-rejected" "Outer syntax error"
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
         ("signature-position-reference", "&u8", "&u8", "Rust reference types"),
         ("signature-position-array", "[u8; 4]", "[u8; 4]", "Rust array types"),
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
      URust_Item_Scope.lookup_function success_ctxt "SignatureNavigationCommand"
    val declaration_position = URust_Item_Scope.function_position function_entry
    val _ =
      require "successful command lost native function declaration markup"
        (not (null
          (entity_ids "urust_function" Markup.defN "SignatureNavigationCommand"
            declaration_position success_markup)))
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
        (entity_ids "urust_function" Markup.refN "SignatureNavigationCommand"
          call_position client_markup =
            entity_ids "urust_function" Markup.defN "SignatureNavigationCommand"
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
        (null (entities "urust_function" disabled_markup))
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
          (is_none (URust_Item_Scope.lookup_function alias_ctxt rust_name));
        require (label ^ ": optout emitted a synthetic function declaration")
          (null (entities "urust_function" reports));
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

section\<open> Registration context merges \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val parent = \<^theory>

    (* Independent synthetic theories exercise the real Generic_Data merge without
       requiring another imported test theory or leaking a conflicting registry. *)
    fun branch name options =
      let
        val thy = Theory.begin_theory (name, start name) [parent]
        val state =
          run_from (initial thy) name
            (command options "signature_merge_function"
              "fn SignatureMergeFunction(value: u8) -> u8 { value }")
      in Theory.end_theory (Toplevel.theory_of state) end

    fun merge name left right =
      Theory.begin_theory (name, start name) [left, right]
      |> Proof_Context.init_global

    val disabled_left =
      branch "Signature_Function_Merge_Disabled_Left" "[register_notation = false]"
    val disabled_right =
      branch "Signature_Function_Merge_Disabled_Right" "[register_notation = false]"
    val disabled =
      merge "Signature_Function_Merge_Disabled" disabled_left disabled_right
    val _ =
      require "disabled function registrations conflicted during context merge"
        (is_none (URust_Item_Scope.lookup_function disabled "SignatureMergeFunction"))
    val _ =
      List.app
        (fn name => ignore (theorem disabled (name ^ ".signature_merge_function")))
        ["Signature_Function_Merge_Disabled_Left", "Signature_Function_Merge_Disabled_Right"]

    val enabled_left = branch "Signature_Function_Merge_Enabled_Left" "[register_notation]"
    val enabled_right = branch "Signature_Function_Merge_Enabled_Right" "[register_notation]"
    val enabled_failure =
      Exn.result
        (fn () =>
          merge "Signature_Function_Merge_Enabled" enabled_left enabled_right
          |> (fn ctxt => URust_Item_Scope.lookup_function ctxt "SignatureMergeFunction")) ()
      |> message
    val _ =
      require "different enabled backends merged for one Rust function path"
        (String.isSubstring "conflicting Rust function path" enabled_failure)

    val notation_name = "Signature_Function_Merge_Call_Notation"
    val notation_context =
      Theory.begin_theory (notation_name, start notation_name) [parent]
      |> Context.Theory
      |> Micro_Rust_Names.register Micro_Rust_Names.NFunction "SignatureMergeFunction"
          \<^term>\<open>signature_existing_call\<close> (start notation_name)
    val notation_thy = notation_context |> Context.the_theory |> Theory.end_theory

    val constructor_name = "Signature_Function_Merge_Constructor"
    val constructor_state =
      Theory.begin_theory (constructor_name, start constructor_name) [parent]
      |> initial
      |> (fn state =>
          run_from state constructor_name
            ("urust_datatype signature_merge_constructor " ^
              cartouche " struct SignatureMergeFunction; "))
    val constructor_thy =
      constructor_state |> Toplevel.theory_of |> Theory.end_theory

    fun reject_merge (label, left, right, expected) =
      let
        val failure =
          Exn.result
            (fn () =>
              let
                val ctxt = merge label left right
                (* Force both owning data structures, including lazy theory merges. *)
                val _ = Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction
                  "SignatureMergeFunction"
                val _ = URust_Item_Scope.lookup_function ctxt "SignatureMergeFunction"
                val _ = URust_Item_Scope.lookup_constructor ctxt "SignatureMergeFunction"
              in () end) ()
          |> message
      in
        require (label ^ ": wrong merge conflict: " ^ failure)
          (String.isSubstring expected failure andalso
            String.isSubstring "SignatureMergeFunction" failure)
      end

    val _ =
      List.app reject_merge
        [("Signature_Function_Then_Notation_Merge", enabled_left, notation_thy,
          "conflicts with an existing micro_rust_notation (call) declaration"),
         ("Signature_Notation_Then_Function_Merge", notation_thy, enabled_left,
          "conflicts with an existing micro_rust_notation (call) declaration"),
         ("Signature_Function_Then_Constructor_Merge", enabled_left, constructor_thy,
          "already owned by a Rust constructor item"),
         ("Signature_Constructor_Then_Function_Merge", constructor_thy, enabled_left,
          "already owned by a Rust constructor item")]

    val disabled_notation =
      merge "Signature_Disabled_Function_Notation_Merge" disabled_left notation_thy
    val _ =
      require "opted-out function reserved the call-notation path during merge"
        (is_none (URust_Item_Scope.lookup_function disabled_notation "SignatureMergeFunction") andalso
          length (Micro_Rust_Names.lookups disabled_notation
            Micro_Rust_Names.NFunction "SignatureMergeFunction") = 1)
    val disabled_constructor =
      merge "Signature_Disabled_Function_Constructor_Merge" disabled_left constructor_thy
    val _ =
      require "opted-out function reserved the constructor path during merge"
        (is_none (URust_Item_Scope.lookup_function disabled_constructor "SignatureMergeFunction") andalso
          is_some (URust_Item_Scope.lookup_constructor disabled_constructor "SignatureMergeFunction"))

    val function_then_notation =
      Exn.result
        (fn () =>
          Context.Theory enabled_left
          |> Micro_Rust_Names.register Micro_Rust_Names.NFunction "SignatureMergeFunction"
              \<^term>\<open>signature_existing_call\<close>
              (start "signature-notation-replay-after-function")) ()
      |> message
    val _ =
      require "call-notation replay ignored a reserved function path"
        (String.isSubstring
          "conflicts with an existing micro_rust_notation (call) declaration"
          function_then_notation)
    val notation_then_function =
      Exn.result
        (fn () =>
          run_from (initial notation_thy) "signature-function-replay-after-notation"
            (command "" "signature_replay_after_notation"
              "fn SignatureMergeFunction(value: u8) -> u8 { value }")) ()
      |> message
    val _ =
      require "function replay ignored an occupied call-notation path"
        (String.isSubstring
          "conflicts with an existing micro_rust_notation (call) declaration"
          notation_then_function)
    val _ =
      require "synthetic merge fixtures leaked into the enclosing context"
        (is_none (URust_Item_Scope.lookup_function \<^context> "SignatureMergeFunction"))
  in
    val _ = ()
  end
\<close>

section\<open> Registration failure reports \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val function_state =
      run_from base "signature-report-function-prefix"
        (command "" "signature_report_function"
          "fn SignatureReportReserved(value: u8) -> u8 { value }")
    val function_ctxt =
      Toplevel.context_of function_state |> Context_Position.set_visible true
    val backend = \<^term>\<open>signature_existing_call\<close>

    (* Success controls prove the capture sees each declaration protocol. *)
    val notation_control_position = start "signature-notation-report-control"
    val (_, notation_control_markup) =
      Parser_Test_Reports.markup (fn () =>
        Micro_Rust_Names.register Micro_Rust_Names.NFunction "SignatureNotationReportControl"
          backend notation_control_position (Context.Proof function_ctxt))
    val _ =
      require "notation report capture did not observe the success control"
        (not (null (entity_ids "micro_rust_notation" Markup.defN
          "SignatureNotationReportControl" notation_control_position notation_control_markup)))

    val (notation_failure_result, notation_failure_markup) =
      Parser_Test_Reports.markup (fn () =>
        Exn.result
          (fn () =>
            Micro_Rust_Names.register Micro_Rust_Names.NFunction "SignatureReportReserved"
              backend (start "signature-notation-report-failure")
              (Context.Proof function_ctxt)) ())
    val notation_failure = message notation_failure_result
    val _ =
      require "reverse notation registration did not reject the occupied function path"
        (String.isSubstring
          "conflicts with an existing micro_rust_notation (call) declaration"
          notation_failure)
    val _ =
      require "failed reverse notation registration emitted declaration entities"
        (null (declaration_definitions notation_failure_markup))

    val notation_state =
      run_from base "signature-report-notation-prefix"
        "urust_notation (call) signature_existing_call (\"SignatureReportOccupied\")"
    val notation_lthy =
      Named_Target.theory_init (Toplevel.theory_of notation_state)
      |> Context_Position.set_visible true
    val item_control_position = start "signature-item-report-control"
    val (_, item_control_markup) =
      Parser_Test_Reports.markup (fn () =>
        URust_Item_Scope.register_function
          {rust_name = "SignatureItemReportControl",
           rust_pos = item_control_position,
           function = backend}
          notation_lthy)
    val _ =
      require "item report capture did not observe the success control"
        (not (null (entity_ids "urust_function" Markup.defN
          "SignatureItemReportControl" item_control_position item_control_markup)))

    (* Bypass command preflight to exercise the public declaration callback itself. *)
    val (item_failure_result, item_failure_markup) =
      Parser_Test_Reports.markup (fn () =>
        Exn.result
          (fn () =>
            URust_Item_Scope.register_function
              {rust_name = "SignatureReportOccupied",
               rust_pos = start "signature-item-report-failure",
               function = backend}
              notation_lthy) ())
    val item_failure = message item_failure_result
    val _ =
      require "reverse function callback did not reject the occupied notation path"
        (String.isSubstring
          "conflicts with an existing micro_rust_notation (call) declaration"
          item_failure)
    val _ =
      require "failed reverse function callback emitted declaration entities"
        (null (declaration_definitions item_failure_markup))
    val _ =
      require "failed notation registration changed the existing function path"
        (is_some (URust_Item_Scope.lookup_function function_ctxt "SignatureReportReserved") andalso
          null (Micro_Rust_Names.lookups function_ctxt
            Micro_Rust_Names.NFunction "SignatureReportReserved"))
    val _ =
      require "failed function callback changed the existing notation path"
        (is_none (URust_Item_Scope.lookup_function notation_lthy "SignatureReportOccupied") andalso
          length (Micro_Rust_Names.lookups notation_lthy
            Micro_Rust_Names.NFunction "SignatureReportOccupied") = 1)
  in
    val _ = ()
  end
\<close>

section\<open> Repeated locale interpretations \<close>

context signature_registration_disabled
begin

ML_val \<open>
  val _ =
    Parser_Function_Regression_Test.require "disabled locale registered a Rust path"
      (is_none (URust_Item_Scope.lookup_function \<^context> "SignatureRepeatedLocale"))
\<close>

end

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val first =
      run_from base "signature-enabled-first-interpretation"
        ("interpretation signature_enabled_first: signature_registration_enabled 1\n" ^
          "by unfold_locales")
    val first_ctxt = Toplevel.context_of first
    val SOME first_entry =
      URust_Item_Scope.lookup_function first_ctxt "SignatureRepeatedEnabled"
    val failure =
      Exn.result
        (fn () =>
          run_from first "signature-enabled-second-interpretation"
            ("interpretation signature_enabled_second: signature_registration_enabled 2\n" ^
              "by unfold_locales")) ()
      |> message
    val _ =
      require "enabled repeat interpretation did not report a function mapping conflict"
        (String.isSubstring "function" failure andalso
          (String.isSubstring "conflict" failure orelse
            String.isSubstring "already mapped" failure))
    val SOME retained =
      URust_Item_Scope.lookup_function
        (Toplevel.context_of first) "SignatureRepeatedEnabled"
    val _ =
      require "failed repeat interpretation changed the first function mapping"
        (Term.aconv
          (URust_Item_Scope.function_term first_entry,
           URust_Item_Scope.function_term retained))
    val _ =
      require "disabled interpretations leaked a Rust path globally"
        (is_none (URust_Item_Scope.lookup_function \<^context> "SignatureRepeatedLocale"))
    val _ =
      require "isolated enabled interpretation leaked into the surrounding theory"
        (is_none (URust_Item_Scope.lookup_function \<^context> "SignatureRepeatedEnabled"))
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = initial \<^theory>
    val first =
      run_from base "signature-type-only-first-interpretation"
        ("interpretation signature_type_only_first: signature_type_only_registration " ^
          quote "TYPE(nat)" ^ "\nby unfold_locales")
    val first_ctxt = Toplevel.context_of first
    val SOME first_entry =
      URust_Item_Scope.lookup_function first_ctxt "SignatureTypeOnlyFunction"
    val first_term = URust_Item_Scope.function_term first_entry
    val (_, first_result, _, _, _) = channels (fastype_of first_term)
    val _ =
      require "type-only interpretation did not instantiate the function at nat"
        (binder_types (fastype_of first_term) = [\<^typ>\<open>nat\<close>] andalso
          first_result = \<^typ>\<open>nat\<close>)

    val identical =
      run_from first "signature-type-only-identical-interpretation"
        ("interpretation signature_type_only_identical: signature_type_only_registration " ^
          quote "TYPE(nat)" ^ "\nby unfold_locales")
    val identical_ctxt = Toplevel.context_of identical
    val SOME identical_entry =
      URust_Item_Scope.lookup_function identical_ctxt "SignatureTypeOnlyFunction"
    val _ =
      require "identical type-only interpretation changed the typed function mapping"
        (Term.aconv
          (apply2 Term_Subst.zero_var_indexes
            (first_term, URust_Item_Scope.function_term identical_entry)))

    val different_failure =
      Exn.result
        (fn () =>
          run_from identical "signature-type-only-different-interpretation"
            ("interpretation signature_type_only_different: signature_type_only_registration " ^
              quote "TYPE(bool)" ^ "\nby unfold_locales")) ()
      |> message
    val _ =
      require "different type-only interpretation reused the nat function mapping"
        (String.isSubstring "SignatureTypeOnlyFunction" different_failure andalso
          (String.isSubstring "conflicting Rust function path" different_failure orelse
            String.isSubstring "already mapped to a different HOL function" different_failure))
    val _ =
      registry_unchanged "failed type-only interpretation" identical_ctxt
        (Toplevel.context_of identical)

    (* These terms have the same constant and value syntax; only their types differ.
       Exercise the two public registration owners separately. *)
    fun bool_instance (Type (name, arguments)) =
          if name = \<^type_name>\<open>nat\<close> andalso null arguments then \<^typ>\<open>bool\<close>
          else Type (name, map bool_instance arguments)
      | bool_instance typ = typ
    val bool_term =
      Term.map_types bool_instance first_term
    val normalized_instances =
      apply2 Term_Subst.zero_var_indexes (first_term, bool_term)
    val (_, bool_result, _, _, _) = channels (fastype_of bool_term)
    val _ =
      require "type-only conflict fixture changed value syntax"
        (Term.aconv_untyped normalized_instances andalso
          not (Term.aconv normalized_instances) andalso
          binder_types (fastype_of bool_term) = [\<^typ>\<open>bool\<close>] andalso
          bool_result = \<^typ>\<open>bool\<close>)
    val identical_reservation =
      Micro_Rust_Names.reserve_function_item "SignatureTypeOnlyFunction" first_term
        (start "signature-type-only-identical-reservation")
        (Context.Theory (Toplevel.theory_of identical))
    val _ =
      require "identical reservation changed the existing function entry"
        (case URust_Item_Scope.lookup_function
            (Context.proof_of identical_reservation) "SignatureTypeOnlyFunction" of
           SOME entry =>
             Term.aconv
               (apply2 Term_Subst.zero_var_indexes
                 (first_term, URust_Item_Scope.function_term entry))
         | NONE => false)
    val reservation_failure =
      Exn.result
        (fn () =>
          Micro_Rust_Names.reserve_function_item "SignatureTypeOnlyFunction" bool_term
            (start "signature-type-only-different-reservation")
            identical_reservation) ()
      |> message
    val _ =
      require "exclusive reservations compared only untyped function syntax"
        (String.isSubstring "conflicting Rust function path" reservation_failure)

    val item_lthy =
      Named_Target.theory_init (Toplevel.theory_of identical)
      |> Context_Position.set_visible true
    val item_failure =
      Exn.result
        (fn () =>
          URust_Item_Scope.register_function
            {rust_name = "SignatureTypeOnlyFunction",
             rust_pos = start "signature-type-only-different-item",
             function = bool_term}
            item_lthy) ()
      |> message
    val _ =
      require "item registration delegated a type-only conflict to another registry"
        (String.isSubstring "already mapped to a different HOL function" item_failure)
    val _ =
      require "isolated type-only interpretations leaked into the enclosing theory"
        (is_none (URust_Item_Scope.lookup_function \<^context> "SignatureTypeOnlyFunction"))
  in
    val _ = ()
  end
\<close>

section\<open> Schematic index replay and call freshness \<close>

ML_val \<open>
  local
    open Parser_Function_Regression_Test
    val base = Named_Target.theory_init \<^theory>
    val identity_name = \<^const_name>\<open>signature_plain_identity\<close>
    val polymorphic =
      Const (identity_name, declared_type base "signature_plain_identity")
      |> Term_Subst.zero_var_indexes
    val variables = Term.add_tvars polymorphic []
    val _ =
      require "schematic replay fixture is not a generalized HOL constant"
        (length variables > 1 andalso null (Term.add_tfrees polymorphic []))
    val index_ten = Term.map_types (Logic.incr_tvar 10) polymorphic
    val index_hundred = Term.map_types (Logic.incr_tvar 100) polymorphic
    val _ =
      require "schematic replay fixture did not change only its indices"
        (not (Term.aconv (index_ten, index_hundred)) andalso
          Term.aconv
            (apply2 Term_Subst.zero_var_indexes (index_ten, index_hundred)))

    fun register_replay term position ctxt =
      URust_Item_Scope.register_function
        {rust_name = "SignatureSchematicReplay",
         rust_pos = start position,
         function = term}
        ctxt
    val first = register_replay index_ten "signature-replay-index-ten" base
    val repeated =
      register_replay index_hundred "signature-replay-index-hundred" first
    val _ =
      registry_unchanged "same polymorphic item with different schematic indices"
        first repeated
    val SOME replayed_entry =
      URust_Item_Scope.lookup_function repeated "SignatureSchematicReplay"
    val _ =
      require "schematic replay changed the typed polymorphic backend"
        (Term.aconv
          (apply2 Term_Subst.zero_var_indexes
            (URust_Item_Scope.function_term replayed_entry, polymorphic)))

    (* Test the other owner directly, independently of the item callback. *)
    val reserved =
      Context.Theory \<^theory>
      |> Micro_Rust_Names.reserve_function_item "SignatureReservationReplay" index_ten
          (start "signature-reservation-index-ten")
      |> Micro_Rust_Names.reserve_function_item "SignatureReservationReplay" index_hundred
          (start "signature-reservation-index-hundred")
    val _ =
      require "schematic reservation replay changed ordinary notation entries"
        (notation_snapshot base = notation_snapshot (Context.proof_of reserved))

    (* Give distinct variables one spelling and different indices. Both the signature
       variable and the independent effects must retain their own identities. *)
    val mixed_substitutions =
      map_index
        (fn (index, (variable, sort)) =>
          ((variable, sort), TVar (("'signature_stored", index + 10), sort)))
        variables
      |> TVars.make
    val mixed =
      Term.map_types (Term_Subst.instantiateT mixed_substitutions) polymorphic
    val _ =
      require "mixed-index call fixture did not retain independent variables"
        (length (Term.add_tvars mixed []) = length variables andalso
          length (distinct (op =) (map (snd o fst) (Term.add_tvars mixed []))) > 1)
    val mixed_ctxt =
      URust_Item_Scope.register_function
        {rust_name = "SignatureStoredMixed",
         rust_pos = start "signature-stored-mixed-registration",
         function = mixed}
        base
    val SOME mixed_entry =
      URust_Item_Scope.lookup_function mixed_ctxt "SignatureStoredMixed"
    val _ =
      require "registration erased the mixed-index regression fixture"
        (Term.aconv (URust_Item_Scope.function_term mixed_entry, mixed))
    val SOME (URust_AST.UE_Call (URust_AST.UC_Path path, _, _)) =
      URust_Parser.parse_source mixed_ctxt
        (source "signature-stored-mixed-path" "SignatureStoredMixed(value)")

    fun resolve_call () =
      Navigation.capture (fn () =>
        URust_Item_Scope.capture_function_reports (fn () =>
          URust_Resolution.function_path mixed_ctxt
            URust_Resolution.empty_environment path 1))
      |> fst |> fst
    val first_call = resolve_call ()
    val second_call = resolve_call ()
    val first_variables = Term.add_tvars first_call []
    val second_variables = Term.add_tvars second_call []
    val _ =
      require "call resolution lost or shared stored signature/effect variables"
        (length first_variables = length variables andalso
          length second_variables = length variables andalso
          not (exists (member (op =) second_variables) first_variables))
    val _ =
      require "call freshness shifted heterogeneous indices without normalizing them"
        (length (distinct (op =) (map (snd o fst) first_variables)) = 1 andalso
          length (distinct (op =) (map (snd o fst) second_variables)) = 1)

    val mixed_call =
      Parser_Test_Elaboration.function mixed_ctxt
        {raw_type =
           ("8 word \<Rightarrow> bool \<Rightarrow> " ^
             "(_, 8 word \<times> bool \<times> tnil, _, _, _) function_body",
            start "signature-stored-mixed-call-type"),
         parameters =
           [("value", start "signature-stored-mixed-value"),
            ("flag", start "signature-stored-mixed-flag")],
         parameters_pos = start "signature-stored-mixed-parameters",
         body = source "signature-stored-mixed-body"
           "(SignatureStoredMixed(value), SignatureStoredMixed(flag))"}
    val (_, mixed_result, _, _, _) = channels (fastype_of mixed_call)
    val _ =
      require "stored mixed indices prevented two different call instantiations"
        (binder_types (fastype_of mixed_call) = [\<^typ>\<open>8 word\<close>, \<^typ>\<open>bool\<close>] andalso
          mixed_result = \<^typ>\<open>8 word \<times> bool \<times> tnil\<close>)

    (* A locale's fixed type variable is rigid even when its unused effect variables
       are schematic and need fresh instances at each call. *)
    val [mixed_value_variable] = binder_types (fastype_of mixed)

    fun ambient_call (locale_name, rust_name, label, required_sort) =
      let
        val ambient_ctxt =
          Named_Target.init [] (Locale.intern \<^theory> locale_name) \<^theory>
        val ambient = Syntax.read_typ ambient_ctxt "'a"
        val _ =
          require (label ^ ": fixture lost its rigid locale type or sort")
            (case ambient of
               TFree (name, sort) =>
                 is_some (Variable.def_sort ambient_ctxt (name, ~1)) andalso
                 Sign.subsort (Proof_Context.theory_of ambient_ctxt) (sort, required_sort)
             | _ => false)
        val rigid =
          Term.map_types (Term.typ_subst_atomic [(mixed_value_variable, ambient)]) mixed
        val rigid_ctxt =
          URust_Item_Scope.register_function
            {rust_name = rust_name,
             rust_pos = start (label ^ "-registration"),
             function = rigid}
            ambient_ctxt
        val rigid_call =
          Parser_Test_Elaboration.function rigid_ctxt
            {raw_type =
               ("'a \<Rightarrow> (_, 'a, _, _, _) function_body",
                start (label ^ "-call-type")),
             parameters = [("value", start (label ^ "-value"))],
             parameters_pos = start (label ^ "-value"),
             body = source (label ^ "-body") (rust_name ^ "(value)")}
        val (_, rigid_result, _, _, _) = channels (fastype_of rigid_call)
        val _ =
          require (label ^ ": call freshness changed an ambient fixed type or its sort")
            (binder_types (fastype_of rigid_call) = [ambient] andalso rigid_result = ambient)
        val rigid_failure =
          Exn.result
            (fn () =>
              Parser_Test_Elaboration.function rigid_ctxt
                {raw_type =
                   ("(_, bool, _, _, _) function_body",
                    start (label ^ "-rejection-type")),
                 parameters = [],
                 parameters_pos = start (label ^ "-rejection"),
                 body = source (label ^ "-rejection") (rust_name ^ "(true)")}) ()
          |> message
      in
        require (label ^ ": Boolean call instantiated an ambient rigid type variable")
          (String.isSubstring "Type" rigid_failure)
      end

    val _ =
      List.app ambient_call
        [("signature_type_only_registration", "SignatureStoredRigid",
          "signature-stored-rigid", \<^sort>\<open>type\<close>),
         ("signature_ordered_ambient", "SignatureStoredRigidOrdered",
          "signature-stored-rigid-ordered", \<^sort>\<open>linorder\<close>)]
  in
    val _ = ()
  end
\<close>

end
