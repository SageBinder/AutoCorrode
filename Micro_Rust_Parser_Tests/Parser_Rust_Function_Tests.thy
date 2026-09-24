theory Parser_Rust_Function_Tests
  imports Parser_Test_Utils
begin

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

urust_fn [abbrev] abbreviated_hol_name ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn AbbreviatedRustName(x: u128) -> i8 {
      x
    }
  \<close>

urust_fn [application_def, attrs = [micro_rust_simps]]
  attributed_application_function ::
  \<open>64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  \<open>
    fn AttributedApplication(x: u64) -> u64 {
      x
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

urust_fn call_inferred_function ::
  \<open>(unit, unit, unit, unit, unit) function_body\<close>
  ()
  \<open> HTTPServer() \<close>

lemma explicit_hol_name_shape:
  \<open>explicit_hol_name =
    (\<lambda>x _. FunctionBody (literal x))\<close>
  by (simp add: explicit_hol_name_def)

lemma inferred_hol_name_shape:
  \<open>http_server = FunctionBody (literal ())\<close>
  by (simp add: http_server_def)

thm rust_hol_disagreement_def
thm attributed_application_function_def
thm configured_function_def

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
  fun source text =
    Parser_Lex_Util.positioned_content_source text
      (Position.line_file 1 "rust-function-type-forms")

  val type_forms =
    source
      "fn Types(\
      \a: u8, b: i128, c: bool, d: char, e: &str, \
      \f: &mut [u64], g: *const Foo::Bar<Baz<u8>, 4>, \
      \h: *mut u16, i: [u8; 32], j: (u8, bool), \
      \k: (), l: !, m: u16, n: u32, o: u128, p: usize, \
      \q: i8, r: i16, s: i32, t: i64, u: isize) \
      \-> Outer::Result<Inner<u64>, 8> { a >> 1 }"

  val parsed =
    (case URust_Parser.parse_function_source \<^context> type_forms of
       SOME function => function
     | NONE => error "Rust function type-form source parsed as empty")

  val serialized =
    URust_Printer.string_of_function
      URust_Printer.serialized_options parsed

  val reparsed =
    (case
        URust_Parser.parse_function_source \<^context>
          (Parser_Lex_Util.text_source serialized) of
       SOME function => function
     | NONE => error "serialized Rust function parsed as empty")

  val original_tokens =
    URust_Printer.tokens_of_function
      URust_Printer.serialized_options parsed

  val reparsed_tokens =
    URust_Printer.tokens_of_function
      URust_Printer.serialized_options reparsed

  val _ =
    if original_tokens = reparsed_tokens then ()
    else error "Rust function parse-print-parse tokens changed"

  val _ =
    if String.isSubstring "Outer::Result<Inner<u64>, 8>" serialized
    then ()
    else error "nested Rust generic types were not preserved"
  val _ =
    if String.isSubstring "a >> 1" serialized
    then ()
    else error "function-body shift tokenization changed"
in
end
\<close>

ML_val\<open>
local
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
  val source_open = Symbol.open_
  val source_close = Symbol.close
  val serial = Unsynchronized.ref 0

  fun command name typ item =
    "urust_fn " ^ name ^ " :: " ^ typ ^ " " ^
      source_open ^ item ^ source_close

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
    reject "rust-function-tuple-pattern"
      "unsupported function parameter pattern"
      (command "tuple_pattern" unary_type
        "fn TuplePattern((x, y): (u64, u64)) -> u64 { x }")
  val _ =
    reject "rust-function-mut-wildcard"
      "unsupported function parameter pattern"
      (command "mut_wildcard" unary_type
        "fn MutWildcard(mut _: u64) -> u64 { 0 }")
  val _ =
    reject "rust-function-duplicate-parameter"
      "duplicate parameter \"x\""
      (command "duplicate_parameter" binary_type
        "fn DuplicateParameter(x: u64, x: u64) -> u64 { x }")
  val _ =
    reject "rust-function-parameter-count"
      "declared type expects 1 parameter"
      (command "parameter_count" unary_type
        "fn ParameterCount(x: u64, y: u64) -> u64 { x }")
  val _ =
    reject "rust-function-receiver"
      "receiver parameters are not supported"
      (command "receiver_parameter" unary_type
        "fn Receiver(self: u64) -> u64 { self }")
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
    "fn SignatureMarkup(x: u64) -> bool { x == 0 }"
  val signature_source =
    Parser_Lex_Util.positioned_content_source
      signature_text signature_start
  val (_, fn_pos) =
    position_at signature_start signature_text "fn" 0
  val (_, arrow_pos) =
    position_at signature_start signature_text "->" 0
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
    if has_markup Markup.keyword1N fn_pos signature_markup andalso
       has_markup Markup.delimiterN arrow_pos signature_markup
    then ()
    else error "function signature keyword/delimiter markup changed"

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
