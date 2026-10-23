(* ML audits for trait mappings and generic function items.
   The readable examples are in Parser_Generics_Examples. *)

theory Parser_Generics_ML_Tests
  imports Parser_Generics_Examples Micro_Rust_Parser_Impl.Parser_Impl_Chunk
begin

chapter\<open> Trait mappings \<close>

text\<open> Reserved for U1 trait-mapping audits. \<close>

chapter\<open> Syntax \<close>

text\<open>
Generic headers parse and print before signature elaboration. Type and const parameters currently
reach the temporary guard in both signature modes; these audits preserve the delivered lifetime,
receiver, datatype and retained literal-type behavior until signature support removes that guard.
\<close>

section\<open> Source positions and test support \<close>

ML\<open>
structure Generic_Syntax_Test =
struct
  open URust_AST
  fun require label condition =
    if condition then () else error ("generic syntax audit: " ^ label)
  fun start label =
    let val position = Position.make0 1 1 0 "" label label
        val thread_position = Position.thread_data ()
    in if is_some (Position.id_of thread_position)
       then Position.copy_id thread_position position else position end
  fun source label text = Parser_Lex_Util.positioned_content_source text (start label)
  fun parse ctxt label text =
    (case URust_Parser.parse_function_source ctxt (source label text) of
       SOME function => function | NONE => error (label ^ ": empty function"))
  fun chunk ctxt label text =
    (case URust_Parser.parse_chunk_source ctxt (source label text) of
       SOME chunk => chunk | NONE => error (label ^ ": empty chunk"))
  fun position_range pos =
    (the_default ~1 (Position.offset_of pos), the_default ~1 (Position.end_offset_of pos))
  fun raw_index text needle occurrence =
    let
      val target = Symbol.explode needle
      fun search _ [] _ = error ("missing test token " ^ quote needle)
        | search offset (symbols as symbol :: rest) n =
            if take (length target) symbols = target andalso n = 0 then offset
            else search (offset + size symbol) rest
              (if take (length target) symbols = target then n - 1 else n)
    in search 0 (Symbol.explode text) occurrence end
  fun range_of text needle occurrence =
    let val raw = raw_index text needle occurrence
        val start = length (Symbol.explode (String.substring (text, 0, raw))) + 1
    in (start, start + length (Symbol.explode needle)) end
  fun message_positions text =
    let
      fun collect (XML.Elem ((name, props), body)) =
            (if name = Markup.positionN then [Position.of_properties props] else []) @ maps collect body
        | collect (XML.Text _) = []
    in maps collect (YXML.parse_body text) end
  fun failure label expected action =
    (case Exn.capture action () of
       Exn.Res _ => error (label ^ ": unexpectedly accepted")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else let val message = Runtime.exn_message exn in
           require (label ^ ": wrong diagnostic " ^ message) (String.isSubstring expected message);
           message
         end)
  fun rejects ctxt (label, expected, text, needle, occurrence) =
    let val message = failure label expected (fn () => parse ctxt label text)
        val positions = map position_range (message_positions message)
    in require (label ^ ": wrong error range")
         (not (null positions) andalso hd positions = range_of text needle occurrence) end
  fun roundtrip ctxt label text =
    let
      val function = parse ctxt label text
      fun check options =
        let val generated = URust_Printer.string_of_function options function
            val reparsed = parse ctxt (label ^ "-reparsed") generated
        in require (label ^ ": printer tokens changed: " ^ generated)
             (URust_Printer.tokens_of_function options function =
              URust_Printer.tokens_of_function options reparsed) end
      val _ = List.app check [URust_Printer.serialized_options, URust_Printer.human_options]
    in function end
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun run thy label text =
    fold (Toplevel.command_exception true)
      (Outer_Syntax.parse_text thy (K thy) (start label) text) (Toplevel.make_state (SOME thy))
  fun reports action =
    let
      val (result, markup) = Parser_Test_Reports.markup action
      val events = map (fn (name, props) =>
        (name, position_range (Position.of_properties props), props)) markup
    in (result, events) end
  fun has_role events name range = exists (fn (role, at, _) => role = name andalso at = range) events
end
\<close>

section\<open> Accepted headers and printer roundtrips \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val ctxt = Context_Position.set_visible true @{context}
  val shapes =
    [("absent", "fn Plain() {}"),
     ("empty", "fn Empty<>() {}"),
     ("rust-function-parser-generics", "fn Generic<T>(value: T) -> T { value }"),
     ("types", "fn Pair<T, U,>(left: T, right: U) -> T { left }"),
     ("lifetimes", "fn Borrow<'a, 'b,>(value: &'a mut u8) -> &'a mut u8 { value }"),
     ("const", "fn Sized<const N: usize,>(value: [u8; N]) -> usize { 0 }"),
     ("mixed-type-const", "fn Mix<'a, T, const N: usize, U, const M: usize>(value: T) -> T { value }"),
     ("mixed-const-type", "fn Mix<const N: usize, T, const M: usize, U,>(value: T) -> T { value }"),
     ("inline", "fn Bounds<T: Marker + outer::inner::Scale, U: Copy>(value: T) -> T { value }"),
     ("where-only", "fn Bounds<T, U>(value: T) -> T where T: Marker, U: outer::Scale, { value }"),
     ("both-bounds", "fn Bounds<T: Marker>(value: T) -> T where T: Scale + Copy { value }"),
     ("unused", "fn Unused<T>() {}"),
     ("retained-types", "fn Retained<T>(value: impl Marker, callback: fn(T) -> T) -> impl Marker { value }"),
     ("signature-identifiers", "fn Names(for: u8, where: u8) {}"),
     ("bare-return-identifier", "fn Named(value: where) -> where { value }"),
     ("reference-return-identifier", "fn Named<T>() -> &mut where where T: Marker {}"),
     ("impl-return-identifier", "fn Named<T>() -> impl where where T: Marker {}"),
     ("function-return-identifier", "fn Named<T>() -> fn(u8) -> where where T: Marker {}"),
     ("qualified-result-where", "fn PathClause<T>() -> outer::Result where T: Marker {}"),
     ("where-tail-then-clause", "fn PathClause<T>() -> outer::where where T: Marker {}"),
     ("commented-path-tail", "fn PathClause<T>() -> outer:: /* tail */ where where T: Marker {}"),
     ("path-tail-identifiers", "fn PathTail(value: outer::where) -> outer::where { value }"),
     ("qualified-bound-identifiers", "fn BoundTail<T: outer::where>() where T: other::where {}"),
     ("function-keyword-name", "fn where() {}"),
     ("nested-identifiers", "fn Nested<T>(value: outer::where<T>, callback: fn(where) -> where) {}")]
  val _ = List.app (fn (label, text) => ignore (roundtrip ctxt label text)) shapes
  val projected = roundtrip ctxt "projection"
    "fn Project<'a, T: A + outer::B, const N: usize, U>(value: T) where U: C, T: D + E, T: F { value }"
  val _ = require "source generic order"
    (map (fn Generic_Lifetime (Rust_Lifetime (name, _)) => name
           | Generic_Type (name, _, _) => name | Generic_Const (name, _, _) => name)
       (#parameters (function_generics projected)) = ["'a", "T", "N", "U"])
  val _ = require "lifetime projection" (length (function_lifetime_parameters projected) = 1)
  val _ = require "type/const descriptor identity"
    (map (fn Generic_Parameter (name, _, kind) => (name, kind)) (function_type_parameters projected) =
      [("T", Type_Parameter), ("N", Const_Parameter), ("U", Type_Parameter)])
  fun bound_name (Rust_Trait_Bound (path, _)) = space_implode "::" (map #1 path)
  val _ = require "inline/where bound order"
    (map (fn (name, bounds) => (name, map bound_name bounds)) (function_bounds projected) =
      [("T", ["A", "outer::B", "D", "E", "F"]), ("U", ["C"])])
  val _ = require "authored where entries stay separate"
    (map #1 (#where_clause (function_generics projected)) = ["U", "T", "T"])
  val _ = require "empty list stays authored"
    (String.isSubstring "Empty<>" (URust_Printer.string_of_function URust_Printer.serialized_options
      (parse ctxt "empty-preservation" "fn Empty<>() {}")))
  val members =
    "fn Free<T: Copy>(value: T) -> T where T: Marker { value }\n" ^
    "impl Counter {\n" ^
    "fn Value<T>(self, value: T) -> T { value }\n" ^
    "fn Mutable<const N: usize>(mut self) -> usize { 0 }\n" ^
    "fn Shared<'a, T>(&'a self, value: T) -> T where T: Copy { value }\n" ^
    "fn Unique<T>(&mut self, value: T) -> T { value }\n" ^
    "fn Typed<T>(self: Self, value: T) -> T { value }\n}"
  val parsed_chunk = chunk ctxt "generic-members" members
  fun check_chunk options =
    let val generated = URust_Printer.string_of_chunk options parsed_chunk
        val reparsed = chunk ctxt "generic-members-reparsed" generated
    in require "generic chunk/member roundtrip"
      (URust_Printer.tokens_of_chunk options parsed_chunk = URust_Printer.tokens_of_chunk options reparsed) end
  val _ = List.app check_chunk [URust_Printer.serialized_options, URust_Printer.human_options]
  val _ = List.app (fn envelope =>
    let val generated = URust_Printer.string_of_annotated_item URust_Printer.serialized_options envelope
        val reparsed = hd (chunk_items (chunk ctxt "generic-envelope-reparsed" generated))
    in require "generic envelope roundtrip"
      (URust_Printer.tokens_of_annotated_item URust_Printer.serialized_options envelope =
       URust_Printer.tokens_of_annotated_item URust_Printer.serialized_options reparsed) end)
      (chunk_items parsed_chunk)
in val _ = () end
\<close>

section\<open> Positioned unsupported forms \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val ctxt = Context_Position.set_visible true @{context}
  val tests =
    [("lifetime-after-type", "lifetime parameters must be declared prior", "fn Bad<T, 'a>() {}", "'a", 0),
     ("lifetime-after-const", "lifetime parameters must be declared prior", "fn Bad<const N: usize, 'a>() {}", "'a", 0),
     ("type-default", "defaults on function generic parameters", "fn Bad<T = u8>() {}", "=", 0),
     ("const-default", "defaults on function generic parameters", "fn Bad<const N: usize = 3>() {}", "=", 0),
     ("default-block", "defaults on function generic parameters", "fn Bad<const N: usize = { 3 }>() {}", "=", 0),
     ("optional-inline", "optional trait bounds are not supported", "fn Bad<T: ?Sized>() {}", "?", 0),
     ("optional-where", "optional trait bounds are not supported", "fn Bad<T>() where T: ?Sized {}", "?", 0),
     ("lifetime-parameter-bound", "lifetime bounds are not supported", "fn Bad<'a: 'b>() {}", ":", 0),
     ("lifetime-parameter-plus-bounds", "lifetime bounds are not supported", "fn Bad<'a: 'b + 'c>() {}", ":", 0),
     ("lifetime-inline-bound", "lifetime bounds are not supported", "fn Bad<'a, T: 'a>() {}", "'a", 1),
     ("lifetime-inline-plus-bound", "lifetime bounds are not supported", "fn Bad<'a, T: Marker + 'a>() {}", "'a", 1),
     ("lifetime-where-bound", "lifetime bounds are not supported", "fn Bad<'a, T>() where T: 'a {}", "'a", 1),
     ("fn-inline-bound", "Fn trait bounds are not supported", "fn Bad<T: Fn(u8) -> u8>() {}", "(", 0),
     ("fn-where-bound", "Fn trait bounds are not supported", "fn Bad<T>() where T: Fn(u8) -> u8 {}", "(", 1),
     ("generic-inline-bound", "generic trait bounds are not supported", "fn Bad<T: Trait<u8>>() {}", "<", 1),
     ("generic-empty-bound", "generic trait bounds are not supported", "fn Bad<T: Trait<>>() {}", "<", 1),
     ("generic-associated-bound", "generic trait bounds are not supported", "fn Bad<T>() where T: outer::Trait<Item = u8> {}", "<", 1),
     ("const-colon-bound", "bounds on const parameters are not supported", "fn Bad<const N: usize: Trait>() {}", ":", 1),
     ("const-plus-bound", "bounds on const parameters are not supported", "fn Bad<const N: usize + Trait>() {}", "+", 0),
     ("const-u8", "urust_datatype: const parameters require usize", "fn Bad<const N: u8>() {}", "u8", 0),
     ("const-named-type", "urust_datatype: const parameters require usize", "fn Bad<const N: Length>() {}", "Length", 0),
     ("where-unknown", "where clauses may only bound this function's type parameters", "fn Bad<T>() where U: Trait {}", "U", 0),
     ("where-const", "where clauses may only bound this function's type parameters", "fn Bad<const N: usize>() where N: Trait {}", "N", 1),
     ("where-concrete", "where clauses may only bound this function's type parameters", "fn Bad<T>() where u8: Trait {}", "u8", 0),
     ("where-qualified", "where clauses may only bound this function's type parameters", "fn Bad<T>() where outer::T: Trait {}", "outer", 0),
     ("where-applied", "where clauses may only bound this function's type parameters", "fn Bad<T>() where T<u8>: Trait {}", "T", 1),
     ("where-reference", "where clauses may only bound this function's type parameters", "fn Bad<T>() where &T: Trait {}", "&", 0),
     ("legacy-parser-where", "where clauses may only bound this function's type parameters", "fn Where(value: u64) -> u64 where u64: Copy { value }", "u64", 2),
     ("legacy-command-where", "where clauses may only bound this function's type parameters", "fn WhereClause(x: u64) -> u64 where X: Y { x }", "X", 0)]
  val _ = List.app (rejects ctxt) tests
in val _ = () end
\<close>

section\<open> Declaration markup and duplicate locations \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val ctxt = Context_Position.set_visible true @{context}
  val text = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ fn Mark<'a, T: outer::Scale + Copy, const N: usize>(value: T) -> T where T: Marker { value }"
  val (function, events) = reports (fn () => parse ctxt "generic-markup" text)
  fun role name token occurrence =
    require ("missing " ^ name ^ " at " ^ token)
      (has_role events name (range_of text token occurrence))
  val _ = List.app (fn (token, occurrence) => role Markup.keyword1N token occurrence)
    [("fn", 0), ("const", 0), ("where", 0)]
  val _ = List.app (fn (token, occurrence) => role Markup.delimiterN token occurrence)
    [("<", 0), (">", 0), (",", 0), (",", 1), (":", 0), ("::", 0), ("(", 0), (")", 0), ("->", 0)]
  val _ = role Markup.operatorN "+" 0
  val _ = List.app (fn (token, occurrence) => role Markup.tfreeN token occurrence)
    [("'a", 0), ("T", 0), ("N", 0)]
  val _ = role Markup.typingN "'a" 0
  val _ = List.app (fn token =>
    require ("syntax prematurely resolved bound " ^ token)
      (not (has_role events Markup.entityN (range_of text token 0)))) ["outer", "Scale", "Copy", "Marker"]
  val generic_layout = #layout (function_generics function)
  fun token_position token expected =
    require "generic source-layout token range"
      (exists (fn pos => position_range pos = expected) (source_token_positions generic_layout token))
  val _ = token_position (Keyword_Token "const") (range_of text "const" 0)
  val _ = token_position (Keyword_Token "where") (range_of text "where" 0)
  val _ = token_position Operator_Token (range_of text "+" 0)
  val first_bound = hd (#2 (hd (function_bounds function)))
  val _ = (case first_bound of Rust_Trait_Bound ([("outer", outer), ("Scale", scale)], layout) =>
      (require "qualified bound head exact symbol range" (position_range outer = range_of text "outer" 0);
       require "qualified bound tail exact symbol range" (position_range scale = range_of text "Scale" 0);
       require "qualified bound separator exact symbol range"
         (map position_range (source_token_positions layout (Delimiter_Token "::")) = [range_of text "::" 0]))
    | _ => error "qualified bound shape changed")
  val _ = require "symbol offsets do not count bytes"
    (#1 (range_of text "T" 0) < raw_index text "T" 0 + 1)
  val _ = List.app (fn (label, item, needle, occurrence) =>
    let val diagnostic = failure label "duplicate generic parameter" (fn () => parse ctxt label item)
        val positions = map position_range (message_positions diagnostic)
    in require (label ^ ": both duplicate declaration ranges")
      (positions = [range_of item needle occurrence, range_of item needle 0]) end)
    [("duplicate-types", "fn Bad<T, T>() {}", "T", 1),
     ("duplicate-consts", "fn Bad<const N: usize, const N: usize>() {}", "N", 1),
     ("duplicate-type-const", "fn Bad<T, const T: usize>() {}", "T", 1),
     ("duplicate-const-type", "fn Bad<const T: usize, T>() {}", "T", 1)]
in val _ = () end
\<close>

section\<open> Temporary guards and delivered compatibility \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val thy = @{theory}
  val hol_type = "nat => ('s, nat, 'abort, 'i, 'o) function_body"
  fun declaration declared item =
    "urust_fn [pp_test, verbosity = 0] generic_syntax_failure " ^
    (if declared then ":: " ^ cartouche hol_type ^ " " else "") ^ cartouche item
  fun guard (label, declared, item, token) =
    let
      val text = declaration declared item
      val (message, events) = reports (fn () => failure label
        "urust_fn: type generics are not supported" (fn () => run thy label text))
      val positions = map position_range (message_positions message)
      val _ = require (label ^ ": stub did not identify first non-lifetime parameter")
        (not (null positions) andalso hd positions = range_of text token 0)
      val _ = require (label ^ ": premature declaration markup")
        (not (exists (fn (name, _, props) => name = Markup.entityN andalso
          is_some (Properties.get props Markup.defN)) events))
      val recovered = run thy (label ^ "-recovery")
        (declaration false "fn Generic(value: u8) -> u8 { value }") |> Toplevel.context_of
      val _ = require (label ^ ": command did not recover")
        (is_some (Parser_Test_Calls.lookup recovered "Generic"))
    in () end
  val _ = List.app guard
    [("guard-inferred-type", false, "fn Generic<T>(x: T) -> T { x }", "T"),
     ("guard-declared-type", true, "fn Generic<T>(value: impl Marker) -> impl Marker { value }", "T"),
     ("guard-inferred-const", false, "fn Sized<const N: usize>(value: [u8; N]) -> usize { 0 }", "N"),
     ("guard-declared-const", true, "fn Sized<const N: usize>(value: Unknown) -> Unknown { value }", "N"),
     ("guard-inferred-mixed", false, "fn Mix<'a, const N: usize, T>(value: T) -> T { value }", "N"),
     ("guard-declared-mixed", true, "fn Mix<'a, T, const N: usize>(value: Unknown) -> Unknown { value }", "T"),
     ("legacy-reference-mixed-generics", false, "fn BadReference<'a, T>(value: &'a mut u8) -> u8 { 0 }", "T")]
  val _ = ignore (run thy "lifetime-only-command"
    (declaration false "fn Borrow<'a>(value: &'a mut u8) -> &'a mut u8 { value }"))
  val _ = List.app (fn (label, expected, item) => ignore (failure label expected
    (fn () => run thy label (declaration false item))))
    [("lifetime-undeclared", "undeclared lifetime", "fn Borrow(value: &'a mut u8) -> u8 { 0 }"),
     ("lifetime-duplicate", "duplicate lifetime parameter", "fn Borrow<'a, 'a>(value: &'a mut u8) -> u8 { 0 }"),
     ("lifetime-static", "cannot be declared as a lifetime parameter", "fn Borrow<'static>(value: u8) -> u8 { 0 }"),
     ("lifetime-anonymous", "cannot be declared as a lifetime parameter", "fn Borrow<'_>(value: u8) -> u8 { 0 }"),
     ("inferred-impl-trait", "Rust impl Trait types", "fn Retained(value: impl Marker) -> u8 { 0 }")]
  val retained = run thy "declared-literal-types"
    (declaration true "fn Retained(value: impl Marker) -> impl Marker { value }") |> Toplevel.context_of
  val _ = require "declared HOL type retained impl Trait bypass"
    (is_some (Parser_Test_Calls.lookup retained "Retained"))
  val model = run thy "generic-member-model"
    ("urust_datatype [verbosity = 0] " ^ cartouche "struct SyntaxCounter { value: u8 }")
    |> Toplevel.theory_of
  val chunks =
    [("chunk-generic-function", "fn Generic<T>(value: T) -> T { value }", "T"),
     ("impl-generic-value", "impl SyntaxCounter { fn Value<T>(self, value: T) -> T { value } }", "T"),
     ("impl-generic-mutable", "impl SyntaxCounter { fn Value<T>(mut self, value: T) -> T { value } }", "T"),
     ("impl-generic-shared", "impl SyntaxCounter { fn Value<'a, T>(&'a self, value: T) -> T { value } }", "T"),
     ("impl-generic-unique", "impl SyntaxCounter { fn Value<const N: usize>(&mut self) -> usize { 0 } }", "N"),
     ("impl-generic-typed", "impl SyntaxCounter { fn Value<T>(self: Self, value: T) -> T { value } }", "T")]
  val _ = List.app (fn (label, item, token) =>
    let val text = "urust [pp_test, verbosity = 0] " ^ cartouche item
        val diagnostic = failure label "urust_fn: type generics are not supported"
          (fn () => run model label text)
    in require (label ^ ": chunk/member stub range")
      (hd (map position_range (message_positions diagnostic)) = range_of text token 0) end) chunks
  val ctxt = Proof_Context.init_global thy
  fun datatype_of text = the (URust_Parser.parse_datatype_source ctxt (source "datatype-generic-control" text))
  fun alias_of text = the (URust_Parser.parse_type_alias_source ctxt (source "alias-generic-control" text))
  val datatype_item = datatype_of "struct Cell<T, const N: usize> { value: T, bytes: [u8; N] }"
  val alias_item = alias_of "type CellAlias<T, const N: usize> = Cell<T, N>;"
  val _ = (case datatype_item of Datatype_Header (parameters, _, _, _) =>
    require "datatype descriptor identity"
      (map (fn Generic_Parameter (name, _, kind) => (name, kind)) parameters =
        [("T", Type_Parameter), ("N", Const_Parameter)]) | _ => error "datatype header changed")
  val _ = require "alias descriptor identity"
    (map (fn Generic_Parameter (name, _, kind) => (name, kind)) (type_alias_parameter_descriptors alias_item) =
      [("T", Type_Parameter), ("N", Const_Parameter)])
  val _ = List.app (fn options =>
    (require "datatype generic printer compatibility"
      (URust_Printer.tokens_of_datatype options datatype_item =
       URust_Printer.tokens_of_datatype options (datatype_of (URust_Printer.string_of_datatype options datatype_item)));
     require "alias generic printer compatibility"
      (URust_Printer.tokens_of_type_alias options alias_item =
       URust_Printer.tokens_of_type_alias options (alias_of (URust_Printer.string_of_type_alias options alias_item)))))
    [URust_Printer.serialized_options, URust_Printer.human_options]
  val _ = ignore (failure "datatype-bounds-control" "syntax error"
    (fn () => datatype_of "struct Cell<T: Copy> { value: T }"))
  val _ = ignore (failure "datatype-optional-bound-control" "unexpected input \"?\""
    (fn () => datatype_of "struct Cell<T: ?Sized> { value: T }"))
  val _ = ignore (failure "alias-optional-bound-control" "unexpected input \"?\""
    (fn () => alias_of "type CellAlias<T: ?Sized> = T;"))
  val _ = ignore (failure "impl-plus-target-control" "unexpected input \"+\""
    (fn () => chunk ctxt "impl-plus-target-control" "impl SyntaxCounter + Marker {}"))
  val _ = List.app (fn (label, token, text) => ignore (failure label
    ("unexpected input " ^ quote token) (fn () => parse ctxt label text)))
    [("retained-numeric-argument-plus", "+", "fn Numeric(value: Cell<u8, 4+4>) {}"),
     ("retained-optional-type", "?", "fn Optional(value: ?Sized) {}")]
  val _ = ignore (failure "extracted-numeric-argument-plus" "unexpected input \"+\""
    (fn () => URust_Parser.parse_generic_argument_source ctxt
      (source "extracted-numeric-argument-plus" "4+4")))
in val _ = () end
\<close>

chapter\<open> Signatures \<close>

text\<open> Reserved for U3 generic signature audits. \<close>

chapter\<open> Bodies \<close>

text\<open> Reserved for U4 generic body audits. \<close>

chapter\<open> Turbofish \<close>

text\<open> Reserved for U4 generic call audits. \<close>

end
