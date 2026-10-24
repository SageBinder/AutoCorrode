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
  val (function, captured) =
    Parser_Test_Reports.chunks (fn () => parse ctxt "generic-markup" text)
  val trees = maps YXML.parse_body captured
  val events = map (fn (name, props) =>
    (name, position_range (Position.of_properties props), props))
    (fold Parser_Test_Reports.collect_markup trees [])
  fun typing_texts range (XML.Elem ((name, props), body)) =
        (if name = Markup.typingN andalso position_range (Position.of_properties props) = range
         then [XML.content_of body] else []) @ maps (typing_texts range) body
    | typing_texts _ (XML.Text _) = []
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
  val _ = List.app (fn (token, occurrence) => role Markup.typingN token occurrence)
    [("'a", 0), ("T", 0), ("N", 0)]
  val _ = List.app (fn (token, descriptor) =>
    require ("missing native parameter tooltip at " ^ token)
      (member (op =) (maps (typing_texts (range_of text token 0)) trees) descriptor))
    [("T", "type parameter T"), ("N", "const parameter N")]
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

section\<open> Native result channels and callback restoration \<close>

text\<open>
Native datatype generation keeps its synchronous ordinary and urgent results quiet. These
unfiltered captures preserve every callback's channel and chunks, check exact predecessor
identities, and exercise nested scopes, independent physical threads, child joins and interrupts.
Semantic channels remain audible, including native aliases to ordinary output.
\<close>

ML\<open>
(* Direct native result channel probes against the canonical A20 owner. *)
structure Generic_Syntax_Native_Output =
struct
  val require = Generic_Syntax_Test.require

  val owned =
    [("writeln", Private_Output.writeln_fn),
     ("urgent", Private_Output.writeln_urgent_fn),
     ("state", Private_Output.state_fn),
     ("tracing", Private_Output.tracing_fn),
     ("system", Private_Output.system_message_fn)]

  val simple_channels = owned @
    [("information", Private_Output.information_fn),
     ("warning", Private_Output.warning_fn),
     ("legacy", Private_Output.legacy_fn),
     ("status", Private_Output.status_fn),
     ("report", Private_Output.report_fn)]

  fun with_callbacks settings action =
    fold_rev (fn (reference, callback) => fn body => fn () =>
      Unsynchronized.setmp reference callback body ()) settings action ()

  fun saved_callbacks () = map (fn (_, reference) => !reference) owned
  fun same_callbacks saved =
    forall (fn (callback, (_, reference)) => PolyML.pointerEq (callback, !reference))
      (saved ~~ owned)

  (* Complete result/report chunks are retained without source/thread/message filtering.
     Native lifecycle callbacks stay installed during source-generation matrices. *)
  fun capture_with semantic_probe action =
    let
      val events = Synchronized.var "generic syntax native output" ([]: (string * string list) list)
      fun collect channel chunks = Synchronized.change events (fn prior => prior @ [(channel, chunks)])
      val probe: unit Thread_Data.var = Thread_Data.var ()
      fun owns_probe () = is_some (Thread_Data.get probe)
      val captured_channels = ["writeln", "urgent", "report"]
      val channels = if semantic_probe then simple_channels
        else filter (fn (channel, _) => member (op =) captured_channels channel) simple_channels
      fun callback channel original chunks =
        if member (op =) captured_channels channel orelse owns_probe ()
        then collect channel chunks else original chunks
      val settings = map (fn (channel, reference) =>
        (reference, callback channel (!reference))) channels
      val original_error = !Private_Output.error_message_fn
      val original_result = !Private_Output.result_fn
      val original_protocol = !Private_Output.protocol_message_fn
      fun body () = Print_Mode.with_modes [Print_Mode.PIDE] (fn () => Exn.capture action ()) ()
      (* Only the explicit synchronous semantic probe uses these collectors. Unmarked native
         threads retain exact status/protocol properties, bodies and chunks. *)
      fun semantic_body () =
        Thread_Data.setmp probe (SOME ()) (fn () =>
          Unsynchronized.setmp Private_Output.error_message_fn
            (fn (serial, chunks) =>
              if owns_probe () then collect "error" chunks else original_error (serial, chunks))
            (fn () =>
              Unsynchronized.setmp Private_Output.result_fn
                (fn props => fn chunks =>
                  if owns_probe () then collect "result" chunks else original_result props chunks)
                (fn () =>
                  Unsynchronized.setmp Private_Output.protocol_message_fn
                    (fn props => fn bodies =>
                      if owns_probe () then collect "protocol" (map YXML.string_of_body bodies)
                      else original_protocol props bodies) body ()) ()) ()) ()
      val result = Parser_Test_Report_Lock.run (fn () =>
        with_callbacks settings (if semantic_probe then semantic_body else body))
    in (result, Synchronized.value events) end

  fun capture action = capture_with false action
  fun capture_semantics action = capture_with true action

  fun chunks channel events = maps #2 (filter (fn (name, _) => name = channel) events)
  fun ordinary events = chunks "writeln" events @ chunks "urgent" events
  fun trees channel events = maps YXML.parse_body (chunks channel events)

  (* Physical native threads make overlap independent of the configured future worker count. *)
  fun fork label action =
    let
      val result = Single_Assignment.var label
      val thread = Isabelle_Thread.fork (Isabelle_Thread.params label)
        (fn () => Single_Assignment.assign result (Exn.capture action ()))
    in fn () => (Isabelle_Thread.join thread; Exn.release (Single_Assignment.await result)) end

  val quiet = URust_Report_Transaction.quiet_native_results
end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Native_Output
  exception Scope_Failure
  fun hidden label =
    (Output.writelns [label, "-ordinary"]; Output.writelns_urgent [label, "-urgent"])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val attributes = Thread_Attributes.convert_attributes (Thread_Attributes.get_attributes ())
      val normal = quiet (fn () =>
        (require "native result action retains original interrupt attributes"
           (Thread_Attributes.convert_attributes (Thread_Attributes.get_attributes ()) = attributes);
         hidden "normal"; 37))
      val _ = require "normal native result value and callback identities"
        (normal = 37 andalso same_callbacks callbacks)
      val failure = Exn.capture (fn () => quiet (fn () => (hidden "failure"; raise Scope_Failure))) ()
      val _ = require "native result exception and callback identities"
        ((case failure of Exn.Exn Scope_Failure => true | _ => false) andalso same_callbacks callbacks)
      val interrupt = Exn.capture (fn () =>
        quiet (fn () => (hidden "interrupt"; Isabelle_Thread.raise_interrupt ()))) ()
      val _ = require "native result interrupt and callback identities"
        ((case interrupt of Exn.Exn exn => Exn.is_interrupt exn | _ => false) andalso
          same_callbacks callbacks)
      val _ = quiet (fn () =>
        let
          val callbacks = saved_callbacks ()
          val nested = Exn.capture (fn () =>
            quiet (fn () => (hidden "nested-failure"; raise Scope_Failure))) ()
          val _ = require "same-thread nested failure retains outer callback installation"
            ((case nested of Exn.Exn Scope_Failure => true | _ => false) andalso
              same_callbacks callbacks)
        in hidden "outer-after-nested-failure" end)
      val _ = require "nested failure restores exact enclosing callbacks" (same_callbacks callbacks)
      val _ = Output.writelns ["after", "normal-exception-interrupt"]
      val _ = Output.writelns_urgent ["after", "urgent"]
    in () end)
  val _ = Exn.release result
  val _ = require "native result scope suppresses only owned ordinary and urgent chunks"
    (events = [("writeln", ["after", "normal-exception-interrupt"]),
      ("urgent", ["after", "urgent"])])

  val foreign_probe: unit Thread_Data.var = Thread_Data.var ()
  val foreign_status = Synchronized.var "foreign native status chunks" ([]: string list)
  val foreign_protocol =
    Synchronized.var "foreign native protocol payload" (NONE: (Properties.T * XML.body list) option)
  val status_callback = !Private_Output.status_fn
  val protocol_callback = !Private_Output.protocol_message_fn
  val foreign_properties = [("function", "foreign-output-probe"), ("probe", "native")]
  val foreign_bodies = [[XML.Text "foreign-protocol"]]
  (* The controlled predecessor consumes only the explicitly tagged worker's synthetic payload.
     All real lifecycle traffic keeps its original native sink. *)
  val (result, events) = Native_Output_Ownership.with_temporary_hooks (fn () =>
    Unsynchronized.setmp Private_Output.status_fn
      (fn chunks => if is_some (Thread_Data.get foreign_probe)
        then Synchronized.change foreign_status (fn _ => chunks) else status_callback chunks)
      (fn () =>
        Unsynchronized.setmp Private_Output.protocol_message_fn
          (fn props => fn bodies => if is_some (Thread_Data.get foreign_probe)
            then Synchronized.change foreign_protocol (fn _ => SOME (props, bodies))
            else protocol_callback props bodies)
          (fn () => capture_semantics (fn () =>
            let
              val callbacks = saved_callbacks ()
              val untouched = drop 5 simple_channels
                |> map (fn (_, reference) => (!reference, reference))
              val error_callback = !Private_Output.error_message_fn
              val result_callback = !Private_Output.result_fn
              val protocol_callback = !Private_Output.protocol_message_fn
              val _ = quiet (fn () =>
                (require "other semantic channel refs are untouched"
                   (forall (fn (callback, reference) => PolyML.pointerEq (callback, !reference)) untouched
                    andalso PolyML.pointerEq (error_callback, !Private_Output.error_message_fn)
                    andalso PolyML.pointerEq (result_callback, !Private_Output.result_fn)
                    andalso PolyML.pointerEq (protocol_callback, !Private_Output.protocol_message_fn));
                 hidden "semantic-control";
                 Output.state ["state", "-chunks"];
                 Output.tracing "tracing";
                 Output.system_message "system";
                 Output.information "information";
                 Output.warning "warning";
                 Output.legacy_feature "legacy";
                 Output.error_message "error";
                 Output.status ["status", "-chunks"];
                 Output.report ["report", "-chunks"];
                 Output.result [] ["result", "-chunks"];
                 Output.protocol_message [] [[XML.Text "protocol"]]))
              val foreign = fork "foreign native lifecycle traffic" (fn () =>
                Thread_Data.setmp foreign_probe (SOME ()) (fn () =>
                  (Output.status ["foreign-status", "-chunks"];
                   Output.protocol_message foreign_properties foreign_bodies)) ())
              val _ = foreign ()
            in require "semantic channels restore exact five callbacks" (same_callbacks callbacks) end)) ()) ())
  val _ = Exn.release result
  val _ = require "semantic probe forwards unrelated native status/protocol without changing payloads"
    (Synchronized.value foreign_status = ["foreign-status", "-chunks"] andalso
      Synchronized.value foreign_protocol = SOME (foreign_properties, foreign_bodies))
  val _ = require "all semantic channels remain audible with their chunks and channels"
    (events =
      [("state", ["state", "-chunks"]), ("tracing", ["tracing"]), ("system", ["system"]),
       ("information", ["information"]), ("warning", ["warning"]),
       ("legacy", ["Legacy feature! legacy"]), ("error", ["error"]),
       ("status", ["status", "-chunks"]), ("report", ["report", "-chunks"]),
       ("result", ["result", "-chunks"]), ("protocol", ["protocol"])])

  val (result, events) = capture (fn () =>
    with_callbacks
      [(Private_Output.writeln_urgent_fn, fn chunks => !Private_Output.writeln_fn chunks),
       (Private_Output.state_fn, fn chunks => !Private_Output.writeln_fn chunks),
       (Private_Output.tracing_fn, fn chunks => !Private_Output.writeln_fn chunks),
       (Private_Output.system_message_fn, fn chunks => !Private_Output.writeln_fn chunks)]
      (fn () =>
        let
          val callbacks = saved_callbacks ()
          val _ = quiet (fn () =>
            (hidden "standalone-alias-hidden";
             Output.state ["alias-state", "-chunks"];
             Output.tracing "alias-tracing";
             Output.system_message "alias-system";
             hidden "after-alias-hidden"))
          val _ = require "standalone aliases restore exact callback objects" (same_callbacks callbacks)
        in Output.writelns_urgent ["outside", "-urgent-alias"] end))
  val _ = Exn.release result
  val _ = require "standalone semantic aliases clear only the physical quiet marker"
    (events = [("writeln", ["alias-state", "-chunks"]),
      ("writeln", ["alias-tracing"]), ("writeln", ["alias-system"]),
      ("writeln", ["outside", "-urgent-alias"])])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val ready_a = Single_Assignment.var "quiet owner A entered"
      val ready_b = Single_Assignment.var "quiet owner B entered"
      val release_a = Single_Assignment.var "quiet owner A leave"
      val release_b = Single_Assignment.var "quiet owner B leave"
      fun owner label ready release = fork label (fn () => quiet (fn () =>
        (hidden (label ^ "-first"); Single_Assignment.assign ready ();
         Single_Assignment.await release; hidden (label ^ "-last"))))
      val join_a = owner "scope-A" ready_a release_a
      val _ = Single_Assignment.await ready_a
      val installed = saved_callbacks ()
      val join_b = owner "scope-B" ready_b release_b
      val _ = Single_Assignment.await ready_b
      val overlap_reuses_installation = same_callbacks installed
      val unrelated = fork "unrelated physical output" (fn () =>
        (Output.writelns ["foreign", "-ordinary"];
         Output.writelns_urgent ["foreign", "-urgent"]))
      val _ = unrelated ()
      val future = Future.fork (fn () =>
        (Output.writelns ["future", "-ordinary"]; Output.writelns_urgent ["future", "-urgent"]))
      val _ = Future.join future
      val _ = Single_Assignment.assign release_a ()
      val _ = join_a ()
      val first_leave_retains_installation = same_callbacks installed
      val _ = Output.writelns ["between", "-owners"]
      val _ = Single_Assignment.assign release_b ()
      val _ = join_b ()
      val _ = require "overlapping physical owners share and retain one installation"
        (overlap_reuses_installation andalso first_leave_retains_installation)
      val _ = require "last physical owner restores exact callbacks" (same_callbacks callbacks)
    in Output.writelns_urgent ["after", "-owners"] end)
  val _ = Exn.release result
  val _ = require "unrelated threads and futures preserve ordinary/urgent channel chunks"
    (events = [("writeln", ["foreign", "-ordinary"]), ("urgent", ["foreign", "-urgent"]),
      ("writeln", ["future", "-ordinary"]), ("urgent", ["future", "-urgent"]),
      ("writeln", ["between", "-owners"]), ("urgent", ["after", "-owners"])])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val _ = quiet (fn () =>
        let
          val installed = saved_callbacks ()
          val child = fork "explicit child quiet scope" (fn () =>
            quiet (fn () => hidden "child-helper"))
          val _ = child ()
          val _ = require "parent join retains its installation" (same_callbacks installed)
        in hidden "parent-after-child-join" end)
    in require "parent child join restores callbacks without an action lock"
      (same_callbacks callbacks) end)
  val _ = Exn.release result
  val _ = require "explicit child helpers suppress their own synchronous results" (null events)

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val entered = Single_Assignment.var "interruptible quiet scope entered"
      val blocked = Single_Assignment.var "interruptible quiet scope blocker"
      val finished = Single_Assignment.var "interruptible quiet scope result"
      val thread = Isabelle_Thread.fork
        (Isabelle_Thread.interrupts (Isabelle_Thread.params "interruptible native result scope"))
        (fn () => Single_Assignment.assign finished
          (Exn.capture (fn () => quiet (fn () =>
            (hidden "actual-interrupt"; Single_Assignment.assign entered ();
             Single_Assignment.await blocked))) ()))
      val _ = Single_Assignment.await entered
      val _ = Isabelle_Thread.interrupt_thread thread
      val _ = Isabelle_Thread.join thread
      val interrupted = Single_Assignment.await finished
      val _ = require "native interrupt leaves scope before propagating the original interrupt"
        ((case interrupted of Exn.Exn exn => Exn.is_interrupt exn | _ => false) andalso
          same_callbacks callbacks)
    in Output.writelns ["after", "-actual-interrupt"] end)
  val _ = Exn.release result
  val _ = require "interrupt cleanup restores a live enclosing collector"
    (events = [("writeln", ["after", "-actual-interrupt"])])
in val _ = () end
\<close>

section\<open> Native hook publication \<close>

text\<open>
The canonical neutral owner coordinates temporary result and printer-report callbacks with
permanent tool publication. Native barriers exercise draining, admission and interruption;
publication from its own temporary scope and recursive publication reject before mutation.
\<close>

ML_val\<open>
local
  open Generic_Syntax_Test Generic_Syntax_Native_Output
  exception Publication_Failure
  val temporary = Native_Output_Ownership.with_temporary_hooks
  val publish = Native_Output_Ownership.publish_hooks

  val _ = require "Parser_Utils uses the canonical imported native result operation"
    (PolyML.pointerEq (URust_Report_Transaction.quiet_native_results,
      Native_Output_Ownership.quiet_results))

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val normal = publish (fn () =>
        (require "publication callback masks interrupts for its complete update"
          (Thread_Attributes.convert_attributes (Thread_Attributes.get_attributes ()) =
            Thread_Attributes.convert_attributes Thread_Attributes.no_interrupts);
         43))
      val _ = require "publication preserves its original result" (normal = 43)
      val failed = Exn.capture (fn () => publish (fn () => raise Publication_Failure)) ()
      val _ = require "publication preserves its original exception"
        (case failed of Exn.Exn Publication_Failure => true | _ => false)
      val _ = temporary (fn () => quiet (fn () => Output.writeln "quiet after publication failure"))
      val mutated = Unsynchronized.ref false
      val _ = temporary (fn () =>
        ignore (failure "same-thread publication" "publication inside temporary hooks" (fn () =>
          publish (fn () => mutated := true))))
      val _ = publish (fn () =>
        (ignore (failure "recursive publication" "recursive publication" (fn () =>
           publish (fn () => mutated := true)));
         ignore (failure "temporary scope in publication" "temporary hooks inside publication" (fn () =>
           temporary (fn () => mutated := true)))))
      val _ = require "reentrant publication rejects before callback mutation"
        (not (!mutated) andalso same_callbacks callbacks)
      val _ = temporary (fn () => temporary (fn () => ()))
    in Output.writelns ["after", "-publication-failure-and-rejections"] end)
  val _ = Exn.release result
  val _ = require "publication failure and rejected recursion leave live predecessor routing"
    (events = [("writeln", ["after", "-publication-failure-and-rejections"])])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val report_callback = !Private_Output.report_fn
      val publication_count = Synchronized.var "publication executes once" 0
      val forwarded = Synchronized.var "published callback forwarding" 0
      val ready_quiet = Single_Assignment.var "publication quiet scope entered"
      val child_go = Single_Assignment.var "pending publisher child go"
      val child_done = Single_Assignment.var "pending publisher child done"
      val quiet_release = Single_Assignment.var "publication quiet scope release"
      val ready_report = Single_Assignment.var "publication report capture entered"
      val report_release = Single_Assignment.var "publication report capture release"
      val attempted = Single_Assignment.var "publication attempt"
      val published = Single_Assignment.var "publication complete"
      val installed = Single_Assignment.var "published callback objects"
      val quiet_join = fork "publication held quiet scope" (fn () => quiet (fn () =>
        (Output.writeln "held quiet output";
         Single_Assignment.assign ready_quiet ();
         Single_Assignment.await child_go;
         let
           val child = fork "quiet child while publication waits" (fn () =>
             quiet (fn () => Output.writeln_urgent "held child output"))
         in child () end;
         Single_Assignment.assign child_done ();
         Single_Assignment.await quiet_release)))
      val _ = Single_Assignment.await ready_quiet
      val function = parse (Context_Position.set_visible true @{context})
        "publication-report-function" "fn Plain() {}"
      val report_join = fork "publication held native printer capture" (fn () =>
        Print_Mode.with_modes [Print_Mode.PIDE] (fn () =>
          ignore (URust_Printer_Output.pretty_human_function_with_reparse
            (fn source =>
              (Single_Assignment.assign ready_report ();
               Single_Assignment.await report_release;
               ignore (URust_Parser.parse_function_source
                 (Context_Position.set_visible true @{context}) source)))
            function)) ())
      val _ = Single_Assignment.await ready_report
      fun wrap callback chunks =
        (Synchronized.change forwarded (fn count => count + 1); callback chunks)
      val publication_join = fork "publication waits for both hook scopes" (fn () =>
        (Single_Assignment.assign attempted ();
         publish (fn () =>
           let
             val _ = require "publication captures restored ordinary/semantic and report sinks"
               (same_callbacks callbacks andalso
                PolyML.pointerEq (!Private_Output.report_fn, report_callback))
             val replacements = map wrap callbacks
             val replacement_report = wrap report_callback
             val _ = List.app (fn (callback, (_, reference)) => reference := callback)
               (replacements ~~ owned)
             val _ = Private_Output.report_fn := replacement_report
             val _ = Synchronized.change publication_count (fn count => count + 1)
             val _ = Single_Assignment.assign installed (replacements, replacement_report)
           in () end);
         Single_Assignment.assign published ()))
      val _ = Single_Assignment.await attempted
      (* Necessary child admission remains open while a publisher drains its parent. *)
      val _ = Single_Assignment.assign child_go ()
      val _ = Single_Assignment.await child_done
      val waited_for_both = is_none (Single_Assignment.peek published)
      val _ = Single_Assignment.assign quiet_release ()
      val _ = quiet_join ()
      val waited_for_report = is_none (Single_Assignment.peek published)
      val _ = Single_Assignment.assign report_release ()
      val _ = report_join ()
      val _ = publication_join ()
      val (replacement_callbacks, replacement_report) = Single_Assignment.await installed
      val stable = same_callbacks replacement_callbacks andalso
        PolyML.pointerEq (!Private_Output.report_fn, replacement_report)
      val _ = quiet (fn () => Output.writeln "quiet after completed publication")
      val stable_after_quiet = same_callbacks replacement_callbacks
      val _ = Output.writelns ["published", "-ordinary"]
      val _ = Output.writelns_urgent ["published", "-urgent"]
      val _ = Output.report [YXML.string_of_body [XML.Text "published-report"]]
      (* Restore the enclosing fixture before propagating any assertion failure. *)
      val _ = publish (fn () =>
        (List.app (fn (callback, (_, reference)) => reference := callback) (callbacks ~~ owned);
         Private_Output.report_fn := report_callback))
      val _ = require "publication waits for both result and actual printer-report scopes"
        (waited_for_both andalso waited_for_report)
      val _ = require "publication resumes once without later temporary restoration clobbering it"
        (Synchronized.value publication_count = 1 andalso stable andalso stable_after_quiet)
      val _ = require "published callbacks preserve forwarding after native quieting"
        (Synchronized.value forwarded = 3)
      val _ = require "publication fixture restores exact original callbacks"
        (same_callbacks callbacks andalso PolyML.pointerEq (!Private_Output.report_fn, report_callback))
    in () end)
  val _ = Exn.release result
  val _ = require "published ordinary and urgent chunks remain exact"
    (chunks "writeln" events = ["published", "-ordinary"] andalso
      chunks "urgent" events = ["published", "-urgent"])
  val _ = require "published reports remain audible" (member (op =) (chunks "report" events) "published-report")

  val (result, events) = capture (fn () =>
    let
      val entered = Single_Assignment.var "exclusive publication entered"
      val release = Single_Assignment.var "exclusive publication release"
      val attempted = Single_Assignment.var "temporary entry during publication"
      val complete = Single_Assignment.var "exclusive publication complete"
      val publication_join = fork "publication excludes temporary admission" (fn () =>
        publish (fn () =>
          (Single_Assignment.assign entered (); Single_Assignment.await release;
           Single_Assignment.assign complete ())))
      val _ = Single_Assignment.await entered
      val temporary_join = fork "temporary scope waits for publication" (fn () =>
        (Single_Assignment.assign attempted ();
         temporary (fn () =>
           require "temporary entry begins after complete publication"
             (is_some (Single_Assignment.peek complete)))))
      val _ = Single_Assignment.await attempted
      val _ = Single_Assignment.assign release ()
      val _ = publication_join ()
      val _ = temporary_join ()
    in () end)
  val _ = Exn.release result
  val _ = require "publication admission probe emits no channel payload" (null events)

  val (result, events) = capture (fn () =>
    let
      val ready = Single_Assignment.var "interrupt publication quiet scope entered"
      val release = Single_Assignment.var "interrupt publication quiet scope release"
      val attempted = Single_Assignment.var "interruptible publication attempted"
      val complete = Single_Assignment.var "interruptible publication result"
      val mutated = Unsynchronized.ref false
      val quiet_join = fork "interrupt publication held quiet scope" (fn () =>
        quiet (fn () => (Single_Assignment.assign ready (); Single_Assignment.await release)))
      val _ = Single_Assignment.await ready
      val thread = Isabelle_Thread.fork
        (Isabelle_Thread.interrupts (Isabelle_Thread.params "interruptible publication wait"))
        (fn () => Single_Assignment.assign complete
          (Exn.capture (fn () =>
            (Single_Assignment.assign attempted (); publish (fn () => mutated := true))) ()))
      val _ = Single_Assignment.await attempted
      val _ = Isabelle_Thread.interrupt_thread thread
      val _ = Isabelle_Thread.join thread
      val interrupted = Single_Assignment.await complete
      val _ = Single_Assignment.assign release ()
      val _ = quiet_join ()
      val _ = require "publication wait is interruptible and captures no temporary callback"
        ((case interrupted of Exn.Exn exn => Exn.is_interrupt exn | _ => false) andalso not (!mutated))
      val _ = publish (fn () => ())
      val _ = temporary (fn () => ())
    in () end)
  val _ = Exn.release result
  val _ = require "interrupted publication wait leaves no channel mutation" (null events)
in val _ = () end
\<close>

section\<open> Complete datatype output atomicity \<close>

text\<open>
Successful structs and native HOL enums retain authored verbosity, definition reports and
all generated class artifacts. Failed chunks release no earlier successful declaration reports
or ordinary or urgent output. A failed member may report only its own exact binder declarations.
Configuration tests distinguish absent entries from explicit values through both merge orders,
and nested targets retain each original setting. Generic guards remain temporary until U3;
the malformed nongeneric body supplies an independent durable failure and recovery control.
\<close>

ML\<open>
structure Generic_Syntax_Output_Atomicity =
struct
  open Generic_Syntax_Test Generic_Syntax_Native_Output

  fun run_with interactive thy label text =
    fold (Toplevel.command_exception interactive)
      (Outer_Syntax.parse_text thy (K thy) (start label) text) (Toplevel.make_state (SOME thy))

  fun continue interactive state label text =
    let val thy = Toplevel.theory_of state in
      fold (Toplevel.command_exception interactive)
        (Outer_Syntax.parse_text thy (K thy) (start label) text) state
    end

  fun snapshot ctxt =
    (Parser_Test_Calls.dump ctxt |> map (fn (name, entry) =>
        (name, #hol_term entry, Position.properties_of (#reg_pos entry))),
     URust_Item_Scope.dump_types ctxt |> map (fn entry =>
        (URust_Item_Scope.type_rust_name entry, URust_Item_Scope.type_hol_name entry,
         Position.properties_of (URust_Item_Scope.type_position entry))),
     URust_Item_Scope.dump_constructors ctxt |> map (fn entry =>
        (URust_Item_Scope.constructor_rust_path entry, URust_Item_Scope.constructor_term entry,
         URust_Item_Scope.constructor_fields entry,
         Position.properties_of (URust_Item_Scope.constructor_position entry))),
     Micro_Rust_Names.Declaration_Owners.get (Context.Proof ctxt) |> Symtab.dest
       |> map (fn (name, owners) => (name, map (fn ({kind, pos}: Micro_Rust_Names.declaration_owner) =>
           (kind, Position.properties_of pos)) owners)),
     Micro_Rust_Names.dump ctxt |> map (fn (kind, name, entry) =>
       (kind, name, #hol_term entry, #source_const entry, #serial entry,
        Position.properties_of (#reg_pos entry))),
     URust_Type_Mappings.dump ctxt |> map (fn (name, entry) =>
       (name, URust_Type_Mappings.entry_template entry, URust_Type_Mappings.entry_arities entry,
        URust_Type_Mappings.entry_parameter_sorts entry, URust_Type_Mappings.entry_identity entry)),
     #constants (Consts.dest (Proof_Context.consts_of ctxt)))

  fun definition_reports events =
    fold Parser_Test_Reports.collect_markup (trees "report" events) []
    |> filter (fn (name, props) => name = Markup.entityN andalso
        is_some (Properties.get props Markup.defN))
  fun declaration_reports events =
    definition_reports events
    |> filter (fn (_, props) => Properties.get props Markup.kindN <> SOME "urust_var")
  fun binder_reports events =
    definition_reports events
    |> filter (fn (_, props) => Properties.get props Markup.kindN = SOME "urust_var")
  fun callback_count channel events = length (filter (fn (name, _) => name = channel) events)
  fun exact_binders label text expected events =
    let
      val actual = binder_reports events |> map (fn (_, props) =>
        (the_default "" (Properties.get props Markup.kindN),
         the_default "" (Properties.get props Markup.nameN),
         the_default "" (Position.file_of (Position.of_properties props)),
         position_range (Position.of_properties props)))
        |> sort (string_ord o apply2 #2)
      val wanted = map (fn (name, occurrence) =>
        ("urust_var", name, label, range_of text name occurrence)) expected
        |> sort (string_ord o apply2 #2)
    in require (label ^ ": exact failed-member binder kind/name/file/source range changed")
      (actual = wanted) end

  fun command verbosity body =
    "urust [verbosity = " ^ string_of_int verbosity ^ "] " ^ cartouche ("\n" ^ body ^ "\n")

  val holder = "struct SyntaxOutputHolder { value: u8 }"
  val choice = "\<omega>" ^ cartouche "backend = \"hol\"" ^
    "\nenum SyntaxOutputChoice { Empty, Byte(u8) }"
  val member = "impl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { value } }"

  fun setting NONE thy = thy
    | setting (SOME value) thy = Config.put_global Proof_Display.show_results value thy
  fun setting_name NONE = "absent"
    | setting_name (SOME true) = "true"
    | setting_name (SOME false) = "false"

  fun native_artifacts ctxt rust_name =
    let
      val entry = the (URust_Type_Mappings.lookup ctxt rust_name)
      val T = URust_Type_Mappings.entry_template entry
      val thy = Proof_Context.theory_of ctxt
    in
      require (rust_name ^ ": native class artifacts were retained")
        (Sign.of_sort thy (T, @{sort typerep}) andalso
         Sign.of_sort thy (T, @{sort term_of}) andalso
         Sign.of_sort thy (T, @{sort equal}) andalso
         Sign.of_sort thy (T, @{sort random}))
    end

  fun target_settings ctxt =
    let
      val settings = Unsynchronized.ref ([]: (int * bool) list)
      val _ = Local_Theory.map_contexts (fn depth => fn context =>
        (settings := (depth, Config.get context Proof_Display.show_results) :: !settings; context)) ctxt
    in sort (int_ord o apply2 #1) (!settings) end
end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val thy = @{theory}
  fun success (setting_value, interactive, verbosity, rust_name, body) =
    let
      val configured = setting setting_value thy
      val label = "native-success-" ^ rust_name ^ "-" ^ string_of_int verbosity ^ "-" ^
        Bool.toString interactive ^ "-" ^ setting_name setting_value
      val (result, events) = capture (fn () => run_with interactive configured label
        (command verbosity body))
      val state = Exn.release result
      val ctxt = Toplevel.context_of state
      val enabled = interactive orelse Config.get_global configured Proof_Display.show_results
      val _ = require (label ^ ": authored verbosity output changed")
        ((not (null (ordinary events))) = (enabled andalso verbosity > 0))
      val _ = require (label ^ ": native backend result output escaped")
        (callback_count "writeln" events = (if enabled andalso verbosity > 0 then 1 else 0) andalso
          null (chunks "urgent" events))
      val _ = require (label ^ ": authored definitions were not released")
        (not (null (declaration_reports events)))
      val _ = require (label ^ ": type registry lost its authored item")
        (is_some (URust_Item_Scope.lookup_type ctxt rust_name))
      val _ = native_artifacts ctxt rust_name
      val _ = require (label ^ ": native global show_results value changed")
        (Config.get_global (Toplevel.theory_of state) Proof_Display.show_results =
          Config.get_global configured Proof_Display.show_results)
    in () end
  val _ = List.app success
    (maps (fn setting_value => maps (fn interactive => maps (fn verbosity =>
      [(setting_value, interactive, verbosity, "SyntaxOutputHolder", holder),
       (setting_value, interactive, verbosity, "SyntaxOutputChoice", choice)]) [0, 1, 2])
      [false, true]) [NONE, SOME true, SOME false])
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val thy = @{theory}
  val ctxt = Proof_Context.init_global thy
  val initial_snapshot = snapshot ctxt
  val failures =
    [("member-type-guard", holder ^ "\nimpl SyntaxOutputHolder { fn member<T>(self, value: T) -> T { value } }",
       "urust_fn: type generics are not supported"),
     ("free-const-guard", holder ^ "\nfn sized<const N: usize>(value: [u8; N]) -> usize { 0 }",
       "urust_fn: type generics are not supported"),
     ("nongeneric-body", holder ^ "\nimpl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { missing_output_value } }",
       "missing_output_value")]
  fun failing (setting_value, verbosity, (kind, body, expected)) =
    let
      val configured = setting setting_value thy
      val label = "complete-atomicity-" ^ kind ^ "-" ^ string_of_int verbosity ^ "-" ^
        setting_name setting_value
      val (result, events) = capture (fn () => run_with true configured label (command verbosity body))
      val message =
        (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
         | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
      val _ = require (label ^ ": wrong diagnostic") (String.isSubstring expected message)
      val _ = require (label ^ ": earlier successful datatype output escaped") (null (ordinary events))
      val _ = require (label ^ ": earlier successful definition reports escaped")
        (null (declaration_reports events))
      val _ = exact_binders label (command verbosity body)
        (if kind = "nongeneric-body" then [("self", 0), ("value", 1)] else []) events
      val _ = require (label ^ ": original registry or theory artifacts changed")
        (snapshot (Proof_Context.init_global configured) = initial_snapshot)
      val (recovery, recovery_events) = capture (fn () =>
        run_with true configured (label ^ "-recovery") (command verbosity (holder ^ "\n" ^ member)))
      val recovered = Exn.release recovery |> Toplevel.context_of
      val _ = require (label ^ ": failure leaked artifacts or blocked a later valid declaration")
        (is_some (Parser_Test_Calls.lookup recovered "SyntaxOutputHolder::member"))
      val _ = native_artifacts recovered "SyntaxOutputHolder"
      val _ = require (label ^ ": recovery lost authored definition reports")
        (not (null (declaration_reports recovery_events)))
    in () end
  val _ = List.app failing
    (maps (fn setting_value => maps (fn verbosity =>
      map (fn failure => (setting_value, verbosity, failure)) failures) [0, 1, 2])
      [NONE, SOME true, SOME false])
  fun guard declared verbosity =
    let
      val label = "complete-output-signature-guard-" ^ Bool.toString declared ^ "-" ^ string_of_int verbosity
      val body = "fn SyntaxOutputGeneric<T>(value: T) -> T { value }"
      val text = "urust_fn [verbosity = " ^ string_of_int verbosity ^ "] syntax_output_guard " ^
        (if declared then ":: " ^ cartouche "nat => ('s, nat, 'abort, 'i, 'o) function_body" ^ " "
         else "") ^ cartouche body
      val (result, events) = capture (fn () => run_with true thy label text)
      val diagnostic =
        (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
         | Exn.Exn exn => Runtime.exn_message exn)
      val _ = require (label ^ ": wrong temporary generic diagnostic")
        (String.isSubstring "urust_fn: type generics are not supported" diagnostic)
      val _ = require (label ^ ": complete output or definition reports escaped")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = exact_binders label text [] events
      val _ = require (label ^ ": first non-lifetime declaration range changed")
        (hd (map position_range (message_positions diagnostic)) = range_of text "T" 0)
    in () end
  val _ = List.app (fn verbosity => List.app (fn declared => guard declared verbosity) [false, true])
    [0, 1, 2]
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val base = Theory.end_theory @{theory}
  fun fresh label parents = Theory.begin_theory (label, Position.none) parents
  fun finished label configure = fresh label [base] |> configure |> Theory.end_theory
  fun flag_name NONE = "Absent" | flag_name (SOME true) = "True" | flag_name (SOME false) = "False"
  fun generated flag =
    let
      val label = "SyntaxOutputConfig" ^ flag_name flag
      val parent = fresh label [base] |> setting flag
      val (result, _) = capture (fn () => run_with false parent label (command 0 holder))
    in Exn.release result |> Toplevel.theory_of |> Theory.end_theory end
  fun merge label parents = fresh label parents |> Theory.end_theory
  fun value thy = Config.get_global thy Proof_Display.show_results
  val _ = List.app (fn flag =>
    let
      val generated = generated flag
      val pristine = finished ("SyntaxOutputPristine" ^ flag_name flag) (setting flag)
      val _ = List.app (fn other =>
        let
          val suffix = flag_name flag ^ Bool.toString other
          val opposite = finished ("SyntaxOutputOpposite" ^ suffix) (setting (SOME other))
          val original_first = merge ("SyntaxOutputControlFirst" ^ suffix) [pristine, opposite]
          val generated_first = merge ("SyntaxOutputGeneratedFirst" ^ suffix) [generated, opposite]
          val original_last = merge ("SyntaxOutputControlLast" ^ suffix) [opposite, pristine]
          val generated_last = merge ("SyntaxOutputGeneratedLast" ^ suffix) [opposite, generated]
          val _ = require (suffix ^ ": generation changed first-parent configuration semantics")
            (value generated_first = value original_first)
          val _ = require (suffix ^ ": generation changed last-parent configuration semantics")
            (value generated_last = value original_last)
          val _ = if is_none flag then
            require (suffix ^ ": absence control contains a show_results entry")
              (value original_first = other andalso value original_last = other) else ()
        in () end) [true, false]
    in () end) [NONE, SOME true, SOME false]
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val thy = @{theory}
  val locale = run_with false thy "native-output-locale"
    "locale SyntaxOutputScope = fixes output_seed :: nat"
  val entered = continue false locale "native-output-nested-enter"
    "context SyntaxOutputScope begin\ndeclare [[show_results = true]]\n\
    \context begin\ndeclare [[show_results = false]]"
  val before_context = Toplevel.context_of entered
  val before_settings = target_settings before_context
  val before_global = Config.get_global (Toplevel.theory_of entered) Proof_Display.show_results
  val (success, events) = capture (fn () => continue true entered "native-output-nested-datatype"
    (command 2 holder))
  val declared = Exn.release success
  val declared_context = Toplevel.context_of declared
  val _ = require "nested datatype restores every original target show_results setting"
    (length before_settings >= 2 andalso target_settings declared_context = before_settings)
  val _ = require "nested datatype preserves global show_results"
    (Config.get_global (Toplevel.theory_of declared) Proof_Display.show_results = before_global)
  val _ = require "nested datatype keeps authored output and definition markup"
    (callback_count "writeln" events = 1 andalso null (chunks "urgent" events) andalso
      not (null (declaration_reports events)))
  val failures =
    [("member-type-guard", "impl SyntaxOutputHolder { fn member<T>(self, value: T) -> T { value } }",
       "urust_fn: type generics are not supported", []),
     ("nongeneric-body", "impl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { missing_output_value } }",
       "missing_output_value", [("self", 0), ("value", 1)])]
  val _ = List.app (fn (kind, member, expected, binders) =>
    let
      val label = "native-output-nested-failure-" ^ kind
      val text = command 2 (holder ^ "\n" ^ member)
      val (failure, failed_events) = capture (fn () => continue true entered label text)
      val _ = require (label ^ ": failure retains its diagnostic")
        (case failure of Exn.Exn exn => String.isSubstring expected (Runtime.exn_message exn)
         | _ => false)
      val _ = require (label ^ ": earlier successful output or definition markup escaped")
        (null (ordinary failed_events) andalso null (declaration_reports failed_events))
      val _ = exact_binders label text binders failed_events
      val _ = require (label ^ ": failure preserves all original target settings")
        (target_settings (Toplevel.context_of entered) = before_settings)
    in () end) failures
in val _ = () end
\<close>

chapter\<open> Signatures \<close>

text\<open> Reserved for U3 generic signature audits. \<close>

chapter\<open> Bodies \<close>

text\<open> Reserved for U4 generic body audits. \<close>

chapter\<open> Turbofish \<close>

text\<open> Reserved for U4 generic call audits. \<close>

end
